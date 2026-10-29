//! Platform hooks the verified kernel declares as `extern "C"` (the IOTLB hook is in `iommu`).

use core::arch::asm;
use core::sync::atomic::{AtomicUsize, Ordering};

use veriflat_monolith::Registers;

use crate::cpu::{self, MAX_CPUS};
use crate::interrupt;

/// Toggling CR4.PGE invalidates every TLB entry of every PCID, global ones included.
const CR4_PGE: u64 = 1 << 7;

/// `INVPCID` type 1: invalidate every non-global translation of one PCID.
const INVPCID_SINGLE_CONTEXT: u64 = 1;

/// `FLUSH_REQUESTS[target][sender]` is `pcid + 1` while `sender` waits for `target` to flush `pcid`.
/// One slot per sender needs no lock, and an NMI handler that scans every slot also serves an NMI
/// that arrived while another one was pending.
static FLUSH_REQUESTS: [[AtomicUsize; MAX_CPUS]; MAX_CPUS] = [const { [const { AtomicUsize::new(0) }; MAX_CPUS] }; MAX_CPUS];

/// `RUNNING_TO_IDLE_REQUESTS[target]` is the default `cr3` while the caller of
/// `veriflat_ipi_running_to_idle` waits for `target` to load it, else 0. Only the holder of
/// `target`'s CPU lock sends it the running-to-idle IPI, so one slot per target suffices.
static RUNNING_TO_IDLE_REQUESTS: [AtomicUsize; MAX_CPUS] = [const { AtomicUsize::new(0) }; MAX_CPUS];

pub static REMOTE_FLUSHES: AtomicUsize = AtomicUsize::new(0);
pub static NMI_FLUSHES: AtomicUsize = AtomicUsize::new(0);
pub static REMOTE_RUNNING_TO_IDLE_IPIS: AtomicUsize = AtomicUsize::new(0);
pub static WAKE_IPIS: AtomicUsize = AtomicUsize::new(0);

/// Whether this CPU implements `INVPCID` (CPUID.07H:EBX[10]).
pub fn has_invpcid() -> bool {
    core::arch::x86_64::__cpuid_count(7, 0).ebx & (1 << 10) != 0
}

fn invpcid_single_context(pcid: usize) {
    let descriptor: [u64; 2] = [pcid as u64, 0];
    unsafe {
        asm!("invpcid {ty}, xmmword ptr [{desc}]", ty = in(reg) INVPCID_SINGLE_CONTEXT, desc = in(reg) &descriptor, options(nostack, preserves_flags));
    }
}

/// Invalidates every non-global PCID on this CPU.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_local_flush_all_pcids() {
    unsafe {
        let cr4: u64;
        asm!("mov {}, cr4", out(reg) cr4, options(nomem, nostack, preserves_flags));
        asm!("mov cr4, {}", in(reg) cr4 ^ CR4_PGE, options(nostack, preserves_flags));
        asm!("mov cr4, {}", in(reg) cr4, options(nostack, preserves_flags));
    }
}

/// Invalidates `pcid` on `cpu_id` (another CPU) and returns once it is done. The target serves the
/// request in its NMI handler, which takes no locks, so the caller may hold kernel locks. A CPU that
/// never started has never loaded a user PCID.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_remote_flush_pcid(cpu_id: usize, pcid: usize) {
    if !cpu::is_started(cpu_id) {
        return;
    }
    REMOTE_FLUSHES.fetch_add(1, Ordering::Relaxed);
    let slot = &FLUSH_REQUESTS[cpu_id][cpu::get_cpu_id()];
    slot.store(pcid + 1, Ordering::Release);
    interrupt::send_nmi(cpu::apic_id(cpu_id));
    while slot.load(Ordering::Acquire) != 0 {
        core::hint::spin_loop();
    }
}

/// Makes `cpu_id` (another CPU, whose CPU lock the caller holds and marked) abandon the thread it
/// runs: it loads `default_cr3` (page aligned) with the kernel PCID 0, flushing that PCID, and sets
/// its `running_to_idle_pending` flag, so its next exit through `restore_frame` enters its idle loop
/// instead of ring 3. Returns once the target acknowledged. The request travels by the maskable
/// running-to-idle IPI, which the target takes anywhere outside a kernel step (interrupts are off
/// exactly inside one): in user mode, in a trampoline, in its idle loop, or at a `hlt`. The caller
/// holds the target's lock, so the target is not inside a step, and every path of the target that
/// would lock its own CPU sees the mark and returns at once.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_ipi_running_to_idle(cpu_id: usize, default_cr3: usize) {
    if !cpu::is_started(cpu_id) {
        return;
    }
    REMOTE_RUNNING_TO_IDLE_IPIS.fetch_add(1, Ordering::Relaxed);
    let slot = &RUNNING_TO_IDLE_REQUESTS[cpu_id];
    slot.store(default_cr3, Ordering::Release);
    interrupt::send_ipi(cpu::apic_id(cpu_id), interrupt::VECTOR_RUNNING_TO_IDLE);
    while slot.load(Ordering::Acquire) != 0 {
        core::hint::spin_loop();
    }
}

/// Running-to-idle IPI handler. Interrupts are on everywhere outside a kernel step, so `regs` is a
/// user frame or a kernel frame of a trampoline, of the idle loop, or of a `hlt`; every frame is
/// handled alike. Loads the requested default `cr3`, then sets this CPU's `running_to_idle_pending`
/// flag, so the next exit through `restore_frame` diverts to the idle loop, then acknowledges. A
/// flag that no such exit consumes is cleared by the idle loop or by the next step's release of
/// this CPU's own lock (`veriflat_clear_running_to_idle_pending`). Also sets `wake_seen`.
pub fn handle_running_to_idle_ipi(_regs: &Registers) {
    interrupt::end_of_interrupt();
    cpu::set_wake_seen();
    let me = cpu::get_cpu_id();
    let slot = &RUNNING_TO_IDLE_REQUESTS[me];
    let default_cr3 = slot.load(Ordering::Acquire);
    if default_cr3 != 0 {
        // PCID 0 in bits 11:0 and bit 63 clear: flushes PCID 0's non-global translations.
        unsafe { asm!("mov cr3, {}", in(reg) default_cr3, options(nostack, preserves_flags)) };
        cpu::set_running_to_idle_pending();
        slot.store(0, Ordering::Release);
    }
}

/// NMI handler: serves every pending flush request for this CPU. Runs with either GS base loaded
/// (see `wrap_nmi`), so it uses `cpu_id_without_gs`. Must not log or lock.
pub fn handle_nmi(_regs: &mut Registers) {
    let me = cpu::cpu_id_without_gs();
    for slot in FLUSH_REQUESTS[me].iter() {
        let request = slot.load(Ordering::Acquire);
        if request != 0 {
            invpcid_single_context(request - 1);
            NMI_FLUSHES.fetch_add(1, Ordering::Relaxed);
            slot.store(0, Ordering::Release);
        }
    }
}

/// Sends the wake-up IPI to `target`. A CPU that does not exist has nothing to wake.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_send_ipi(target: usize) {
    if cpu::is_started(target) {
        WAKE_IPIS.fetch_add(1, Ordering::Relaxed);
        interrupt::send_ipi(cpu::apic_id(target), interrupt::VECTOR_WAKE);
    }
}

/// Halts until an interrupt arrives. Called outside kernel steps, where interrupts are on, so a
/// wake-up taken after the last step read this CPU's state but before the `hlt` would be slept
/// through: the wake-up, running-to-idle, and timer handlers set `wake_seen`, the own-lock grant
/// clears it, and the check runs with interrupts off. `sti; hlt` then halts atomically (an interrupt
/// is held for one instruction after `sti`), so one arriving after the check still ends the `hlt`.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_halt_until_ipi() {
    unsafe {
        asm!("cli", options(nostack, preserves_flags));
        if cpu::wake_seen() {
            asm!("sti", options(nostack, preserves_flags));
        } else {
            asm!("sti", "hlt", options(nostack, preserves_flags));
        }
    }
}

/// Disables interrupts on this CPU. The verified kernel's own-CPU lock calls it inside the lock's
/// spinlock when it grants the lock, so a CPU runs with interrupts off exactly while it holds its
/// own CPU lock in a kernel step (model state InStep). No `nomem`: the `asm!` is a compiler barrier.
/// It also clears `wake_seen`: the step reads this CPU's state after every wake-up seen so far.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_disable_interrupts() {
    unsafe { asm!("cli", options(nostack, preserves_flags)) };
    cpu::clear_wake_seen();
}

/// Enables interrupts on this CPU. The verified kernel's own-CPU lock calls it after the release
/// that ends a kernel step; the CPU then rests in Trap, Idle, or Off, all with interrupts on. Boot
/// also calls it before a CPU first enters its idle loop (CPU 0) or its Off wait (the APs).
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_enable_interrupts() {
    unsafe { asm!("sti", options(nostack, preserves_flags)) };
}

/// Clears this CPU's `running_to_idle_pending` flag. The verified kernel calls it inside a step,
/// right before it releases this CPU's own lock. A flag still set there is stale: the killer that
/// set it held this CPU's lock, moved this CPU to idle, and released the lock before the step could
/// start, so the step's result alone decides where the CPU goes.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_clear_running_to_idle_pending() {
    cpu::clear_running_to_idle_pending();
}

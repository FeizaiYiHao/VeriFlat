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

/// `EVICT_REQUESTS[target]` is the default `cr3` while the caller of `veriflat_evict_ipi` waits
/// for `target` to load it, else 0. Only the holder of `target`'s CPU lock evicts it, so one slot
/// per target suffices.
static EVICT_REQUESTS: [AtomicUsize; MAX_CPUS] = [const { AtomicUsize::new(0) }; MAX_CPUS];

pub static REMOTE_FLUSHES: AtomicUsize = AtomicUsize::new(0);
pub static NMI_FLUSHES: AtomicUsize = AtomicUsize::new(0);
pub static REMOTE_EVICTIONS: AtomicUsize = AtomicUsize::new(0);
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
/// runs: it loads `default_cr3` (page aligned) with the kernel PCID 0, flushing that PCID, and from
/// user mode enters its idle loop. Returns once the target acknowledged. The request travels by the
/// maskable eviction IPI, so the target takes it only with interrupts enabled: in user mode or at
/// the `hlt` of its idle loop, never inside a syscall. A target inside the kernel reaches one of the
/// two because every path that would lock its own CPU sees the mark and returns at once.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_evict_ipi(cpu_id: usize, default_cr3: usize) {
    if !cpu::is_started(cpu_id) {
        return;
    }
    REMOTE_EVICTIONS.fetch_add(1, Ordering::Relaxed);
    let slot = &EVICT_REQUESTS[cpu_id];
    slot.store(default_cr3, Ordering::Release);
    interrupt::send_ipi(cpu::apic_id(cpu_id), interrupt::VECTOR_EVICT);
    while slot.load(Ordering::Acquire) != 0 {
        core::hint::spin_loop();
    }
}

/// Eviction IPI handler. Interrupts are enabled only in user mode and at the `hlt` of the idle loop,
/// so `regs` is a user frame or an idle-loop frame. Loads the requested default `cr3`; from user mode
/// it also marks this CPU evicted, so the trampoline's exit through `restore_frame` diverts to the
/// idle loop. Then acknowledges.
pub fn handle_evict_ipi(regs: &Registers) {
    interrupt::end_of_interrupt();
    let me = cpu::get_cpu_id();
    let evict = &EVICT_REQUESTS[me];
    let default_cr3 = evict.load(Ordering::Acquire);
    if default_cr3 != 0 {
        // PCID 0 in bits 11:0 and bit 63 clear: flushes PCID 0's non-global translations.
        unsafe { asm!("mov cr3, {}", in(reg) default_cr3, options(nostack, preserves_flags)) };
        if regs.cs & 3 == 3 {
            cpu::set_evicted();
        }
        evict.store(0, Ordering::Release);
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

/// Halts with interrupts enabled until one arrives. `sti` delays interrupts by one instruction, so an
/// IPI already pending, or arriving before `hlt`, still ends the `hlt`.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_halt_until_ipi() {
    unsafe { asm!("sti", "hlt", "cli", options(nomem, nostack)) };
}

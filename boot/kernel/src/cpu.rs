//! The per-CPU data structure.
//!
//! The [`Cpu`] data structure is set as the `GS` base on the CPU.
//! It currently consists of the following:
//!
//! - GDT
//! - TSS
//! - IST stack spaces
//! - the kernel stack used by syscalls
//! - the frame-top word: the end of the trap frame of the thread this CPU runs

use core::arch::asm;
use core::mem::{offset_of, MaybeUninit};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};

use x86::msr;

use crate::gdt::{GlobalDescriptorTable, TaskStateSegment};
use crate::interrupt::x86_xapic::XAPIC;

/// One trap-layer CPU per verified `CpuId`.
pub const MAX_CPUS: usize = veriflat_monolith::NUM_CPUS;
const _: () = assert!(MAX_CPUS == astd::boot::MAX_CPUS);

/// `IA32_TSC_AUX`, read by `rdtscp`/`rdpid`: user code reads its CPU ID from it.
const IA32_TSC_AUX: u32 = 0xc000_0103;

/// Size of an IST stack (exceptions and IRQs only log or acknowledge).
const IST_STACK_SIZE: usize = 64 * 1024;

/// Size of the per-CPU kernel stack used by syscalls, interrupts from user mode, and the idle loop.
pub const KERNEL_STACK_SIZE: usize = 1024 * 1024;

/// Offset of a thread's saved `Registers` in its 4K page (`thread_trap_frame_addr` of the verified
/// kernel): the frame ends where the page's three list-node slots begin.
pub const THREAD_FRAME_OFFSET: usize = veriflat_monolith::PAGE_SZ_4K_LESS_3_NODE_SLOTS - veriflat_monolith::TRAP_FRAME_SZ;
/// Offset of the end of a thread's saved `Registers` in its page: the frame top, where the CPU
/// pushes the interrupt frame of a ring 3 interrupt (TSS.rsp0) and `sys_entry` starts its pushes.
pub const THREAD_FRAME_TOP_OFFSET: usize = veriflat_monolith::PAGE_SZ_4K_LESS_3_NODE_SLOTS;
const _: () = assert!(THREAD_FRAME_OFFSET == 3736 && veriflat_monolith::TRAP_FRAME_SZ == core::mem::size_of::<veriflat_monolith::Registers>());
// The CPU aligns rsp0 down to 16 bytes before it pushes an interrupt frame.
const _: () = assert!(THREAD_FRAME_TOP_OFFSET % 16 == 0);

const NEW_CPU: Cpu = Cpu::new();

/// Per-processor data.
static mut CPUS: [Cpu; MAX_CPUS] = [NEW_CPU; MAX_CPUS];

const _: () = assert!(KERNEL_STACK_SIZE % 4096 == 0);

/// Per-processor kernel stacks, page aligned.
#[repr(C, align(4096))]
struct KernelStacks {
    stacks: [Stack<KERNEL_STACK_SIZE>; MAX_CPUS],
}

static mut KERNEL_STACKS: KernelStacks = KernelStacks { stacks: [const { Stack::new() }; MAX_CPUS] };

/// Local APIC ID of each CPU ID, written by the BSP before it starts the APs.
static APIC_IDS: [AtomicU32; MAX_CPUS] = [const { AtomicU32::new(0) }; MAX_CPUS];

/// CPU IDs `0..PRESENT_CPUS` exist; the others stay Off in the verified model forever.
static PRESENT_CPUS: AtomicUsize = AtomicUsize::new(1);

/// Set once a CPU can take NMIs and IPIs.
static STARTED: [AtomicBool; MAX_CPUS] = [const { AtomicBool::new(false) }; MAX_CPUS];

macro_rules! read_current_cpu_offset {
    ($offset:expr) => {{
        let value: u64;
        unsafe {
            asm!(
                "mov {result}, gs:[{offset}]",
                offset = const $offset,
                result = out(reg) value,
            );
        }
        value
    }}
}

macro_rules! read_current_cpu_field {
    ($field:ident) => {
        read_current_cpu_offset!(offset_of!($crate::cpu::Cpu, $field))
    };
}

macro_rules! get_current_cpu_field_ptr {
    ($field:ident, $type:ty) => {{
        let mut address: u64 = core::mem::offset_of!($crate::cpu::Cpu, $field) as u64;
        #[allow(unused_unsafe)] // nested unsafe
        unsafe {
            core::arch::asm!(
                "add {result}, gs:{self_offset}",
                self_offset = const core::mem::offset_of!($crate::cpu::Cpu, self_ptr),
                result = inout(reg) address => address,
                options(pure, readonly),
            );
        }
        address as *mut $type
    }}
}
pub(crate) use get_current_cpu_field_ptr;

/// Per-processor data for a CPU.
#[repr(C, align(4096))]
pub struct Cpu {
    /// A pointer to ourselves.
    pub self_ptr: *const Cpu,

    /// The CPU ID (the VeriFlat `CpuId`).
    pub id: usize,

    /// The top of the kernel stack. The syscall and interrupt trampolines switch to it once the
    /// trap frame is saved; the idle loop and an AP start on it.
    pub kernel_sp: u64,

    /// The frame top of the thread this CPU runs (its page + [`THREAD_FRAME_TOP_OFFSET`]), equal to
    /// TSS.rsp0: `sys_entry` and the interrupt trampolines save the user registers right below it,
    /// into the thread's own trap-frame slot, and `restore_frame` is entered at `frame_top - 168`.
    /// Updated together with TSS.rsp0 by `syscalls::sync_current_frame` whenever the thread the
    /// verified kernel records as this CPU's current one changes; stale (unused) while the CPU has
    /// no thread.
    pub frame_top: u64,

    /// This CPU's object in the verified kernel's cpu array (inside its lock cell); set at boot.
    pub verified_cpu: *const veriflat_monolith::Cpu,

    /// Whether the timer handler re-arms the one-shot LAPIC timer (false while the CPU is Off).
    pub timer_on: bool,

    /// Set by every running-to-idle IPI (`platform::handle_running_to_idle_ipi`) together with
    /// `running_to_idle_ack_owed`, so outside the handler the two are equal; cleared with it by the
    /// idle loop when it acknowledges (`platform::acknowledge_running_to_idle`).
    /// While it is set the CPU runs on the kernel page table and must not return to ring 3:
    /// `restore_frame` diverts to the idle loop instead.
    pub running_to_idle_pending: AtomicBool,

    /// Set by every running-to-idle IPI after `running_to_idle_pending`: this CPU owes the sender
    /// its acknowledgement. The idle loop clears both flags and acknowledges when it enters and at
    /// the top of every iteration (`platform::acknowledge_running_to_idle`), after this CPU has left
    /// the trap path of the thread it ran. `platform::veriflat_halt_until_ipi` never halts while it
    /// is set.
    pub running_to_idle_ack_owed: AtomicBool,

    /// Set by the wake-up, running-to-idle, and timer handlers; cleared by every attempt to take this
    /// CPU's own lock, failed ones too (`platform::veriflat_disable_interrupts`). `platform::veriflat_halt_until_ipi` skips
    /// its `hlt` while it is set: an interrupt arrived after the last step read this CPU's state.
    pub wake_seen: AtomicBool,

    /// Remote flushes this CPU requested (`platform::veriflat_remote_flush_pcid`).
    pub remote_flushes: u64,

    /// State for the xAPIC driver.
    pub xapic: MaybeUninit<XAPIC>,

    /// The Global Descriptor Table.
    pub gdt: GlobalDescriptorTable,

    /// The Task State Segment.
    pub tss: TaskStateSegment,

    /// IST1 (exceptions) and IST2 (IRQs).
    pub ist: [IstStack; 2],
}

/// A stack.
#[repr(C, align(16))]
pub struct Stack<const SZ: usize>([u8; SZ]);

/// An IST stack.
pub type IstStack = Stack<IST_STACK_SIZE>;

impl<const SZ: usize> Stack<SZ> {
    pub const fn new() -> Self {
        Self([0u8; SZ])
    }

    pub fn bottom(&self) -> *const u8 {
        unsafe { self.0.as_ptr().add(SZ) }
    }

    /// Bytes from the bottom that were ever written (the stack starts zeroed).
    pub fn high_water(&self) -> usize {
        let used = self.0.iter().position(|b| *b != 0).unwrap_or(SZ);
        SZ - used
    }
}

unsafe impl Send for Cpu {}
unsafe impl Sync for Cpu {}

impl Cpu {
    pub const fn new() -> Self {
        Self {
            self_ptr: ptr::null(),
            id: 0,
            kernel_sp: 0,
            frame_top: 0,
            verified_cpu: ptr::null(),
            timer_on: false,
            running_to_idle_pending: AtomicBool::new(false),
            running_to_idle_ack_owed: AtomicBool::new(false),
            wake_seen: AtomicBool::new(false),
            remote_flushes: 0,
            xapic: MaybeUninit::uninit(),
            gdt: GlobalDescriptorTable::empty(),
            tss: {
                // No I/O permission bitmap: a base at or past the TSS limit denies every port to ring 3.
                let mut tss = TaskStateSegment::new();
                tss.iomap_base = core::mem::size_of::<TaskStateSegment>() as u16;
                tss
            },
            ist: [IstStack::new(), IstStack::new()],
        }
    }
}

/// Returns a handle to the current CPU's data structure.
pub fn get_current() -> &'static mut Cpu {
    let address = read_current_cpu_field!(self_ptr) as *mut Cpu;
    unsafe { &mut *address }
}

/// Returns the current CPU ID.
pub fn get_cpu_id() -> usize {
    read_current_cpu_field!(id) as usize
}

/// The current CPU ID from `IA32_TSC_AUX`, without `gs`. For code that can run while the GS base is
/// the user's: the NMI handler and faults in the return path after `swapgs`.
pub fn cpu_id_without_gs() -> usize {
    let id: u64;
    unsafe { asm!("rdpid {}", out(reg) id, options(nomem, nostack, preserves_flags)) };
    id as usize
}

/// The saved registers of the thread the current CPU runs, in that thread's page: right below
/// `frame_top`. Valid only while the CPU runs a thread and `frame_top` is synchronized.
pub fn current_frame() -> *mut veriflat_monolith::Registers {
    let top = read_current_cpu_field!(frame_top) as usize;
    (top - core::mem::size_of::<veriflat_monolith::Registers>()) as *mut _
}

/// The stack pointer an AP boots with: the top of its kernel stack.
pub fn idle_stack(cpu_id: usize) -> u64 {
    unsafe { (*(&raw const KERNEL_STACKS)).stacks[cpu_id].bottom() as u64 }
}

pub fn set_apic_id(cpu_id: usize, apic_id: u32) {
    APIC_IDS[cpu_id].store(apic_id, Ordering::Relaxed);
}

pub fn apic_id(cpu_id: usize) -> u32 {
    APIC_IDS[cpu_id].load(Ordering::Relaxed)
}

pub fn set_present_cpus(count: usize) {
    PRESENT_CPUS.store(count, Ordering::Release);
}

pub fn present_cpus() -> usize {
    PRESENT_CPUS.load(Ordering::Acquire)
}

pub fn mark_started(cpu_id: usize) {
    STARTED[cpu_id].store(true, Ordering::Release);
}

pub fn is_started(cpu_id: usize) -> bool {
    STARTED[cpu_id].load(Ordering::Acquire)
}

/// Sets `running_to_idle_pending`. For the running-to-idle IPI handler.
pub fn set_running_to_idle_pending() {
    get_current().running_to_idle_pending.store(true, Ordering::Relaxed);
}

/// Clears `running_to_idle_pending`. For the idle loop's acknowledgement.
pub fn clear_running_to_idle_pending() {
    get_current().running_to_idle_pending.store(false, Ordering::Relaxed);
}

/// Sets `running_to_idle_ack_owed`. For the running-to-idle IPI handler.
pub fn set_running_to_idle_ack_owed() {
    get_current().running_to_idle_ack_owed.store(true, Ordering::Relaxed);
}

/// Clears `running_to_idle_ack_owed` and returns whether it was set. For the idle loop's
/// acknowledgement. A load and a store suffice: no other running-to-idle IPI reaches this CPU
/// before it acknowledges the one that set the flag.
pub fn take_running_to_idle_ack_owed() -> bool {
    let owed = &get_current().running_to_idle_ack_owed;
    let was = owed.load(Ordering::Relaxed);
    if was {
        owed.store(false, Ordering::Relaxed);
    }
    was
}

/// Whether `running_to_idle_ack_owed` is set. For `veriflat_halt_until_ipi`.
pub fn running_to_idle_ack_owed() -> bool {
    get_current().running_to_idle_ack_owed.load(Ordering::Relaxed)
}

/// Sets `wake_seen`. For the wake-up, running-to-idle, and timer handlers.
pub fn set_wake_seen() {
    get_current().wake_seen.store(true, Ordering::Relaxed);
}

/// Clears `wake_seen`. For `veriflat_disable_interrupts`, at every attempt to take this CPU's own lock.
pub fn clear_wake_seen() {
    get_current().wake_seen.store(false, Ordering::Relaxed);
}

pub fn wake_seen() -> bool {
    get_current().wake_seen.load(Ordering::Relaxed)
}

/// Counts one remote flush request of the current CPU. Only this CPU writes its count.
pub fn count_remote_flush() {
    unsafe { asm!("inc qword ptr gs:[{offset}]", offset = const offset_of!(Cpu, remote_flushes), options(nostack)) };
}

/// Remote flushes requested by all CPUs so far.
pub fn remote_flushes() -> u64 {
    let cpus = unsafe { &*(&raw const CPUS) };
    cpus[..present_cpus()].iter().map(|cpu| unsafe { ptr::read_volatile(&cpu.remote_flushes) }).sum()
}

/// Kernel stack bytes ever used on `cpu_id`.
pub fn kernel_stack_high_water(cpu_id: usize) -> usize {
    unsafe { (*(&raw const KERNEL_STACKS)).stacks[cpu_id].high_water() }
}

/// CR0.MP: with TS set, `wait`/`fwait` raise #NM too.
pub const CR0_MP: u64 = 1 << 1;
/// CR0.TS: every x87/MMX instruction raises #NM.
pub const CR0_TS: u64 = 1 << 3;
/// CR4.OSFXSR: without it every SSE instruction raises #UD.
const CR4_OSFXSR: u64 = 1 << 9;
/// CR4.OSXSAVE: without it every AVX and XSAVE instruction raises #UD.
const CR4_OSXSAVE: u64 = 1 << 18;

/// Turns floating point off for user mode on the boot CPU (FPU plan A); the APs do the same in the AP
/// trampoline (`boot/ap_start.asm`).
///
/// Trusted fact: every CPU enters user mode with CR0.TS (and CR0.MP) set and CR4.OSFXSR/OSXSAVE clear;
/// the kernel never clears CR0.TS (no `clts`, no CR0 write without TS); the kernel is compiled
/// soft-float. So user x87/MMX instructions raise #NM, SSE/AVX raise #UD, the faulting thread exits,
/// and no floating-point register state passes from one thread to another.
///
/// TODO: floating-point support for user threads needs a per-thread "uses FP" flag fixed at creation,
/// CR0.TS following the incoming thread, and xsave/xrstor (plus a register reset from FP to non-FP
/// threads) on switches that involve an FP thread.
pub unsafe fn disable_user_fp() {
    asm!("mov {t}, cr0", "or {t}, {bits}", "mov cr0, {t}", t = out(reg) _, bits = const CR0_TS | CR0_MP, options(nostack));
}

/// Checks the FPU plan A state of the current CPU before its first entry to user mode: CR0.TS and
/// CR0.MP set, CR4.OSFXSR and CR4.OSXSAVE clear.
pub fn assert_user_fp_disabled() {
    let (cr0, cr4): (u64, u64);
    unsafe {
        asm!("mov {}, cr0", out(reg) cr0, options(nomem, nostack, preserves_flags));
        asm!("mov {}, cr4", out(reg) cr4, options(nomem, nostack, preserves_flags));
    }
    assert!(cr0 & (CR0_TS | CR0_MP) == CR0_TS | CR0_MP, "CPU {}: CR0 {:#x} lets user mode use the FPU", get_cpu_id(), cr0);
    assert!(cr4 & (CR4_OSFXSR | CR4_OSXSAVE) == 0, "CPU {}: CR4 {:#x} enables SSE/XSAVE", get_cpu_id(), cr4);
}

/// Initialize the CPU-local data structure.
///
/// This should only be called once.
pub unsafe fn init_cpu(cpu_id: usize) {
    assert!(cpu_id < MAX_CPUS);
    let cpu = &mut (*(&raw mut CPUS))[cpu_id];
    let address = cpu as *const Cpu;

    cpu.self_ptr = address;
    cpu.id = cpu_id;
    cpu.kernel_sp = (*(&raw const KERNEL_STACKS)).stacks[cpu_id].bottom() as u64;
    cpu.verified_cpu = crate::glue::verified_cpu(cpu_id);

    // In the kernel the GS base is this CPU's `Cpu` and IA32_KERNEL_GSBASE holds the user's (0);
    // `swapgs` at every ring 3 crossing exchanges them, so user loads of `gs` cannot reach the kernel.
    msr::wrmsr(msr::IA32_GS_BASE, address as u64);
    msr::wrmsr(msr::IA32_KERNEL_GSBASE, 0);
    assert!(core::arch::x86_64::__cpuid_count(7, 0).ecx & (1 << 22) != 0, "rdpid is required");
    msr::wrmsr(IA32_TSC_AUX, cpu_id as u64);
}

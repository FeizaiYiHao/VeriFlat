//! The per-CPU data structure.
//!
//! The [`Cpu`] data structure is set as the `GS` base on the CPU.
//! It currently consists of the following:
//!
//! - GDT
//! - TSS
//! - IST stack spaces
//! - the kernel stack used by syscalls

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

/// Bytes at the top of a kernel stack kept free for the trap-frame slot while code below it starts
/// from scratch: an AP booting, or a CPU evicted to its idle loop.
pub const FRAME_SLOT_RESERVE: usize = 4096;

const NEW_CPU: Cpu = Cpu::new();

/// Per-processor data.
static mut CPUS: [Cpu; MAX_CPUS] = [NEW_CPU; MAX_CPUS];

/// Per-processor kernel stacks.
static mut KERNEL_STACKS: [Stack<KERNEL_STACK_SIZE>; MAX_CPUS] = [const { Stack::new() }; MAX_CPUS];

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

    /// The top of the kernel stack; `sys_entry` and user-mode interrupts build the trap frame right below it.
    pub syscall_sp: u64,

    /// Whether the timer handler re-arms the one-shot LAPIC timer (false while the CPU is Off).
    pub timer_on: bool,

    /// Set by an eviction NMI (`platform::veriflat_remote_evict`), cleared on entry to the idle loop.
    /// While it is set the CPU runs on the kernel page table and must not return to ring 3:
    /// `restore_frame` diverts to the idle loop instead.
    pub evicted: AtomicBool,

    /// Returns of `restore_frame` through `sysretq` and through `iretq`.
    pub sysret_exits: u64,
    pub iret_exits: u64,

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
            syscall_sp: 0,
            timer_on: false,
            evicted: AtomicBool::new(false),
            sysret_exits: 0,
            iret_exits: 0,
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

/// Returns the frame slot at the top of the current CPU's kernel stack.
pub fn top_frame() -> *mut veriflat_monolith::Registers {
    let sp = read_current_cpu_field!(syscall_sp) as usize;
    (sp - core::mem::size_of::<veriflat_monolith::Registers>()) as *mut _
}

/// The stack pointer an AP boots with and an evicted CPU restarts with: below the trap-frame slot
/// of its kernel stack.
pub fn idle_stack(cpu_id: usize) -> u64 {
    unsafe { (*(&raw const KERNEL_STACKS))[cpu_id].bottom() as u64 - FRAME_SLOT_RESERVE as u64 }
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

/// Marks `cpu_id` evicted. For the NMI handler, which cannot use `gs`.
pub fn set_evicted(cpu_id: usize) {
    unsafe { (*(&raw const CPUS))[cpu_id].evicted.store(true, Ordering::Relaxed) };
}

pub fn is_evicted() -> bool {
    get_current().evicted.load(Ordering::Relaxed)
}

pub fn clear_evicted() {
    get_current().evicted.store(false, Ordering::Relaxed);
}

/// Returns of `restore_frame` through `sysretq` and through `iretq` on all CPUs so far.
pub fn restore_frame_exits() -> (u64, u64) {
    let cpus = unsafe { &*(&raw const CPUS) };
    cpus[..present_cpus()].iter().fold((0, 0), |(sysret, iret), cpu| unsafe {
        (sysret + ptr::read_volatile(&cpu.sysret_exits), iret + ptr::read_volatile(&cpu.iret_exits))
    })
}

/// Kernel stack bytes ever used on `cpu_id`.
pub fn kernel_stack_high_water(cpu_id: usize) -> usize {
    unsafe { (*(&raw const KERNEL_STACKS))[cpu_id].high_water() }
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
    cpu.syscall_sp = (*(&raw const KERNEL_STACKS))[cpu_id].bottom() as u64;

    // In the kernel the GS base is this CPU's `Cpu` and IA32_KERNEL_GSBASE holds the user's (0);
    // `swapgs` at every ring 3 crossing exchanges them, so user loads of `gs` cannot reach the kernel.
    msr::wrmsr(msr::IA32_GS_BASE, address as u64);
    msr::wrmsr(msr::IA32_KERNEL_GSBASE, 0);
    assert!(core::arch::x86_64::__cpuid_count(7, 0).ecx & (1 << 22) != 0, "rdpid is required");
    msr::wrmsr(IA32_TSC_AUX, cpu_id as u64);
}

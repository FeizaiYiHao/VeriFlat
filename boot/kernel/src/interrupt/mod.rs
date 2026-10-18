//! Interrupt handling.

// Copyright 2021 Zhaofeng Li
// Copyright 2017 Philipp Oppermann
//
// Licensed under the MIT license <http://opensource.org/licenses/MIT>.
// See top-level LICENSE.

mod exception;
mod idt;
mod ioapic;
mod lapic;
mod mps;
pub mod x86_xapic;

use core::arch::{asm, naked_asm};
use core::convert::{Into, TryFrom};
use core::mem::offset_of;

use x86::io::{inb, outb};
use x86::Ring;

pub use exception::Exception;
use exception::EXCEPTION_MAX;
use idt::Idt;
#[allow(unused_imports)]
pub use lapic::{boot_ap, current_apic_id, disarm_timer, end_of_interrupt, send_ipi, send_nmi, set_timer};
use veriflat_monolith::Registers;

/// The IRQ offset.
pub const IRQ_OFFSET: usize = 32;

pub const IRQ_TIMER: usize = 0;

/// The wake-up IPI of `veriflat_send_ipi`.
pub const IRQ_WAKE: usize = 32;
pub const VECTOR_WAKE: u8 = (IRQ_OFFSET + IRQ_WAKE) as u8;

pub const IST_EXCEPTION: usize = 1;
pub const IST_IRQ: usize = 2;

/// NMIs can arrive anywhere, including in `sys_entry` before it switches stacks and in
/// `restore_frame` after it loads the user `rsp` for `sysretq`, so they get their own IST stack.
/// Every exception entry defaults to `IST_EXCEPTION` (`Entry::missing_exception`), which also
/// covers machine checks there. IRQs use no IST: from user mode they build their frame at the top
/// of the kernel stack like `sys_entry`, and in the kernel they only arrive at `hlt`.
pub const IST_NMI: usize = IST_IRQ;

/// The global IDT.
static mut GLOBAL_IDT: Idt = Idt::new();

const PIC1_DATA: u16 = 0x21;
const PIC2_DATA: u16 = 0xa1;

/// An amount of cycles.
#[derive(Debug)]
#[repr(transparent)]
pub struct Cycles(pub usize);

#[repr(C)]
pub struct TrampolineMarker(());

/// Builds a naked trampoline that saves the interrupted registers as a `Registers` frame, calls
/// `handler(&mut frame)`, restores the frame, and returns with `iretq`. `prologue` runs first,
/// with `rsp` at the CPU-pushed part of the frame, and `epilogue` runs after the handler, with `rsp`
/// at the frame; `operands` are extra `naked_asm!` operands for both.
macro_rules! trampoline {
    ($handler:path, [$($prologue:literal),* $(,)?], [$($epilogue:literal),* $(,)?] $(, $($operands:tt)+)?) => {{
        let _: unsafe extern "C" fn(&mut Registers) = $handler;

        /// Interrupt trampoline
        #[unsafe(naked)]
        unsafe extern "C" fn trampoline(_: TrampolineMarker) {
            naked_asm!(
                $($prologue,)*
                "push rax",
                "push rdi",
                "push rsi",
                "push rdx",
                "push rcx",
                "push r8",
                "push r9",
                "push r10",
                "push r11",
                "push rbx",
                "push rbp",
                "push r12",
                "push r13",
                "push r14",
                "push r15",

                // fn handler(registers: &mut Registers); 21 qwords keep rsp 8 off alignment
                "mov rdi, rsp",
                "sub rsp, 8",
                "call {handler}",
                "add rsp, 8",
                $($epilogue,)*

                "pop r15",
                "pop r14",
                "pop r13",
                "pop r12",
                "pop rbp",
                "pop rbx",
                "pop r11",
                "pop r10",
                "pop r9",
                "pop r8",
                "pop rcx",
                "pop rdx",
                "pop rsi",
                "pop rdi",
                "pop rax",
                "add rsp, 8", // error_code
                "iretq",

                handler = sym $handler,
                $($($operands)+)?
            );
        }

        trampoline
    }}
}

/// Wraps a `Registers` handler for a vector whose frame carries a CPU error code. A frame from
/// ring 3 (`cs` at `[rsp + 16]` has RPL 3) needs `swapgs` on the way in, and leaves through
/// `restore_frame`, the only exit to ring 3 (an eviction relies on it); a frame from the kernel
/// already has the kernel GS base.
macro_rules! wrap_interrupt_with_error_code {
    ($handler:path) => {
        // Here rsp is at [error_code][rip][cs][rflags][rsp][ss]
        trampoline!($handler, ["cld", "test byte ptr [rsp + 16], 3", "jz 1f", "swapgs", "1:"],
            ["test byte ptr [rsp + {frame_cs}], 3", "jnz {restore}"],
            frame_cs = const offset_of!(Registers, cs), restore = sym crate::syscalls::restore_frame)
    };
}

/// Wraps a `Registers` handler for a vector without a CPU error code.
macro_rules! wrap_interrupt {
    ($handler:path) => {
        // Here rsp is at [rip][cs][rflags][rsp][ss]; push 0 as the error code first
        trampoline!($handler, ["cld", "push 0", "test byte ptr [rsp + 16], 3", "jz 1f", "swapgs", "1:"],
            ["test byte ptr [rsp + {frame_cs}], 3", "jnz {restore}"],
            frame_cs = const offset_of!(Registers, cs), restore = sym crate::syscalls::restore_frame)
    };
}

/// Wraps the NMI handler. An NMI can land between a `swapgs` and the ring crossing it belongs to,
/// where the frame's `cs` says nothing about which GS base is loaded, so the NMI path never touches
/// `gs` at all and the handler uses `cpu_id_without_gs`. It returns with `iretq` to the frame as the
/// handler left it, which an eviction rewrites.
macro_rules! wrap_nmi {
    ($handler:path) => {
        trampoline!($handler, ["cld", "push 0"], [])
    };
}

/// A handler function wrapped by the interrupt trampoline.
pub type TrampolineHandlerFunc = unsafe extern "C" fn(TrampolineMarker);

/// Logs a fatal exception and exits QEMU with status 3.
///
/// TODO: a fault in ring 3 (`regs.cs & 3 == 3`) is the faulting thread's problem, not the
/// machine's. It should end only that thread (or deliver to its container) instead of exiting;
/// today any user thread can take the whole machine down.
fn fatal_exception(name: &str, regs: &Registers) -> ! {
    let cr2: u64;
    unsafe { asm!("mov {}, cr2", out(reg) cr2) };
    log::error!(
        "CPU {}: {} (error code {:#x}, cr2 {:#x}) at rip {:#x} cs {:#x} rsp {:#x}: {:#x?}",
        crate::cpu::cpu_id_without_gs(),
        name,
        regs.error_code,
        cr2,
        regs.rip,
        regs.cs,
        regs.rsp,
        regs,
    );
    unsafe { crate::boot::exit_qemu(3) }
}

macro_rules! fatal_handlers {
    ($($name:ident => $msg:expr),* $(,)?) => {
        $(
            unsafe extern "C" fn $name(regs: &mut Registers) {
                fatal_exception($msg, regs)
            }
        )*
    };
}

fatal_handlers! {
    divide_by_zero => "Divide Error",
    debug => "Debug",
    overflow => "Overflow",
    bound_range_exceeded => "Bound Range Exceeded",
    invalid_opcode => "Invalid Opcode",
    device_not_available => "Device Not Available",
    double_fault => "Double Fault",
    invalid_tss => "Invalid TSS",
    segment_not_present => "Segment Not Present",
    stack_segment_fault => "Stack Segment Fault",
    general_protection_fault => "General Protection Fault",
    x87_floating_point => "x87 Floating-Point",
    alignment_check => "Alignment Check",
    machine_check => "Machine Check",
    simd_floating_point => "SIMD Floating-Point",
    virtualization => "Virtualization",
    security_exception => "Security",
}

/// Breakpoint handler.
unsafe extern "C" fn breakpoint(regs: &mut Registers) {
    log::warn!("CPU {}: Breakpoint: {:#x?}", crate::cpu::get_cpu_id(), regs);
}

/// Page fault: a fault of the user-memory copy resumes at the copy's exit; any other is fatal.
unsafe extern "C" fn page_fault(regs: &mut Registers) {
    match crate::syscalls::user_copy_fixup(regs) {
        Some(rip) => regs.rip = rip,
        None => fatal_exception("Page Fault", regs),
    }
}

/// NMI: remote TLB flush and eviction requests.
unsafe extern "C" fn non_maskable_interrupt(regs: &mut Registers) {
    crate::platform::handle_nmi(regs);
}

/// Timer handler.
unsafe extern "C" fn timer(regs: &mut Registers) {
    crate::syscalls::timer_interrupt(regs);
}

/// Wake-up IPI handler.
unsafe extern "C" fn wake(regs: &mut Registers) {
    crate::syscalls::wake_interrupt(regs);
}

/// Any other IRQ.
unsafe extern "C" fn spurious(_regs: &mut Registers) {
    log::warn!("CPU {}: unexpected IRQ", crate::cpu::get_cpu_id());
    end_of_interrupt();
}

/// An interrupt.
#[derive(Copy, Clone, Debug)]
#[allow(dead_code)]
pub enum Interrupt {
    /// An exception.
    Exception(Exception),

    /// An IRQ.
    Irq(usize),
}

impl From<Interrupt> for usize {
    fn from(interrupt: Interrupt) -> usize {
        match interrupt {
            Interrupt::Exception(ex) => ex.into(),
            Interrupt::Irq(num) => IRQ_OFFSET + num,
        }
    }
}

impl TryFrom<usize> for Interrupt {
    type Error = &'static str;

    fn try_from(num: usize) -> Result<Self, Self::Error> {
        match num {
            0..=EXCEPTION_MAX => TryFrom::try_from(num).map(Self::Exception),
            IRQ_OFFSET..=255 => Ok(Self::Irq(num)),
            _ => Err("Invalid interrupt line"),
        }
    }
}

/// Initializes global interrupt controllers.
///
/// This should be called only once.
pub unsafe fn init() {
    // Disable 8259 PIC
    let _ = (inb(PIC1_DATA), inb(PIC2_DATA));
    outb(PIC1_DATA, 0xff);
    outb(PIC2_DATA, 0xff);

    let idt = &mut *(&raw mut GLOBAL_IDT);
    idt.divide_by_zero.set_handler_fn(wrap_interrupt!(divide_by_zero));
    idt.debug.set_handler_fn(wrap_interrupt!(debug));
    idt.non_maskable_interrupt.set_handler_fn(wrap_nmi!(non_maskable_interrupt));
    idt.non_maskable_interrupt.set_ist(IST_NMI as u8);
    idt.breakpoint.set_handler_fn(wrap_interrupt!(breakpoint));
    idt.breakpoint.attributes.set_privilege_level(Ring::Ring3);
    idt.overflow.set_handler_fn(wrap_interrupt!(overflow));
    idt.bound_range_exceeded.set_handler_fn(wrap_interrupt!(bound_range_exceeded));
    idt.invalid_opcode.set_handler_fn(wrap_interrupt!(invalid_opcode));
    idt.device_not_available.set_handler_fn(wrap_interrupt!(device_not_available));
    idt.double_fault.set_handler_fn(wrap_interrupt_with_error_code!(double_fault));
    idt.invalid_tss.set_handler_fn(wrap_interrupt_with_error_code!(invalid_tss));
    idt.segment_not_present.set_handler_fn(wrap_interrupt_with_error_code!(segment_not_present));
    idt.stack_segment_fault.set_handler_fn(wrap_interrupt_with_error_code!(stack_segment_fault));
    idt.general_protection_fault.set_handler_fn(wrap_interrupt_with_error_code!(general_protection_fault));
    idt.page_fault.set_handler_fn(wrap_interrupt_with_error_code!(page_fault));
    idt.x87_floating_point.set_handler_fn(wrap_interrupt!(x87_floating_point));
    idt.alignment_check.set_handler_fn(wrap_interrupt_with_error_code!(alignment_check));
    idt.machine_check.set_handler_fn(wrap_interrupt!(machine_check));
    idt.simd_floating_point.set_handler_fn(wrap_interrupt!(simd_floating_point));
    idt.virtualization.set_handler_fn(wrap_interrupt!(virtualization));
    idt.security_exception.set_handler_fn(wrap_interrupt_with_error_code!(security_exception));

    for irq in 0..idt.interrupts.len() {
        idt.interrupts[irq].set_handler_fn(wrap_interrupt!(spurious));
        idt.interrupts[irq].set_ist(0);
    }
    idt.interrupts[IRQ_TIMER].set_handler_fn(wrap_interrupt!(timer));
    idt.interrupts[IRQ_WAKE].set_handler_fn(wrap_interrupt!(wake));
}

/// Initializes per-CPU interrupt controllers.
///
/// This should be called only once per CPU.
pub unsafe fn init_cpu() {
    lapic::init();

    (*(&raw const GLOBAL_IDT)).load();
}

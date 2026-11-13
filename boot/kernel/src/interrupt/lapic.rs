//! LAPIC.
//!
//! xAPIC mode uses the vendored xAPIC MMIO driver (`x86_xapic`); x2APIC mode uses the x2APIC MSRs directly. The boot
//! CPU decides the mode for every CPU: x2APIC when the firmware handed it over in x2APIC mode (IA32_APIC_BASE.EXTD set;
//! VeriFlat never leaves x2APIC mode once in it), or when the boot option `x2apic=on` asks for it and CPUID.01H:ECX[21]
//! reports x2APIC; xAPIC otherwise, as before. Every AP then enters the same mode. APIC IDs above 254 are refused:
//! the loader hands the kernel 8-bit IDs and 255 is the xAPIC broadcast ID.

use core::arch::asm;
use core::mem::MaybeUninit;
use core::slice;
use core::sync::atomic::{AtomicBool, Ordering};

use super::x86_xapic::XAPIC;
use x86::apic::{ApicControl, ApicId, DeliveryMode, DeliveryStatus, DestinationMode, DestinationShorthand, Icr, Level, TriggerMode};
use x86::msr::{self, rdmsr, wrmsr};

use super::Cycles;
use crate::boot::ap_start::StartTrampoline;
use crate::{boot, cpu};

/// IA32_APIC_BASE.EXTD (x2APIC mode) and .EN (APIC globally enabled).
const APIC_BASE_EXTD: u64 = 1 << 10;
const APIC_BASE_EN: u64 = 1 << 11;
/// x2APIC registers (MSR 0x800 + xAPIC offset / 16).
const X2APIC_ID: u32 = 0x802;
const X2APIC_EOI: u32 = 0x80b;
const X2APIC_SVR: u32 = 0x80f;
const X2APIC_ICR: u32 = 0x830;
const X2APIC_LVT_TIMER: u32 = 0x832;
const X2APIC_INIT_COUNT: u32 = 0x838;
/// SVR: APIC software enable, spurious vector 15 (as the xAPIC driver's `attach`).
const SVR_VALUE: u64 = 1 << 8 | 15;
/// The timer vector the xAPIC path passes to `tsc_enable`.
const TIMER_VECTOR: u64 = 32;
/// The largest APIC ID VeriFlat supports.
const MAX_APIC_ID: u32 = 254;

/// Whether every CPU runs its local APIC in x2APIC mode; decided by the boot CPU in `init`.
static X2APIC: AtomicBool = AtomicBool::new(false);

/// Whether the local APICs run in x2APIC mode.
pub fn x2apic_mode() -> bool {
    X2APIC.load(Ordering::Relaxed)
}

/// Returns the 4KiB LAPIC region.
unsafe fn probe_apic() -> &'static mut [u32] {
    let msr27: u32 = msr::rdmsr(msr::APIC_BASE) as u32;
    let lapic = (msr27 & 0xffff_0000) as usize as *mut u32;

    slice::from_raw_parts_mut(lapic, 4096 / 4)
}

/// Whether CPUID.01H:ECX[21] reports x2APIC.
fn cpu_has_x2apic() -> bool {
    core::arch::x86_64::__cpuid(1).ecx & (1 << 21) != 0
}

/// Initializes this CPU's local APIC in the mode the boot CPU chose. On the boot CPU (CPU 0) it runs before the command
/// line is read, so it only follows the firmware's mode; `switch_to_x2apic_if_requested` applies `x2apic=on` later.
pub unsafe fn init() {
    let cpu = cpu::get_current();
    let base = rdmsr(msr::IA32_APIC_BASE);
    if cpu.id == 0 {
        if base & APIC_BASE_EXTD != 0 {
            log::info!("local APIC handed over in x2APIC mode: the kernel stays in x2APIC mode");
            X2APIC.store(true, Ordering::Relaxed);
        }
    } else if !x2apic_mode() {
        assert!(base & APIC_BASE_EXTD == 0, "CPU {} is in x2APIC mode while the boot CPU uses xAPIC mode", cpu.id);
    }
    if x2apic_mode() {
        init_x2apic(cpu.id);
        return;
    }

    let apic_region = probe_apic();
    log::debug!("APIC base: {:?}", apic_region as *mut _ as *mut u8);

    let mut xapic = XAPIC::new(apic_region);
    xapic.attach();
    xapic.tsc_enable(32);

    cpu.xapic.write(xapic);
}

/// Boot option `x2apic=on`, on the boot CPU after the command line is read and before any AP starts: switches its
/// local APIC from xAPIC to x2APIC mode when CPUID reports x2APIC (xAPIC to x2APIC is a legal direct transition), so
/// that every AP follows. Logs the mode the kernel runs in.
pub unsafe fn switch_to_x2apic_if_requested() {
    if !x2apic_mode() && boot::get_command_line().x2apic_on {
        if cpu_has_x2apic() {
            X2APIC.store(true, Ordering::Relaxed);
            init_x2apic(0);
            log::info!("x2apic=on: switched the local APIC from xAPIC to x2APIC mode");
        } else {
            log::warn!("x2apic=on ignored: CPUID.01H:ECX[21] reports no x2APIC");
        }
    }
    log::info!("local APIC mode: {}, boot CPU APIC ID {}", if x2apic_mode() { "x2APIC" } else { "xAPIC" }, current_apic_id());
}

/// Enters x2APIC mode on this CPU if it is not in it already, enables the APIC with the xAPIC path's spurious vector
/// and arms nothing: the timer LVT gets vector 32, unmasked, one-shot, as `XAPIC::tsc_enable`.
unsafe fn init_x2apic(cpu_id: usize) {
    let base = rdmsr(msr::IA32_APIC_BASE);
    if base & APIC_BASE_EXTD == 0 {
        // Disabled -> xAPIC -> x2APIC; both bits together are also legal from the disabled state.
        wrmsr(msr::IA32_APIC_BASE, base | APIC_BASE_EN);
        wrmsr(msr::IA32_APIC_BASE, base | APIC_BASE_EN | APIC_BASE_EXTD);
    }
    let id = rdmsr(X2APIC_ID) as u32;
    assert!(id <= MAX_APIC_ID, "CPU {}: x2APIC ID {} is above {}, which VeriFlat does not support", cpu_id, id, MAX_APIC_ID);
    wrmsr(X2APIC_SVR, SVR_VALUE);
    let lvt = rdmsr(X2APIC_LVT_TIMER) & !0xff & !(1 << 16) & !(0b11 << 17);
    wrmsr(X2APIC_LVT_TIMER, lvt | TIMER_VECTOR);
}

/// This CPU's xAPIC.
fn xapic() -> &'static mut XAPIC {
    unsafe { (&mut *crate::cpu::get_current_cpu_field_ptr!(xapic, MaybeUninit<XAPIC>)).assume_init_mut() }
}

/// Arms the one-shot timer interrupt.
pub fn set_timer(cycles: Cycles) {
    // FIXME: Truncated
    if x2apic_mode() {
        unsafe { wrmsr(X2APIC_INIT_COUNT, cycles.0 as u32 as u64) };
    } else {
        xapic().tsc_set_oneshot(cycles.0 as u32);
    }
}

/// Cancels a pending one-shot timer.
pub fn disarm_timer() {
    if x2apic_mode() {
        unsafe { wrmsr(X2APIC_INIT_COUNT, 0) };
    } else {
        xapic().tsc_set_oneshot(0);
    }
}

/// Acknowledges an interrupt.
pub fn end_of_interrupt() {
    if x2apic_mode() {
        unsafe { wrmsr(X2APIC_EOI, 0) };
    } else {
        xapic().eoi();
    }
}

/// This CPU's local APIC ID.
pub fn current_apic_id() -> u32 {
    if x2apic_mode() {
        unsafe { rdmsr(X2APIC_ID) as u32 }
    } else {
        xapic().id() >> 24
    }
}

/// Writes an x2APIC ICR: one WRMSR with the destination in bits 63:32. WRMSR to the x2APIC ICR is not serializing,
/// so a full fence first makes this CPU's earlier stores visible before the target can take the interrupt.
unsafe fn x2apic_icr(apic_id: u32, low: u32) {
    asm!("mfence", "lfence", options(nostack, preserves_flags));
    wrmsr(X2APIC_ICR, (apic_id as u64) << 32 | low as u64);
}

fn icr(apic_id: u32, vector: u8, mode: DeliveryMode, level: Level, trigger: TriggerMode) -> Icr {
    Icr::for_xapic(
        vector,
        ApicId::XApic(apic_id as u8),
        DestinationShorthand::NoShorthand,
        mode,
        DestinationMode::Physical,
        DeliveryStatus::Idle,
        level,
        trigger,
    )
}

fn send(apic_id: u32, vector: u8, mode: DeliveryMode) {
    let icr = icr(apic_id, vector, mode, Level::Assert, TriggerMode::Edge);
    if x2apic_mode() {
        unsafe { x2apic_icr(apic_id, icr.lower()) };
    } else {
        unsafe { xapic().send_ipi(icr) };
    }
}

/// Sends a fixed-vector IPI.
pub fn send_ipi(apic_id: u32, vector: u8) {
    send(apic_id, vector, DeliveryMode::Fixed);
}

/// Sends an NMI.
pub fn send_nmi(apic_id: u32) {
    send(apic_id, 0, DeliveryMode::NMI);
}

/// Busy-waits for about `cycles` TSC cycles.
fn delay(cycles: u64) {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while unsafe { core::arch::x86_64::_rdtsc() } - start < cycles {
        core::hint::spin_loop();
    }
}

/// Boots an application processor: it enters `code(arg)` on `stack` with the kernel page table.
pub unsafe fn boot_ap(apic_id: u32, arg: u64, stack: u64, code: u64) {
    let boot_info = boot::get_boot_info();
    let start_page = StartTrampoline::new(0x7000)
        .unwrap()
        .with_code(code)
        .with_cr3(boot_info.pml4 as u64)
        .with_stack(stack)
        .with_arg(arg)
        .start_page();

    // INIT, then two STARTUPs (Intel SDM 8.4.4.1).
    if x2apic_mode() {
        x2apic_icr(apic_id, icr(apic_id, 0, DeliveryMode::Init, Level::Assert, TriggerMode::Level).lower());
        delay(20_000_000);
        let startup = icr(apic_id, start_page, DeliveryMode::StartUp, Level::Assert, TriggerMode::Edge).lower();
        x2apic_icr(apic_id, startup);
        delay(1_000_000);
        x2apic_icr(apic_id, startup);
        return;
    }
    let apic = ApicId::XApic(apic_id as u8);
    xapic().ipi_init(apic);
    delay(20_000_000);
    xapic().ipi_startup(apic, start_page);
    delay(1_000_000);
    xapic().ipi_startup(apic, start_page);
}

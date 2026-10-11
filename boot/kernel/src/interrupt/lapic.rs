//! LAPIC.
//!
//! We just use the xAPIC implementation in the x86 crate.

use core::mem::MaybeUninit;
use core::slice;

use super::x86_xapic::XAPIC;
use x86::apic::{ApicControl, ApicId, DeliveryMode, DeliveryStatus, DestinationMode, DestinationShorthand, Icr, Level, TriggerMode};
use x86::msr;

use super::Cycles;
use crate::boot::ap_start::StartTrampoline;
use crate::{boot, cpu};

/// Returns the 4KiB LAPIC region.
unsafe fn probe_apic() -> &'static mut [u32] {
    let msr27: u32 = msr::rdmsr(msr::APIC_BASE) as u32;
    let lapic = (msr27 & 0xffff_0000) as usize as *mut u32;

    slice::from_raw_parts_mut(lapic, 4096 / 4)
}

/// Initializes LAPIC in xAPIC mode.
pub unsafe fn init() {
    let cpu = cpu::get_current();

    let apic_region = probe_apic();
    log::debug!("APIC base: {:?}", apic_region as *mut _ as *mut u8);

    let mut xapic = XAPIC::new(apic_region);
    xapic.attach();
    xapic.tsc_enable(32);

    cpu.xapic.write(xapic);
}

/// This CPU's xAPIC.
fn xapic() -> &'static mut XAPIC {
    unsafe { (&mut *crate::cpu::get_current_cpu_field_ptr!(xapic, MaybeUninit<XAPIC>)).assume_init_mut() }
}

/// Arms the one-shot timer interrupt.
pub fn set_timer(cycles: Cycles) {
    // FIXME: Truncated
    xapic().tsc_set_oneshot(cycles.0 as u32);
}

/// Cancels a pending one-shot timer.
pub fn disarm_timer() {
    xapic().tsc_set_oneshot(0);
}

/// Acknowledges an interrupt.
pub fn end_of_interrupt() {
    xapic().eoi();
}

/// This CPU's local APIC ID.
pub fn current_apic_id() -> u32 {
    xapic().id() >> 24
}

fn send(apic_id: u32, vector: u8, mode: DeliveryMode) {
    let icr = Icr::for_xapic(
        vector,
        ApicId::XApic(apic_id as u8),
        DestinationShorthand::NoShorthand,
        mode,
        DestinationMode::Physical,
        DeliveryStatus::Idle,
        Level::Assert,
        TriggerMode::Edge,
    );
    unsafe { xapic().send_ipi(icr) };
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
    let apic = ApicId::XApic(apic_id as u8);
    xapic().ipi_init(apic);
    delay(20_000_000);
    xapic().ipi_startup(apic, start_page);
    delay(1_000_000);
    xapic().ipi_startup(apic, start_page);
}

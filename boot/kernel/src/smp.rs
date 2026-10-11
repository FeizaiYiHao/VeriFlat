//! Application processor bring-up.
//!
//! CPU 0 is the BSP. The other processors of the ACPI MADT get CPU IDs in table order. Each one
//! boots through the real-mode trampoline at 0x7000, initializes its per-CPU state, and parks Off:
//! the verified model starts every CPU but 0 Off, and `cpu_online` wakes it.

use core::arch::asm;

use crate::cpu::{self, MAX_CPUS};
use crate::{gdt, interrupt, syscalls};

/// CR4.PCIDE: aloader sets it on the BSP; the trampoline does not.
const CR4_PCIDE: u64 = 1 << 17;

/// TSC cycles to wait for an AP to report in.
const AP_START_TIMEOUT: u64 = 2_000_000_000;

/// Starts every other enabled processor, one at a time (they share the trampoline).
pub unsafe fn start_aps() {
    let bsp = interrupt::current_apic_id();
    cpu::set_apic_id(0, bsp);
    let mut count = 1;
    for &apic_id in crate::boot::get_boot_info().apic_ids.iter() {
        let apic_id = apic_id as u32;
        if apic_id == bsp {
            continue;
        }
        if count == MAX_CPUS {
            log::warn!("more than {} processors; APIC ID {} stays down", MAX_CPUS, apic_id);
            continue;
        }
        cpu::set_apic_id(count, apic_id);
        interrupt::boot_ap(apic_id, count as u64, cpu::ap_boot_stack(count), ap_main as *const () as u64);
        let start = core::arch::x86_64::_rdtsc();
        while !cpu::is_started(count) {
            if core::arch::x86_64::_rdtsc() - start > AP_START_TIMEOUT {
                panic!("CPU {} (APIC ID {}) did not start", count, apic_id);
            }
            core::hint::spin_loop();
        }
        count += 1;
    }
    cpu::set_present_cpus(count);
    log::info!("{} CPUs present", count);
}

/// AP entry from the trampoline, on the AP's kernel stack below its trap-frame slot.
extern "C" fn ap_main(cpu_id: u64) -> ! {
    let cpu_id = cpu_id as usize;
    unsafe {
        asm!("mov {t}, cr4", "or {t}, {pcide}", "mov cr4, {t}", t = out(reg) _, pcide = const CR4_PCIDE, options(nostack));
        cpu::init_cpu(cpu_id);
        gdt::init_cpu();
        interrupt::init_cpu();
        syscalls::init_cpu();
    }
    cpu::mark_started(cpu_id);
    unsafe { syscalls::enter_off_cpu() }
}

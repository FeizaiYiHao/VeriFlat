//! Port of Atmosphere's libtime: `rdtsc` and the busy-wait `sys_ns_loopsleep`. Atmosphere converts at a
//! fixed 2 TSC cycles per ns; here the TSC rate comes from CPUID (`tsc_hz`).

pub fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// The TSC rate in Hz: CPUID 16H (processor base frequency, which KVM passes through with `-cpu host`),
/// else the hypervisor timing leaf 4000_0010H (TSC kHz), else the 2.2 GHz of the test machine.
pub fn tsc_hz() -> u64 {
    use core::arch::x86_64::__cpuid;
    if __cpuid(0).eax >= 0x16 {
        let mhz = __cpuid(0x16).eax as u64;
        if mhz != 0 {
            return mhz * 1_000_000;
        }
    }
    if __cpuid(0x4000_0000).eax >= 0x4000_0010 {
        let khz = __cpuid(0x4000_0010).eax as u64;
        if khz != 0 {
            return khz * 1_000;
        }
    }
    2_200_000_000
}

pub fn sys_ns_loopsleep(ns: u64) {
    let target = rdtsc() + (ns as u128 * tsc_hz() as u128 / 1_000_000_000) as u64;
    while rdtsc() < target {
        core::hint::spin_loop();
    }
}

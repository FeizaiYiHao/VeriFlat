//! Port of Atmosphere's libtime: `rdtsc` and the busy-wait `sys_ns_loopsleep`. Atmosphere converts at a
//! fixed 2 TSC cycles per ns; here the TSC rate comes from `tsc_rate`.

use core::sync::atomic::{AtomicU64, Ordering};

/// `VERIFLAT_TSC_MHZ` of the dom0 build: the TSC rate in MHz, ahead of every CPUID source.
const TSC_MHZ_OVERRIDE: Option<u64> = match option_env!("VERIFLAT_TSC_MHZ") {
    Some(s) => Some(parse_mhz(s)),
    None => None,
};

const fn parse_mhz(s: &str) -> u64 {
    let b = s.as_bytes();
    let mut i = 0;
    let mut v = 0;
    while i < b.len() {
        assert!(b[i].is_ascii_digit(), "VERIFLAT_TSC_MHZ must be a decimal number");
        v = v * 10 + (b[i] - b'0') as u64;
        i += 1;
    }
    assert!(v != 0, "VERIFLAT_TSC_MHZ must not be 0");
    v
}

/// The rate `tsc_hz` returns, once it has been read.
static TSC_HZ: AtomicU64 = AtomicU64::new(0);

pub fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// The TSC rate in Hz and where it comes from, in this order: `VERIFLAT_TSC_MHZ` of the build; CPUID 16H
/// (processor base frequency, which KVM passes through with `-cpu host`); the hypervisor timing leaf 4000_0010H
/// (TSC kHz); the "@ x.xxGHz" nominal frequency at the end of the CPUID brand string, at which the invariant TSC
/// of Intel processors without leaf 16H (Haswell Xeons among them) runs. `None` when no source gives a rate.
pub fn tsc_rate() -> Option<(u64, &'static str)> {
    use core::arch::x86_64::__cpuid;
    if let Some(mhz) = TSC_MHZ_OVERRIDE {
        return Some((mhz * 1_000_000, "VERIFLAT_TSC_MHZ"));
    }
    if __cpuid(0).eax >= 0x16 {
        let mhz = __cpuid(0x16).eax as u64;
        if mhz != 0 {
            return Some((mhz * 1_000_000, "CPUID 16H"));
        }
    }
    if __cpuid(0x4000_0000).eax >= 0x4000_0010 {
        let khz = __cpuid(0x4000_0010).eax as u64;
        if khz != 0 {
            return Some((khz * 1_000, "CPUID 4000_0010H"));
        }
    }
    brand_string_mhz().map(|mhz| (mhz * 1_000_000, "the CPUID brand string"))
}

/// The frequency in MHz that the CPUID brand string (leaves 8000_0002H..8000_0004H) ends with, as in
/// "Intel(R) Xeon(R) CPU E5-2630 v3 @ 2.40GHz".
fn brand_string_mhz() -> Option<u64> {
    use core::arch::x86_64::__cpuid;
    if __cpuid(0x8000_0000).eax < 0x8000_0004 {
        return None;
    }
    let mut brand = [0u8; 48];
    for (i, leaf) in (0x8000_0002u32..=0x8000_0004).enumerate() {
        let r = __cpuid(leaf);
        for (j, word) in [r.eax, r.ebx, r.ecx, r.edx].into_iter().enumerate() {
            brand[16 * i + 4 * j..16 * i + 4 * j + 4].copy_from_slice(&word.to_le_bytes());
        }
    }
    let end = brand.windows(3).position(|w| w == b"GHz")?;
    let start = brand[..end].iter().rposition(|c| !c.is_ascii_digit() && *c != b'.')? + 1;
    let (mut ghz, mut mhz, mut scale, mut fraction) = (0u64, 0u64, 1000u64, false);
    for &c in &brand[start..end] {
        if c == b'.' {
            fraction = true;
        } else if !fraction {
            ghz = ghz * 10 + (c - b'0') as u64;
        } else {
            scale /= 10;
            mhz += (c - b'0') as u64 * scale;
        }
    }
    let mhz = ghz * 1000 + mhz;
    (mhz != 0).then_some(mhz)
}

/// The TSC rate in Hz from `tsc_rate`; panics when no source gives one.
pub fn tsc_hz() -> u64 {
    let hz = TSC_HZ.load(Ordering::Relaxed);
    if hz != 0 {
        return hz;
    }
    let (hz, _) = tsc_rate().expect("the TSC rate is unknown: build dom0 with VERIFLAT_TSC_MHZ set");
    TSC_HZ.store(hz, Ordering::Relaxed);
    hz
}

pub fn sys_ns_loopsleep(ns: u64) {
    let target = rdtsc() + (ns as u128 * tsc_hz() as u128 / 1_000_000_000) as u64;
    while rdtsc() < target {
        core::hint::spin_loop();
    }
}

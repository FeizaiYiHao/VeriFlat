//! Turbo control and the effective frequency of CPU 0, for bare-metal benchmark runs.
//!
//! `turbo=off` makes every CPU that comes up set IA32_MISC_ENABLE bit 38 (Turbo Mode Disable) when CPUID.06H:EAX
//! bit 1 reports turbo, and read it back; CPU 0 logs how many CPUs have it set. Setting the bit clears CPUID.06H:EAX
//! bit 1, so on an Intel CPU outside a hypervisor a CPU without that bit has its MSR read to tell "firmware already
//! disabled turbo" from "no turbo". Under a hypervisor nothing is read or written unless CPUID reports turbo.
//!
//! When CPUID.06H:ECX bit 0 reports IA32_APERF/IA32_MPERF, CPU 0 reads them at the end of kernel init and again where
//! the RAM log is finalised (exit, panic, fatal exception or `reset_after=`), and logs TSC rate × ΔAPERF/ΔMPERF:
//! the average frequency of the time CPU 0 was not halted. No syscall path reads them.

use core::arch::x86_64::{__cpuid, __cpuid_count, _rdtsc};
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering::Relaxed};

use x86::msr::{rdmsr, wrmsr};

use crate::cpu::{self, MAX_CPUS};

const IA32_MISC_ENABLE: u32 = 0x1a0;
const IA32_MPERF: u32 = 0xe7;
const IA32_APERF: u32 = 0xe8;
const TURBO_MODE_DISABLE: u64 = 1 << 38;

/// Whether the command line has `turbo=off`.
pub static TURBO_OFF: AtomicBool = AtomicBool::new(false);

/// What `disable_turbo` found on each CPU (one of the `TURBO_*` values).
static TURBO_STATE: [AtomicU8; MAX_CPUS] = [const { AtomicU8::new(TURBO_NOT_RUN) }; MAX_CPUS];
const TURBO_NOT_RUN: u8 = 0;
/// This CPU set bit 38 and read it back set.
const TURBO_DISABLED: u8 = 1;
/// Bit 38 was already set (by firmware or by another CPU of the package).
const TURBO_ALREADY_DISABLED: u8 = 2;
/// CPUID reports no turbo and the MSR was not read (a hypervisor or a non-Intel CPU).
const TURBO_NOT_REPORTED: u8 = 3;
/// CPUID reports no turbo and bit 38 is clear: the CPU has no turbo.
const TURBO_ABSENT: u8 = 4;
/// This CPU wrote bit 38 but read it back clear.
const TURBO_WRITE_IGNORED: u8 = 5;

fn has_turbo() -> bool {
    __cpuid(0).eax >= 6 && __cpuid(6).eax & (1 << 1) != 0
}

fn has_aperf_mperf() -> bool {
    __cpuid(0).eax >= 6 && __cpuid(6).ecx & 1 != 0
}

/// An Intel CPU not running under a hypervisor (CPUID.01H:ECX bit 31 clear), where IA32_MISC_ENABLE exists.
fn intel_bare_metal() -> bool {
    let vendor = __cpuid_count(0, 0);
    let intel = vendor.ebx == u32::from_le_bytes(*b"Genu") && vendor.edx == u32::from_le_bytes(*b"ineI") && vendor.ecx == u32::from_le_bytes(*b"ntel");
    intel && __cpuid(1).ecx & (1 << 31) == 0
}

/// With `turbo=off`, sets IA32_MISC_ENABLE bit 38 on the current CPU and records what it reads back; called once by
/// every CPU that comes up, after the command line is parsed.
pub unsafe fn disable_turbo(cpu_id: usize) {
    if !TURBO_OFF.load(Relaxed) {
        return;
    }
    let state = if has_turbo() {
        let before = rdmsr(IA32_MISC_ENABLE);
        if before & TURBO_MODE_DISABLE != 0 {
            TURBO_ALREADY_DISABLED
        } else {
            wrmsr(IA32_MISC_ENABLE, before | TURBO_MODE_DISABLE);
            if rdmsr(IA32_MISC_ENABLE) & TURBO_MODE_DISABLE != 0 { TURBO_DISABLED } else { TURBO_WRITE_IGNORED }
        }
    } else if intel_bare_metal() {
        if rdmsr(IA32_MISC_ENABLE) & TURBO_MODE_DISABLE != 0 { TURBO_ALREADY_DISABLED } else { TURBO_ABSENT }
    } else {
        TURBO_NOT_REPORTED
    };
    TURBO_STATE[cpu_id].store(state, Relaxed);
}

/// With `turbo=off`, logs on how many of the present CPUs bit 38 is set, and warns for each CPU where it is not.
pub fn log_turbo() {
    if !TURBO_OFF.load(Relaxed) {
        return;
    }
    let present = cpu::present_cpus();
    let count = |s: u8| (0..present).filter(|&c| TURBO_STATE[c].load(Relaxed) == s).count();
    let (set, already) = (count(TURBO_DISABLED), count(TURBO_ALREADY_DISABLED));
    log::info!("turbo=off: IA32_MISC_ENABLE bit 38 set on {} of {} CPUs ({} set here, {} already set)", set + already, present, set, already);
    for c in 0..present {
        let why = match TURBO_STATE[c].load(Relaxed) {
            TURBO_DISABLED | TURBO_ALREADY_DISABLED => continue,
            TURBO_NOT_REPORTED => "CPUID.06H:EAX bit 1 reports no turbo under a hypervisor or non-Intel CPU; MSR not touched",
            TURBO_ABSENT => "CPUID.06H:EAX bit 1 reports no turbo and bit 38 is clear",
            TURBO_WRITE_IGNORED => "bit 38 reads back clear after the write",
            _ => "the CPU did not run the turbo setting",
        };
        log::warn!("turbo=off: CPU {}: bit 38 not set: {}", c, why);
    }
}

/// CPU 0's (TSC, APERF, MPERF) at the end of kernel init; TSC 0 when not taken.
static START: [AtomicU64; 3] = [const { AtomicU64::new(0) }; 3];

/// Takes CPU 0's first frequency sample at the end of kernel init.
pub unsafe fn start_frequency_interval() {
    if !has_aperf_mperf() {
        log::info!("effective frequency: CPUID.06H:ECX bit 0 reports no APERF/MPERF, not measured");
        return;
    }
    let (aperf, mperf) = (rdmsr(IA32_APERF), rdmsr(IA32_MPERF));
    START[1].store(aperf, Relaxed);
    START[2].store(mperf, Relaxed);
    START[0].store(_rdtsc(), Relaxed);
}

/// Logs CPU 0's effective frequency since `start_frequency_interval`; called where the RAM log is finalised.
pub unsafe fn log_frequency() {
    let tsc0 = START[0].load(Relaxed);
    if tsc0 == 0 {
        return;
    }
    let cpu_id = cpu::cpu_id_without_gs();
    if cpu_id != 0 {
        log::info!("effective frequency: finishing on CPU {}, CPU 0's APERF/MPERF are not readable here", cpu_id);
        return;
    }
    let (aperf, mperf, tsc) = (rdmsr(IA32_APERF), rdmsr(IA32_MPERF), _rdtsc());
    let da = aperf.wrapping_sub(START[1].load(Relaxed));
    let dm = mperf.wrapping_sub(START[2].load(Relaxed));
    let (hz, source) = crate::boot::tsc_hz();
    let busy_permille = (dm as u128 * 1000 / (tsc - tsc0).max(1) as u128) as u64;
    if dm == 0 {
        log::info!("effective frequency: CPU 0 MPERF did not advance (TSC {} MHz from {})", hz / 1_000_000, source);
        return;
    }
    let mhz = (hz as u128 * da as u128 / dm as u128 / 1_000_000) as u64;
    let ratio_milli = (da as u128 * 1000 / dm as u128) as u64;
    log::info!(
        "effective frequency: CPU 0 {} MHz = TSC {} MHz (from {}) x APERF/MPERF {}.{:03} ({} / {}), unhalted {}.{}% of {} TSC cycles",
        mhz, hz / 1_000_000, source, ratio_milli / 1000, ratio_milli % 1000, da, dm, busy_permille / 10, busy_permille % 10, tsc - tsc0,
    );
}

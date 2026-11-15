//! A polling, multi-queue driver core for the Intel Ethernet Controller E810 (Linux driver `ice`), written for
//! VeriFlat's dom0 and for a Linux user-space test program. The core does not touch hardware itself: every register
//! access, every DMA allocation and every delay goes through [`Platform`], which each front end implements (dom0:
//! BAR0 through the loader's window and heap pages mapped at IOVA = VA; Linux: `resource0` of sysfs and hugepages).
//!
//! What it does, in the order of [`Device::new`]: PF reset, control (admin) queue bring-up, firmware version, clear of
//! the PF configuration and of the PXE mode, function capabilities, switch configuration (logical port and switch
//! ID), Tx scheduler topology (default tree, removal of the firmware's default nodes, a branch of nodes for the
//! queues), MAC address, one PF VSI with N contiguous queue pairs, Tx queues added through the admin queue, Rx queue
//! contexts written through registers, RSS key and lookup table, switch rules that steer received frames, and link
//! bring-up. Queues are polled: no interrupt is ever enabled.
//!
//! The register offsets, admin queue command layouts, context bit layouts and descriptor formats are those of the
//! Intel Ethernet Controller E810 datasheet as the Linux `ice` driver headers encode them (read as a reference, not
//! copied); the datasheet itself was not at hand, so the module comments name its topics, not section numbers. No
//! hardware was available when this was written: `boot/bench/README.md` lists what is verified and what is not.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod aq;
pub mod bench;
pub mod chan;
pub mod ctx;
pub mod desc;
mod device;
pub mod maglev;
pub mod packet;
mod queue;
pub mod regs;
pub mod ring;
pub mod sched;
pub mod xfer;

#[cfg(any(test, feature = "mock"))]
pub mod mock;

pub use device::{Config, Device, DeviceInfo, LinkStatus, PortStats, RxSteering};
pub use queue::{RxFrame, RxQueue, TxQueue};

use core::fmt;

/// PCI vendor ID of Intel.
pub const INTEL_VENDOR: u16 = 0x8086;

/// PCI device IDs of the E810 family: E810-C backplane, QSFP, SFP; E810-XXV backplane, QSFP, SFP.
pub const E810_DEVICE_IDS: [u16; 6] = [0x1591, 0x1592, 0x1593, 0x1599, 0x159a, 0x159b];

/// Whether `vendor:device` is an E810 physical function.
pub fn is_e810(vendor: u16, device: u16) -> bool {
    vendor == INTEL_VENDOR && E810_DEVICE_IDS.contains(&device)
}

/// Whether `device` is an E810-C (100G) function, which a benchmark prefers over an E810-XXV (25G) one.
pub fn is_e810_c(device: u16) -> bool {
    matches!(device, 0x1591..=0x1593)
}

/// A zeroed DMA region: `va` for the CPU, `iova` for the device, contiguous in both.
#[derive(Clone, Copy, Debug)]
pub struct DmaRegion {
    pub va: *mut u8,
    pub iova: u64,
    pub len: usize,
}

// A region is plain memory that the driver hands from thread to thread together with the queue that owns it.
unsafe impl Send for DmaRegion {}
unsafe impl Sync for DmaRegion {}

impl DmaRegion {
    /// The region `[offset, offset + len)` of this one.
    pub fn slice(&self, offset: usize, len: usize) -> DmaRegion {
        assert!(offset + len <= self.len, "DMA sub-region out of bounds");
        DmaRegion { va: unsafe { self.va.add(offset) }, iova: self.iova + offset as u64, len }
    }
}

/// Everything the driver needs from its environment. Implementations must be usable from several threads at once:
/// each queue pair calls `read32`/`write32` on its own registers from its own CPU.
pub trait Platform: Sync {
    /// Reads the 32-bit register at byte offset `offset` of BAR0.
    fn read32(&self, offset: usize) -> u32;
    /// Writes the 32-bit register at byte offset `offset` of BAR0.
    fn write32(&self, offset: usize, value: u32);
    /// Allocates `len` zeroed bytes aligned to `align` (at most 4096) that the device can read and write at the
    /// returned IOVA, contiguous in VA and IOVA. Regions are never freed. The driver never asks for more than 2 MiB
    /// in one region.
    fn dma_alloc(&self, len: usize, align: usize) -> Option<DmaRegion>;
    /// `dma_alloc` for packet buffers (the Rx buffers), which a front end may place apart from the rings, for
    /// example in memory it shares with another process.
    fn dma_alloc_packets(&self, len: usize, align: usize) -> Option<DmaRegion> {
        self.dma_alloc(len, align)
    }
    /// Waits at least `us` microseconds.
    fn delay_us(&self, us: u64);
    /// A monotonic cycle counter (the TSC) for the benchmark loop.
    fn tsc(&self) -> u64;
}

/// Why an operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A wait ran out: the string says for what.
    Timeout(&'static str),
    /// The firmware completed admin queue command `opcode` with a nonzero return value.
    Aq { opcode: u16, retval: u16 },
    /// `Platform::dma_alloc` returned `None`.
    NoDmaMemory,
    /// The device or firmware answered something the driver cannot use.
    Device(&'static str),
    /// The configuration asks for more than the device offers.
    Config(&'static str),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Timeout(what) => write!(f, "timed out waiting for {}", what),
            Error::Aq { opcode, retval } => {
                write!(f, "admin queue command {:#06x} failed with {} ({})", opcode, retval, aq::retval_name(*retval))
            }
            Error::NoDmaMemory => write!(f, "out of DMA memory"),
            Error::Device(what) => write!(f, "device: {}", what),
            Error::Config(what) => write!(f, "configuration: {}", what),
        }
    }
}

pub type Result<T> = core::result::Result<T, Error>;

/// A MAC address formatted as `aa:bb:cc:dd:ee:ff`.
pub struct Mac(pub [u8; 6]);

impl fmt::Display for Mac {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let m = self.0;
        write!(f, "{:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}", m[0], m[1], m[2], m[3], m[4], m[5])
    }
}

/// Parses `aa:bb:cc:dd:ee:ff` (or with `-`).
pub fn parse_mac(s: &str) -> Option<[u8; 6]> {
    let mut mac = [0u8; 6];
    let mut parts = s.split(|c| c == ':' || c == '-');
    for byte in mac.iter_mut() {
        *byte = u8::from_str_radix(parts.next()?, 16).ok()?;
    }
    parts.next().is_none().then_some(mac)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mac_parse_and_format() {
        let mac = parse_mac("02:1b:21:a0:0f:ff").unwrap();
        assert_eq!(mac, [0x02, 0x1b, 0x21, 0xa0, 0x0f, 0xff]);
        assert_eq!(alloc::format!("{}", Mac(mac)), "02:1b:21:a0:0f:ff");
        assert!(parse_mac("02:1b:21:a0:0f").is_none());
        assert!(parse_mac("02:1b:21:a0:0f:ff:00").is_none());
        assert!(parse_mac("zz:1b:21:a0:0f:ff").is_none());
    }

    #[test]
    fn device_ids() {
        assert!(is_e810(0x8086, 0x1592));
        assert!(is_e810(0x8086, 0x159b));
        assert!(!is_e810(0x8086, 0x10fb));
        assert!(is_e810_c(0x1592) && !is_e810_c(0x159b));
    }
}

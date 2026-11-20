//! PCI configuration space access (legacy 0xCF8/0xCFC mechanism): the scan of every bus, root buses of several host
//! bridges and buses behind PCI-to-PCI bridges alike, that records the functions whose BAR0 dom0 drives, the DMA
//! test device, and the BAR slots: every assigned memory BAR of every function.

use astd::boot::{BarSlot, DmaTestDevice, PciDevice, MAX_BAR_SLOTS, MAX_PCI_DEVICES};
use astd::heapless::Vec as ArrayVec;
use x86::io::{inl, outl};

use crate::memory::PAGE_SIZE;

const CONFIG_ADDRESS: u16 = 0xCF8;
const CONFIG_DATA: u16 = 0xCFC;

/// QEMU's `edu` educational device.
const EDU_VENDOR: u16 = 0x1234;
const EDU_DEVICE: u16 = 0x11e8;

const VENDOR_DEVICE: u8 = 0x00;
const COMMAND: u8 = 0x04;
const CLASS_REVISION: u8 = 0x08;
const HEADER_TYPE: u8 = 0x0c;
const BAR0: u8 = 0x10;
/// Primary, secondary and subordinate bus numbers of a PCI-to-PCI bridge (header type 1).
const BRIDGE_BUSES: u8 = 0x18;
const COMMAND_MEMORY: u32 = 1 << 1;
const COMMAND_BUS_MASTER: u32 = 1 << 2;

const BAR_IO: u32 = 1;
const BAR_TYPE_MASK: u32 = 0b110;
const BAR_TYPE_64: u32 = 0b100;

/// Lowest address of the fixed platform MMIO (IOAPIC, HPET, VT-d, LAPIC, firmware flash): a relocated BAR stays below.
const PLATFORM_MMIO_BASE: u64 = 0xfec0_0000;
const FOUR_GIB: u64 = 1 << 32;

/// The most memory ranges (BARs and bridge windows) of bus 0 the relocation search avoids.
const MAX_BUSY_RANGES: usize = 128;

fn config_address(bus: u8, device: u8, function: u8, offset: u8) -> u32 {
    (1 << 31) | ((bus as u32) << 16) | ((device as u32) << 11) | ((function as u32) << 8) | (offset as u32 & 0xfc)
}

unsafe fn read(bus: u8, device: u8, function: u8, offset: u8) -> u32 {
    outl(CONFIG_ADDRESS, config_address(bus, device, function, offset));
    inl(CONFIG_DATA)
}

unsafe fn write(bus: u8, device: u8, function: u8, offset: u8, value: u32) {
    outl(CONFIG_ADDRESS, config_address(bus, device, function, offset));
    outl(CONFIG_DATA, value);
}

/// A memory BAR: its config offset, base, size in bytes, and whether it is 64-bit.
#[derive(Clone, Copy)]
struct MemoryBar {
    offset: u8,
    base: u64,
    size: u64,
    is_64: bool,
}

/// Sizes the memory BAR at `offset` with memory decoding off; `None` for an I/O or unimplemented BAR. A 64-bit BAR
/// in the last register of the header (`last`) has no upper half and panics.
unsafe fn memory_bar(bus: u8, device: u8, function: u8, offset: u8, last: u8) -> Option<MemoryBar> {
    let low = read(bus, device, function, offset);
    if low & BAR_IO != 0 {
        return None;
    }
    let is_64 = low & BAR_TYPE_MASK == BAR_TYPE_64;
    assert!(!is_64 || offset < last, "PCI {:02x}:{:02x}.{}: 64-bit BAR at {:#x} has no upper register", bus, device, function, offset);
    let assigned = low & !0xf != 0 || is_64 && read(bus, device, function, offset + 4) != 0;
    // Decoding goes off while the BAR holds all ones, unless the BAR is unassigned (as on host bridges).
    let command = read(bus, device, function, COMMAND) & 0xffff;
    if assigned {
        write(bus, device, function, COMMAND, command & !COMMAND_MEMORY);
    }
    write(bus, device, function, offset, 0xffff_ffff);
    let low_mask = read(bus, device, function, offset);
    write(bus, device, function, offset, low);
    let (high, high_mask) = if is_64 {
        let high = read(bus, device, function, offset + 4);
        write(bus, device, function, offset + 4, 0xffff_ffff);
        let high_mask = read(bus, device, function, offset + 4);
        write(bus, device, function, offset + 4, high);
        (high, high_mask)
    } else {
        (0, 0xffff_ffff)
    };
    if assigned {
        write(bus, device, function, COMMAND, command);
    }
    let mask = ((high_mask as u64) << 32) | (low_mask & !0xf) as u64;
    if low_mask & !0xf == 0 && (!is_64 || high_mask == 0) {
        return None;
    }
    let size = (!mask).wrapping_add(1);
    Some(MemoryBar { offset, base: ((high as u64) << 32) | (low & !0xf) as u64, size, is_64 })
}

/// The functions present on `bus` as `(device, function)`, multifunction devices included.
fn functions(bus: u8) -> impl Iterator<Item = (u8, u8)> {
    (0..32u8).flat_map(move |device| {
        let multi = unsafe { read(bus, device, 0, VENDOR_DEVICE) } & 0xffff != 0xffff
            && unsafe { read(bus, device, 0, HEADER_TYPE) } >> 16 & 0x80 != 0;
        (0..if multi { 8u8 } else { 1 }).map(move |function| (device, function))
    })
    .filter(move |&(device, function)| unsafe { read(bus, device, function, VENDOR_DEVICE) } & 0xffff != 0xffff)
}

/// The number of BAR registers of a function with header type `header_type`: 6 for a device, 2 for a bridge.
fn bar_count(header_type: u32) -> u8 {
    match header_type {
        0 => 6,
        1 => 2,
        _ => 0,
    }
}

/// The memory BARs of `(bus, device, function)` as `(index, bar)`, a 64-bit BAR once under its low register.
fn memory_bars(bus: u8, device: u8, function: u8) -> impl Iterator<Item = (u8, MemoryBar)> {
    let count = bar_count(unsafe { read(bus, device, function, HEADER_TYPE) } >> 16 & 0x7f);
    let mut index = 0;
    core::iter::from_fn(move || {
        while index < count {
            let (at, offset) = (index, BAR0 + 4 * index);
            let bar = unsafe { memory_bar(bus, device, function, offset, BAR0 + 4 * (count - 1)) };
            index += if bar.is_some_and(|b| b.is_64) { 2 } else { 1 };
            if let Some(bar) = bar {
                return Some((at, bar));
            }
        }
        None
    })
}

/// The memory ranges decoded on bus 0: every memory BAR below 4 GiB and every bridge memory window.
fn busy_ranges() -> ArrayVec<(u64, u64), MAX_BUSY_RANGES> {
    let mut ranges = ArrayVec::new();
    for (device, function) in functions(0) {
        let header_type = unsafe { read(0, device, function, HEADER_TYPE) } >> 16 & 0x7f;
        for (_, bar) in memory_bars(0, device, function) {
            if bar.base != 0 && bar.base < FOUR_GIB {
                ranges.push((bar.base, bar.size)).expect("too many PCI memory ranges");
            }
        }
        if header_type == 1 {
            // Memory and prefetchable memory windows: base/limit in 1 MiB units at 0x20 and 0x24.
            for offset in [0x20u8, 0x24] {
                let window = unsafe { read(0, device, function, offset) };
                let base = ((window & 0xfff0) as u64) << 16;
                let limit = (((window >> 16) & 0xfff0) as u64) << 16 | 0xf_ffff;
                if limit > base {
                    ranges.push((base, limit + 1 - base)).expect("too many PCI memory ranges");
                }
            }
        }
    }
    ranges
}

fn overlaps(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 < b.0 + b.1 && b.0 < a.0 + a.1
}

/// A free, `size`-aligned range of `size` bytes below the platform MMIO that no e820 region, MMCONFIG window or
/// bus 0 memory range uses.
fn free_bar_range(size: u64, e820: &[(u64, u64)], mmconfig: &[(u64, u64)], busy: &[(u64, u64)]) -> u64 {
    let ram_end = e820.iter().map(|r| r.0 + r.1).filter(|end| *end <= PLATFORM_MMIO_BASE).max().unwrap_or(0);
    let mut base = (ram_end + size - 1) & !(size - 1);
    while base + size <= PLATFORM_MMIO_BASE {
        let candidate = (base, size);
        if !e820.iter().chain(mmconfig).chain(busy).any(|r| overlaps(*r, candidate)) {
            return base;
        }
        base += size;
    }
    panic!("no free range below {:#x} for a {:#x}-byte BAR", PLATFORM_MMIO_BASE, size);
}

/// Whether dom0 drives this function through its BAR0 window: NVMe, Ethernet, and the `edu` test device.
fn recorded_kind(vendor: u16, device: u16, class: u8, subclass: u8) -> bool {
    (class, subclass) == (0x01, 0x08) || (class, subclass) == (0x02, 0x00) || (vendor, device) == (EDU_VENDOR, EDU_DEVICE)
}

/// Enables memory decoding and bus mastering of `(bus, device, function)`.
unsafe fn enable(bus: u8, device: u8, function: u8) {
    let command = read(bus, device, function, COMMAND) & 0xffff;
    write(bus, device, function, COMMAND, command | COMMAND_MEMORY | COMMAND_BUS_MASTER);
}

/// A PCI-to-PCI bridge as `(bus, device, function)` with the secondary and subordinate bus numbers it forwards.
type Bridge = ((u8, u8, u8), u8, u8);

/// The most PCI-to-PCI bridges the scan records to enable the bridges above a recorded function.
const MAX_BRIDGES: usize = 256;

/// Scans every bus 0..=255, since a server has several root buses that each sit under their own host bridge, and
/// records every NVMe, Ethernet and `edu` function with a memory BAR0: enables its memory decoding and bus mastering
/// and those of every bridge whose bus range contains its bus. An assigned BAR0 stays where the firmware put it, below
/// or above 4 GiB; an unassigned BAR0 of a bus 0 function goes to a free range below the platform MMIO, and one off
/// bus 0 is skipped with a warning, since a bridge window bounds it. `e820` are the firmware memory map's ranges below
/// 4 GiB, `mmconfig` the ECAM windows.
pub fn probe_devices(e820: &[(u64, u64)], mmconfig: &[(u64, u64)]) -> ArrayVec<PciDevice, MAX_PCI_DEVICES> {
    let mut busy = busy_ranges();
    let mut devices = ArrayVec::new();
    // The bridges come first, so that the bridges above a function are known whatever bus order the firmware chose.
    let mut bridges: ArrayVec<Bridge, MAX_BRIDGES> = ArrayVec::new();
    let mut function_count = 0usize;
    let mut bus_count = 0usize;
    for bus in 0..=255u8 {
        let mut any = false;
        for (dev, fun) in functions(bus) {
            any = true;
            function_count += 1;
            if unsafe { read(bus, dev, fun, HEADER_TYPE) } >> 16 & 0x7f != 1 {
                continue;
            }
            let buses = unsafe { read(bus, dev, fun, BRIDGE_BUSES) };
            let (secondary, subordinate) = ((buses >> 8) as u8, (buses >> 16) as u8);
            if secondary == 0 || subordinate < secondary {
                log::info!("PCI {:02x}:{:02x}.{} bridge without assigned buses", bus, dev, fun);
                continue;
            }
            log::info!("PCI {:02x}:{:02x}.{} bridges to buses {:02x}..={:02x}", bus, dev, fun, secondary, subordinate);
            if bridges.push(((bus, dev, fun), secondary, subordinate)).is_err() {
                log::warn!("PCI {:02x}:{:02x}.{} bridge not recorded: more than {} bridges", bus, dev, fun, MAX_BRIDGES);
            }
        }
        bus_count += any as usize;
    }
    log::info!("PCI scan: {} functions on {} buses, {} bridges", function_count, bus_count, bridges.len());
    for bus in 0..=255u8 {
        for (dev, fun) in functions(bus) {
            let id = unsafe { read(bus, dev, fun, VENDOR_DEVICE) };
            let (vendor, device) = (id as u16, (id >> 16) as u16);
            let class_rev = unsafe { read(bus, dev, fun, CLASS_REVISION) };
            let (class, subclass) = ((class_rev >> 24) as u8, (class_rev >> 16) as u8);
            let header_type = unsafe { read(bus, dev, fun, HEADER_TYPE) } >> 16 & 0x7f;
            // The loader logs only the functions it may record and the bridges, which keeps a big server's log short.
            if header_type != 0 || !recorded_kind(vendor, device, class, subclass) {
                continue;
            }
            log::info!("PCI {:02x}:{:02x}.{} {:04x}:{:04x} class {:02x}:{:02x}", bus, dev, fun, vendor, device, class, subclass);
            if devices.is_full() {
                log::warn!("PCI {:02x}:{:02x}.{} not recorded: more than {} PCI functions with a device BAR0", bus, dev, fun, MAX_PCI_DEVICES);
                continue;
            }
            let Some(mut bar) = (unsafe { memory_bar(bus, dev, fun, BAR0, BAR0 + 20) }) else { continue };
            let size = bar.size.max(PAGE_SIZE as u64);
            if bar.base == 0 {
                if bus != 0 {
                    log::warn!("PCI {:02x}:{:02x}.{} not recorded: its BAR0 is unassigned behind a bridge", bus, dev, fun);
                    continue;
                }
                let base = free_bar_range(size, e820, mmconfig, &busy);
                log::info!("PCI 00:{:02x}.{} BAR0 relocated {:#x} -> {:#x} ({:#x} bytes)", dev, fun, bar.base, base, size);
                unsafe {
                    let command = read(0, dev, fun, COMMAND) & 0xffff;
                    write(0, dev, fun, COMMAND, command & !COMMAND_MEMORY);
                    let low = read(0, dev, fun, bar.offset) & 0xf;
                    write(0, dev, fun, bar.offset, base as u32 | low);
                    if bar.is_64 {
                        write(0, dev, fun, bar.offset + 4, 0);
                    }
                    write(0, dev, fun, COMMAND, command);
                }
                bar.base = base;
                busy.push((base, size)).expect("too many PCI memory ranges");
            }
            let pages = ((bar.base + bar.size + PAGE_SIZE as u64 - 1) & !(PAGE_SIZE as u64 - 1)) / PAGE_SIZE as u64
                - bar.base / PAGE_SIZE as u64;
            unsafe { enable(bus, dev, fun) };
            // Every bridge that forwards this bus lies above the function; a function on a root bus has none.
            for &((b, d, f), secondary, subordinate) in bridges.iter() {
                if secondary <= bus && bus <= subordinate {
                    unsafe { enable(b, d, f) };
                }
            }
            let bdf = ((bus as u16) << 8) | ((dev as u16) << 3) | fun as u16;
            log::info!("PCI {:02x}:{:02x}.{} recorded: BAR0 {:#x}, {} pages", bus, dev, fun, bar.base, pages);
            devices.push(PciDevice { bdf, vendor, device, class, subclass, bar0_base: bar.base, bar0_pages: pages }).unwrap();
        }
    }
    devices
}

/// The recorded `edu` device, if any. Test-only: the kernel uses it to issue DMA through the IOMMU.
pub fn dma_test_device(devices: &[PciDevice]) -> Option<DmaTestDevice> {
    let edu = devices.iter().find(|d| (d.vendor, d.device) == (EDU_VENDOR, EDU_DEVICE))?;
    log::info!("DMA test device {:02x}:{:02x}.{} BAR0 {:#x}", edu.bdf >> 8, (edu.bdf >> 3) & 0x1f, edu.bdf & 7, edu.bar0_base);
    Some(DmaTestDevice { bdf: edu.bdf, mmio: edu.bar0_base })
}

/// The BAR slots: every assigned memory BAR (nonzero base) of every function on every bus, devices (6 registers) and
/// bridges (2) alike, with its exact byte range, in B/D/F and BAR order. Call it after `probe_devices`, which may
/// assign a BAR0. Panics on more than `MAX_BAR_SLOTS` rather than leave a BAR out.
pub fn bar_slots() -> ArrayVec<BarSlot, MAX_BAR_SLOTS> {
    let mut slots = ArrayVec::new();
    for bus in 0..=255u8 {
        for (dev, fun) in functions(bus) {
            let id = unsafe { read(bus, dev, fun, VENDOR_DEVICE) };
            let bdf = ((bus as u16) << 8) | ((dev as u16) << 3) | fun as u16;
            for (index, bar) in memory_bars(bus, dev, fun).filter(|(_, bar)| bar.base != 0) {
                log::info!(
                    "PCI {:02x}:{:02x}.{} BAR{}: {:#x}..{:#x} ({}-bit)",
                    bus, dev, fun, index, bar.base, bar.base.wrapping_add(bar.size), if bar.is_64 { 64 } else { 32 }
                );
                let slot = BarSlot { bdf, bar: index, vendor: id as u16, device: (id >> 16) as u16, base: bar.base, size: bar.size };
                slots.push(slot).expect("more assigned memory BARs than MAX_BAR_SLOTS");
            }
        }
    }
    log::info!("PCI BAR slots: {}", slots.len());
    slots
}

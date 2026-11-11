//! PCI configuration space access (legacy 0xCF8/0xCFC mechanism): the bus 0 scan that records the
//! functions whose BAR0 dom0 drives, and the DMA test device.

use astd::boot::{DmaTestDevice, PciDevice, MAX_PCI_DEVICES};
use astd::heapless::Vec as ArrayVec;
use x86::io::{inl, outl};
use x86::msr::rdmsr;

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
const COMMAND_MEMORY: u32 = 1 << 1;
const COMMAND_BUS_MASTER: u32 = 1 << 2;

const BAR_IO: u32 = 1;
const BAR_TYPE_MASK: u32 = 0b110;
const BAR_TYPE_64: u32 = 0b100;

/// Lowest address of the fixed platform MMIO (IOAPIC, HPET, VT-d, LAPIC, firmware flash): a relocated BAR stays below.
const PLATFORM_MMIO_BASE: u64 = 0xfec0_0000;
const FOUR_GIB: u64 = 1 << 32;

const IA32_MTRRCAP: u32 = 0xfe;
const IA32_MTRR_DEF_TYPE: u32 = 0x2ff;
const IA32_MTRR_PHYSBASE0: u32 = 0x200;
const MTRR_ENABLE: u64 = 1 << 11;
const MTRR_VALID: u64 = 1 << 11;
const MTRR_TYPE_UC: u64 = 0;
const MTRR_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;

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

/// Sizes the memory BAR at `offset` with memory decoding off; `None` for an I/O or unimplemented BAR.
unsafe fn memory_bar(device: u8, function: u8, offset: u8) -> Option<MemoryBar> {
    let low = read(0, device, function, offset);
    if low & BAR_IO != 0 {
        return None;
    }
    let is_64 = low & BAR_TYPE_MASK == BAR_TYPE_64;
    // Decoding goes off while the BAR holds all ones, unless the BAR is unassigned (as on host bridges).
    let command = read(0, device, function, COMMAND) & 0xffff;
    if low & !0xf != 0 {
        write(0, device, function, COMMAND, command & !COMMAND_MEMORY);
    }
    write(0, device, function, offset, 0xffff_ffff);
    let low_mask = read(0, device, function, offset);
    write(0, device, function, offset, low);
    let (high, high_mask) = if is_64 {
        let high = read(0, device, function, offset + 4);
        write(0, device, function, offset + 4, 0xffff_ffff);
        let high_mask = read(0, device, function, offset + 4);
        write(0, device, function, offset + 4, high);
        (high, high_mask)
    } else {
        (0, 0xffff_ffff)
    };
    if low & !0xf != 0 {
        write(0, device, function, COMMAND, command);
    }
    let mask = ((high_mask as u64) << 32) | (low_mask & !0xf) as u64;
    if low_mask & !0xf == 0 && (!is_64 || high_mask == 0) {
        return None;
    }
    let size = (!mask).wrapping_add(1);
    Some(MemoryBar { offset, base: ((high as u64) << 32) | (low & !0xf) as u64, size, is_64 })
}

/// The functions present on bus 0 as `(device, function)`, multifunction devices included.
fn functions() -> impl Iterator<Item = (u8, u8)> {
    (0..32u8).flat_map(|device| {
        let multi = unsafe { read(0, device, 0, VENDOR_DEVICE) } & 0xffff != 0xffff
            && unsafe { read(0, device, 0, HEADER_TYPE) } >> 16 & 0x80 != 0;
        (0..if multi { 8u8 } else { 1 }).map(move |function| (device, function))
    })
    .filter(|&(device, function)| unsafe { read(0, device, function, VENDOR_DEVICE) } & 0xffff != 0xffff)
}

/// The memory ranges decoded on bus 0: every memory BAR below 4 GiB and every bridge memory window.
fn busy_ranges() -> ArrayVec<(u64, u64), MAX_BUSY_RANGES> {
    let mut ranges = ArrayVec::new();
    for (device, function) in functions() {
        let header_type = unsafe { read(0, device, function, HEADER_TYPE) } >> 16 & 0x7f;
        let bar_count = match header_type {
            0 => 6,
            1 => 2,
            _ => 0,
        };
        let mut index = 0;
        while index < bar_count {
            let offset = BAR0 + 4 * index;
            match unsafe { memory_bar(device, function, offset) } {
                Some(bar) => {
                    if bar.base != 0 && bar.base < FOUR_GIB {
                        ranges.push((bar.base, bar.size)).expect("too many PCI memory ranges");
                    }
                    index += if bar.is_64 { 2 } else { 1 };
                }
                None => index += 1,
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

/// The memory type the MTRRs give physical page `page`: `None` when they are disabled (UC).
fn mtrr_type(page: u64) -> Option<u64> {
    let def_type = unsafe { rdmsr(IA32_MTRR_DEF_TYPE) };
    if def_type & MTRR_ENABLE == 0 {
        return None;
    }
    let count = unsafe { rdmsr(IA32_MTRRCAP) } & 0xff;
    let mut matched: Option<u64> = None;
    for n in 0..count as u32 {
        let base = unsafe { rdmsr(IA32_MTRR_PHYSBASE0 + 2 * n) };
        let mask = unsafe { rdmsr(IA32_MTRR_PHYSBASE0 + 2 * n + 1) };
        if mask & MTRR_VALID == 0 || page & mask & MTRR_ADDR_MASK != base & mask & MTRR_ADDR_MASK {
            continue;
        }
        let ty = base & 0xff;
        // UC wins over every other type; WT wins over WB; other overlaps are undefined, so keep the first.
        matched = Some(match matched {
            None => ty,
            Some(m) if m == MTRR_TYPE_UC || ty == MTRR_TYPE_UC => MTRR_TYPE_UC,
            Some(m) => m.min(ty),
        });
    }
    Some(matched.unwrap_or(def_type & 0xff))
}

/// Panics unless every page of `[base, base + pages * 4K)` is uncacheable under the MTRRs.
fn check_uncacheable(bdf: (u8, u8), base: u64, pages: u64) {
    for page in 0..pages {
        let addr = base + page * PAGE_SIZE as u64;
        if let Some(ty) = mtrr_type(addr) {
            assert!(
                ty == MTRR_TYPE_UC,
                "MTRRs give BAR0 page {:#x} of 00:{:02x}.{} memory type {}, not UC: dom0's BAR0 window has no PCD bit",
                addr, bdf.0, bdf.1, ty
            );
        }
    }
}

/// Whether dom0 drives this function through its BAR0 window: NVMe, Ethernet, and the `edu` test device.
fn recorded_kind(vendor: u16, device: u16, class: u8, subclass: u8) -> bool {
    (class, subclass) == (0x01, 0x08) || (class, subclass) == (0x02, 0x00) || (vendor, device) == (EDU_VENDOR, EDU_DEVICE)
}

/// Scans bus 0 and records every NVMe, Ethernet and `edu` function with a memory BAR0: enables its memory
/// decoding and bus mastering, moves a BAR0 at or above 4 GiB to a free range below, and checks that the MTRRs
/// make BAR0 uncacheable. `e820` are the firmware memory map's ranges below 4 GiB, `mmconfig` the ECAM windows.
pub fn probe_devices(e820: &[(u64, u64)], mmconfig: &[(u64, u64)]) -> ArrayVec<PciDevice, MAX_PCI_DEVICES> {
    let def_type = unsafe { rdmsr(IA32_MTRR_DEF_TYPE) };
    log::info!(
        "MTRRs {} (default type {}, {} variable ranges)",
        if def_type & MTRR_ENABLE != 0 { "enabled" } else { "disabled" },
        def_type & 0xff,
        unsafe { rdmsr(IA32_MTRRCAP) } & 0xff,
    );
    let mut busy = busy_ranges();
    let mut devices = ArrayVec::new();
    for (dev, fun) in functions() {
        let id = unsafe { read(0, dev, fun, VENDOR_DEVICE) };
        let (vendor, device) = (id as u16, (id >> 16) as u16);
        let class_rev = unsafe { read(0, dev, fun, CLASS_REVISION) };
        let (class, subclass) = ((class_rev >> 24) as u8, (class_rev >> 16) as u8);
        let header_type = unsafe { read(0, dev, fun, HEADER_TYPE) } >> 16 & 0x7f;
        log::info!("PCI 00:{:02x}.{} {:04x}:{:04x} class {:02x}:{:02x}", dev, fun, vendor, device, class, subclass);
        if header_type != 0 || !recorded_kind(vendor, device, class, subclass) {
            continue;
        }
        let Some(mut bar) = (unsafe { memory_bar(dev, fun, BAR0) }) else { continue };
        assert!(bar.size >= PAGE_SIZE as u64 || bar.base % PAGE_SIZE as u64 == 0, "BAR0 of 00:{:02x}.{} is not page aligned", dev, fun);
        let size = bar.size.max(PAGE_SIZE as u64);
        if bar.base == 0 || bar.base + size > FOUR_GIB {
            assert!(bar.is_64 || bar.base == 0, "32-bit BAR0 above 4 GiB");
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
        let pages = size / PAGE_SIZE as u64;
        check_uncacheable((dev, fun), bar.base, pages);
        unsafe {
            let command = read(0, dev, fun, COMMAND) & 0xffff;
            write(0, dev, fun, COMMAND, command | COMMAND_MEMORY | COMMAND_BUS_MASTER);
        }
        let bdf = ((dev as u16) << 3) | fun as u16;
        log::info!("PCI 00:{:02x}.{} recorded: BAR0 {:#x}, {} pages, MTRR type UC", dev, fun, bar.base, pages);
        if devices.push(PciDevice { bdf, vendor, device, class, subclass, bar0_base: bar.base, bar0_pages: pages }).is_err() {
            panic!("more than {} PCI functions with a device BAR0", MAX_PCI_DEVICES);
        }
    }
    devices
}

/// The recorded `edu` device, if any. Test-only: the kernel uses it to issue DMA through the IOMMU.
pub fn dma_test_device(devices: &[PciDevice]) -> Option<DmaTestDevice> {
    let edu = devices.iter().find(|d| (d.vendor, d.device) == (EDU_VENDOR, EDU_DEVICE))?;
    log::info!("DMA test device 00:{:02x}.{} BAR0 {:#x}", edu.bdf >> 3, edu.bdf & 7, edu.bar0_base);
    Some(DmaTestDevice { bdf: edu.bdf, mmio: edu.bar0_base })
}

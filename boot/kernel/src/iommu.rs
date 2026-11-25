//! VT-d DMA remapping over the verified kernel's root table.
//!
//! The verified kernel owns the root table: `KernelK.irt` holds a legacy-mode VT-d image pinned
//! one 4K page past the root-table lock cell, and its syscalls only write entries. This module
//! points every remapping unit at that one image (entries are indexed by B/D/F, so the units
//! share it), enables translation, and implements the IOTLB hook. It also enables interrupt
//! remapping on every unit with an empty table and compatibility-format requests blocked, so no
//! device can raise an interrupt: nothing in VeriFlat takes device interrupts. The model relies on
//! hardware properties that `init` checks:
//!
//! - CAP.CM = 0: not-present entries are never cached, so `pci_attach_dma` needs no invalidation;
//!   the model encodes this by caching only roots.
//! - CAP.RWBF = 0: table stores need no write-buffer flush before the unit can see them.
//! - CAP.ND >= 6: 16-bit domain IDs, the model's `VtdDomainId` range.
//! - CAP.SAGAW bit 2: 4-level second-level tables, the address width the model writes.
//! - CAP.DRD (bit 55) and CAP.DWD (bit 54): every IOTLB invalidation drains the domain's pending
//!   DMA reads and writes, so no DMA through a dropped translation completes after it.
//!
//! Table walks of a unit with ECAP.C = 0 do not snoop CPU caches. When some unit reports C = 0,
//! `veriflat_iommu_flush_to_memory` writes back (clflush, then mfence) every store the verified
//! kernel makes into a structure a unit reads: each IOMMU table word, each zeroed new IOMMU table
//! page and each context entry; `init` writes back the whole root and context table, which the
//! kernel built with ordinary stores, and the interrupt remapping table, before any unit is enabled.

use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, AtomicUsize, Ordering};

use astd::boot::MAX_IOMMU_UNITS;

use crate::boot;

/// Register bases of the remapping units, valid up to `UNIT_COUNT`; 0 while translation is off.
static UNITS: [AtomicU64; MAX_IOMMU_UNITS] = [const { AtomicU64::new(0) }; MAX_IOMMU_UNITS];
static UNIT_COUNT: AtomicUsize = AtomicUsize::new(0);
/// Serializes the invalidation registers: a domain-selective context-cache and IOTLB invalidation
/// runs under the verified root-table lock, but an IOTLB-only domain invalidation runs under one
/// IOMMU table's lock, so invalidations of different domains may race on a unit.
static INVALIDATION_LOCK: AtomicBool = AtomicBool::new(false);
/// Whether stores into remapping structures must be written back to memory: `FLUSH_UNKNOWN` until
/// the first `flush_needed` reads every unit's ECAP. That can happen before `init`, because the
/// kernel zeroes the root process's IOMMU root page while it builds itself.
static FLUSH_MODE: AtomicU8 = AtomicU8::new(FLUSH_UNKNOWN);
const FLUSH_UNKNOWN: u8 = 0;
const FLUSH_OFF: u8 = 1;
const FLUSH_ON: u8 = 2;
const CACHE_LINE: usize = 64;
/// One 4 KiB root table and one 4 KiB context table per bus.
const ROOT_AND_CONTEXT_TABLE_SIZE: usize = REGISTER_PAGE * (1 + 256);

/// The interrupt remapping table every unit uses: 256 entries, all not present, never written.
#[repr(C, align(4096))]
struct InterruptRemappingTable([u8; REGISTER_PAGE]);
static IRT: InterruptRemappingTable = InterruptRemappingTable([0; REGISTER_PAGE]);
/// IRTA.S: the table holds 2^(S+1) entries of 16 bytes.
const IRTA_SIZE_256: u64 = 7;

const CAP_REG: usize = 0x08;
const ECAP_REG: usize = 0x10;
const GCMD_REG: usize = 0x18;
const GSTS_REG: usize = 0x1c;
const RTADDR_REG: usize = 0x20;
const CCMD_REG: usize = 0x28;
const FSTS_REG: usize = 0x34;
const IRTA_REG: usize = 0xb8;

const CAP_RWBF: u64 = 1 << 4;
const CAP_CM: u64 = 1 << 7;
const CAP_SAGAW_4_LEVEL: u64 = 1 << 10;
const CAP_DWD: u64 = 1 << 54;
const CAP_DRD: u64 = 1 << 55;
const CAP_ND_16_BIT: u64 = 6;
const ECAP_C: u64 = 1 << 0;
const ECAP_IR: u64 = 1 << 3;

/// TE, SRTP, IRE, SIRTP: GSTS reports them as TES, RTPS, IRES, IRTPS at the same positions.
const GCMD_TE: u32 = 1 << 31;
const GCMD_SRTP: u32 = 1 << 30;
const GCMD_IRE: u32 = 1 << 25;
const GCMD_SIRTP: u32 = 1 << 24;
/// GSTS bits whose GCMD counterparts are one-shot commands; a GCMD write must not repeat them.
const GSTS_ONE_SHOT: u32 = (1 << 30) | (1 << 29) | (1 << 27) | (1 << 24);

const CCMD_ICC: u64 = 1 << 63;
const CCMD_GLOBAL: u64 = 1 << 61;
const CCMD_DOMAIN: u64 = 2 << 61;
/// CCMD.CAIG (bits 60:59): the granularity the unit actually performed.
const CCMD_CAIG_SHIFT: u32 = 59;
const CCMD_CAIG_GLOBAL: u64 = 1;
const CCMD_CAIG_DOMAIN: u64 = 2;

const IOTLB_IVT: u64 = 1 << 63;
const IOTLB_GLOBAL: u64 = 1 << 60;
const IOTLB_DOMAIN: u64 = 2 << 60;
/// IOTLB.IAIG (bits 58:57): the granularity the unit actually performed.
const IOTLB_IAIG_SHIFT: u32 = 57;
const IOTLB_IAIG_GLOBAL: u64 = 1;
const IOTLB_IAIG_DOMAIN: u64 = 2;
const IOTLB_DR: u64 = 1 << 49;
const IOTLB_DW: u64 = 1 << 48;

const FSTS_PFO: u32 = 1 << 0;
const FSTS_PPF: u32 = 1 << 1;
const FRCD_F: u64 = 1 << 63;

const REGISTER_PAGE: usize = 4096;
/// Domain IDs are 16 bits (CAP.ND >= 6).
const DOMAIN_COUNT: usize = 1 << 16;
/// RTADDR.RTA: a 4 KiB-aligned root table below the model's 48-bit `MEM_MASK`; TTM (bits 11:10)
/// stays 00, legacy mode.
const RTADDR_RTA_MASK: u64 = 0x0000_ffff_ffff_f000;

fn read32(base: u64, offset: usize) -> u32 {
    unsafe { ptr::read_volatile((base as usize + offset) as *const u32) }
}

fn write32(base: u64, offset: usize, value: u32) {
    unsafe { ptr::write_volatile((base as usize + offset) as *mut u32, value) }
}

fn read64(base: u64, offset: usize) -> u64 {
    unsafe { ptr::read_volatile((base as usize + offset) as *const u64) }
}

fn write64(base: u64, offset: usize, value: u64) {
    unsafe { ptr::write_volatile((base as usize + offset) as *mut u64, value) }
}

/// Offset of the IOTLB invalidate register (ECAP.IRO counts 16-byte units; IVA precedes it).
fn iotlb_reg(base: u64) -> usize {
    16 * ((read64(base, ECAP_REG) >> 8) & 0x3ff) as usize + 8
}

/// Offset of the first fault-recording register and the number of them.
fn fault_records(base: u64) -> (usize, usize) {
    let cap = read64(base, CAP_REG);
    (16 * ((cap >> 24) & 0x3ff) as usize, ((cap >> 40) & 0xff) as usize + 1)
}

/// Issues a persistent GCMD command (TE, IRE) or a one-shot one (SRTP, SIRTP) and waits until GSTS
/// reports it. CFI is never set, so with IRE on, compatibility-format interrupt requests are blocked.
fn global_command(base: u64, command: u32) {
    write32(base, GCMD_REG, (read32(base, GSTS_REG) & !GSTS_ONE_SHOT) | command);
    while read32(base, GSTS_REG) & command == 0 {
        core::hint::spin_loop();
    }
}

/// Whether the actual granularity `actual` covers the requested `global` or domain invalidation:
/// a domain request accepts domain or the coarser global granularity; a global one needs global.
fn granularity_covers(global: bool, actual: u64, actual_global: u64, actual_domain: u64) -> bool {
    actual == actual_global || (!global && actual == actual_domain)
}

fn invalidate_context_cache(base: u64, command: u64) {
    write64(base, CCMD_REG, CCMD_ICC | command);
    let mut ccmd = read64(base, CCMD_REG);
    while ccmd & CCMD_ICC != 0 {
        core::hint::spin_loop();
        ccmd = read64(base, CCMD_REG);
    }
    let caig = (ccmd >> CCMD_CAIG_SHIFT) & 0x3;
    assert!(granularity_covers(command == CCMD_GLOBAL, caig, CCMD_CAIG_GLOBAL, CCMD_CAIG_DOMAIN), "VT-d context invalidation {:#x} performed at granularity {}", command, caig);
}

/// Every IOTLB invalidation drains the pending DMA reads and writes of the domain (IOTLB.DR, DW),
/// so no DMA that used a dropped translation completes after the invalidation returns; `init_unit`
/// requires CAP.DRD and CAP.DWD on every unit.
fn invalidate_iotlb(base: u64, command: u64) {
    let reg = iotlb_reg(base);
    write64(base, reg, IOTLB_IVT | IOTLB_DR | IOTLB_DW | command);
    let mut iotlb = read64(base, reg);
    while iotlb & IOTLB_IVT != 0 {
        core::hint::spin_loop();
        iotlb = read64(base, reg);
    }
    let iaig = (iotlb >> IOTLB_IAIG_SHIFT) & 0x3;
    assert!(granularity_covers(command == IOTLB_GLOBAL, iaig, IOTLB_IAIG_GLOBAL, IOTLB_IAIG_DOMAIN), "VT-d IOTLB invalidation {:#x} performed at granularity {}", command, iaig);
}

/// The 16-bit domain ID of a hook argument; a wider value is a kernel bug, never masked.
fn domain_id(did: usize) -> u64 {
    assert!(did < DOMAIN_COUNT, "VT-d domain ID {:#x} out of range", did);
    did as u64
}

/// Whether some remapping unit has ECAP.C = 0; decided once from the hardware. Before the first
/// flush it checks CPUID.01H:EDX[19] (CLFSH).
fn flush_needed() -> bool {
    match FLUSH_MODE.load(Ordering::Acquire) {
        FLUSH_OFF => false,
        FLUSH_ON => true,
        _ => {
            let needed = boot::get_boot_info().iommu_units.iter().any(|&base| read64(base, ECAP_REG) & ECAP_C == 0);
            if needed {
                assert!(core::arch::x86_64::__cpuid(1).edx & (1 << 19) != 0, "VT-d table walks do not snoop CPU caches and the CPU has no CLFLUSH");
            }
            FLUSH_MODE.store(if needed { FLUSH_ON } else { FLUSH_OFF }, Ordering::Release);
            needed
        }
    }
}

/// Writes every cache line overlapping [addr, addr + len) back to memory and waits for it, when
/// some unit does not snoop CPU caches; otherwise returns at once. The verified kernel calls it
/// after each store into an IOMMU table page or a context entry and after zeroing a new IOMMU
/// table page, before the store can matter to a unit.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_iommu_flush_to_memory(addr: usize, len: usize) {
    if len == 0 || !flush_needed() {
        return;
    }
    let mut line = addr & !(CACHE_LINE - 1);
    while line < addr + len {
        unsafe { core::arch::x86_64::_mm_clflush(line as *const u8) };
        line += CACHE_LINE;
    }
    unsafe { core::arch::x86_64::_mm_mfence() };
}

/// Points every remapping unit at the verified root table at `root_table` and enables translation
/// and interrupt remapping. From here on a function's DMA faults until `pci_attach_dma` gives it a
/// context entry, and its interrupt requests are always dropped. Runs on CPU 0 before the other
/// CPUs start.
pub fn init(root_table: u64) {
    let units = &boot::get_boot_info().iommu_units;
    assert!(!units.is_empty(), "no VT-d remapping unit: VeriFlat needs DMA remapping");
    if flush_needed() {
        // The kernel built the root and context table with ordinary stores.
        veriflat_iommu_flush_to_memory(root_table as usize, ROOT_AND_CONTEXT_TABLE_SIZE);
        veriflat_iommu_flush_to_memory((&raw const IRT) as usize, REGISTER_PAGE);
        log::info!("VT-d table walks do not snoop CPU caches on some unit: remapping-structure stores are flushed to memory");
    } else {
        log::info!("VT-d table walks snoop CPU caches on every unit: no remapping-structure flush");
    }
    for (i, &base) in units.iter().enumerate() {
        init_unit(base, root_table);
        UNITS[i].store(base, Ordering::Release);
    }
    UNIT_COUNT.store(units.len(), Ordering::Release);
    log::info!("VT-d translation enabled on {} unit(s), root table {:#x}", units.len(), root_table);
}

fn init_unit(base: u64, root_table: u64) {
    let cap = read64(base, CAP_REG);
    let ecap = read64(base, ECAP_REG);
    log::info!("VT-d at {:#x}: CAP {:#x} ECAP {:#x}", base, cap, ecap);
    assert!(cap & CAP_CM == 0, "VT-d caching mode: attach would need an invalidation the model does not issue");
    assert!(cap & CAP_RWBF == 0, "VT-d requires write-buffer flushing, which the model does not issue");
    assert!(cap & 0x7 >= CAP_ND_16_BIT, "VT-d supports fewer than 2^16 domain IDs");
    assert!(cap & CAP_SAGAW_4_LEVEL != 0, "VT-d does not support 4-level tables");
    assert!(cap & CAP_DRD != 0 && cap & CAP_DWD != 0, "VT-d at {:#x}: CAP {:#x} lacks DMA read or write draining (CAP.DRD, CAP.DWD), which every IOTLB invalidation needs", base, cap);
    let (records, count) = fault_records(base);
    assert!(iotlb_reg(base) + 8 <= REGISTER_PAGE && records + 16 * count <= REGISTER_PAGE, "VT-d registers beyond the mapped page");
    assert!(read32(base, GSTS_REG) & (GCMD_TE | GCMD_IRE) == 0, "VT-d translation or interrupt remapping already enabled");
    assert!(ecap & ECAP_IR != 0, "VT-d does not support interrupt remapping");

    assert!(root_table & !RTADDR_RTA_MASK == 0, "VT-d root table {:#x} is not a 4 KiB-aligned 48-bit address", root_table);

    // TTM = 00: legacy-mode root table. After SRTP, invalidate the context cache, then the IOTLB.
    write64(base, RTADDR_REG, root_table);
    global_command(base, GCMD_SRTP);
    invalidate_context_cache(base, CCMD_GLOBAL);
    invalidate_iotlb(base, IOTLB_GLOBAL);
    global_command(base, GCMD_TE);

    // xAPIC destinations (EIME = 0). The unit has never remapped interrupts since reset (IRES was
    // 0), so its interrupt entry cache is empty and the table, which is never written, needs no
    // invalidation: no invalidation queue is set up.
    write64(base, IRTA_REG, (&raw const IRT) as u64 | IRTA_SIZE_256);
    global_command(base, GCMD_SIRTP);
    global_command(base, GCMD_IRE);
}

/// The register bases of the enabled remapping units; empty while translation is off.
fn units() -> impl Iterator<Item = u64> {
    let count = UNIT_COUNT.load(Ordering::Acquire);
    UNITS[..count].iter().map(|unit| unit.load(Ordering::Acquire))
}

fn acquire_invalidation_lock() {
    while INVALIDATION_LOCK.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
        core::hint::spin_loop();
    }
}

fn release_invalidation_lock() {
    INVALIDATION_LOCK.store(false, Ordering::Release);
}

/// Drops one domain's context-cache entries, then empties its IOTLB, on every unit. The verified
/// kernel calls it, under the root-table lock, right after it clears that domain's context entry;
/// the model's `IommuTLB::invalidate_domain` states both effects.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_iommu_invalidate_domain(did: usize) {
    let did = domain_id(did);
    acquire_invalidation_lock();
    for base in units() {
        invalidate_context_cache(base, CCMD_DOMAIN | did);
        invalidate_iotlb(base, IOTLB_DOMAIN | (did << 32));
    }
    release_invalidation_lock();
}

/// Empties one domain's IOTLB on every unit and waits, with only domain-selective IOTLB
/// invalidation; the context cache is untouched.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_iommu_invalidate_iotlb_domain(did: usize) {
    let did = domain_id(did);
    acquire_invalidation_lock();
    for base in units() {
        invalidate_iotlb(base, IOTLB_DOMAIN | (did << 32));
    }
    release_invalidation_lock();
}

/// `edu` registers and its DMA buffer window.
const EDU_ID: usize = 0x00;
const EDU_DMA_SRC: usize = 0x80;
const EDU_DMA_DST: usize = 0x88;
const EDU_DMA_COUNT: usize = 0x90;
const EDU_DMA_CMD: usize = 0x98;
const EDU_DMA_RUN: u64 = 1;
const EDU_DMA_TO_RAM: u64 = 2;
const EDU_BUFFER: u64 = 0x40000;
const EDU_ID_MAGIC: u32 = 0xed;

/// I/O virtual address the probe reads; the verified kernel never maps IOMMU tables.
const PROBE_IOVA: u64 = 0x80_0010_0000;
/// TSC cycles to wait for the device (it runs DMA from a 100 ms timer).
const PROBE_TIMEOUT: u64 = 20_000_000_000;

/// The B/D/F of the DMA test device, when it and the remapping unit are both present.
pub fn dma_test_device() -> Option<u16> {
    let device = boot::get_boot_info().dma_test_device?;
    (UNIT_COUNT.load(Ordering::Acquire) != 0).then_some(device.bdf)
}

/// Test only: has the DMA test device read 8 bytes at `PROBE_IOVA` and returns the VT-d fault
/// reason the read caused (2: context entry not present, 6: read through a non-present
/// second-level entry), or 0 if it was translated.
pub fn dma_probe() -> Option<u8> {
    dma_transfer(false)
}

/// Test only: writes the eight bytes previously loaded into EDU's buffer back to `PROBE_IOVA`.
/// Call the read probe on a mapped page first to seed the device buffer with known data.
pub fn dma_write_probe() -> Option<u8> {
    dma_transfer(true)
}

fn dma_transfer(to_ram: bool) -> Option<u8> {
    let device = boot::get_boot_info().dma_test_device?;
    if UNIT_COUNT.load(Ordering::Acquire) == 0 {
        return None;
    }
    let mmio = device.mmio;
    assert!(read32(mmio, EDU_ID) & 0xff == EDU_ID_MAGIC, "DMA test device is not edu");
    assert!(read64(mmio, EDU_DMA_CMD) & EDU_DMA_RUN == 0, "DMA test device is already running");
    for base in units() {
        let (records, count) = fault_records(base);
        for i in 0..count {
            write64(base, records + 16 * i + 8, FRCD_F);
        }
        write32(base, FSTS_REG, FSTS_PFO);
    }

    write64(mmio, EDU_DMA_SRC, if to_ram { EDU_BUFFER } else { PROBE_IOVA });
    write64(mmio, EDU_DMA_DST, if to_ram { PROBE_IOVA } else { EDU_BUFFER });
    write64(mmio, EDU_DMA_COUNT, 8);
    write64(mmio, EDU_DMA_CMD, EDU_DMA_RUN | if to_ram { EDU_DMA_TO_RAM } else { 0 });
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while read64(mmio, EDU_DMA_CMD) & EDU_DMA_RUN != 0 {
        assert!(unsafe { core::arch::x86_64::_rdtsc() } - start < PROBE_TIMEOUT, "DMA test device did not finish");
        core::hint::spin_loop();
    }

    // Whichever unit covers the device recorded the fault, if any.
    for base in units() {
        let fsts = read32(base, FSTS_REG);
        assert!(fsts & FSTS_PFO == 0, "VT-d fault record overflow during DMA probe");
        if fsts & FSTS_PPF == 0 {
            continue;
        }
        let (records, _) = fault_records(base);
        let record = records + 16 * ((fsts >> 8) & 0xff) as usize;
        let upper = read64(base, record + 8);
        assert!(upper & FRCD_F != 0, "VT-d pending fault has no valid record");
        assert!(upper & 0xffff == device.bdf as u64, "VT-d fault from another requester {:#x}", upper & 0xffff);
        assert!((upper & (1 << 62) == 0) == to_ram, "VT-d fault has the wrong DMA direction");
        assert!(read64(base, record) & !0xfff == PROBE_IOVA, "VT-d fault has the wrong IOVA");
        log::info!("DMA probe completed: to_ram={} requester={:#x} iova={:#x} fault={:#x}",
            to_ram, device.bdf, PROBE_IOVA, (upper >> 32) as u8);
        write64(base, record + 8, FRCD_F);
        return Some((upper >> 32) as u8);
    }
    Some(0)
}

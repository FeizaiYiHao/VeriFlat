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
//! - ECAP.QI = 1: every invalidation goes through the unit's invalidation queue. A unit of major
//!   version 6 or later treats register-based invalidation (CCMD, IOTLB registers) as incorrect and
//!   ignores it. Like Linux, a unit with ECAP.SMTS = 1 gets 256-bit descriptors (IQA.DW = 1), any
//!   other unit 128-bit ones.
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
use core::sync::atomic::{fence, AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};

use astd::boot::MAX_IOMMU_UNITS;

use crate::boot;

/// Register bases of the remapping units, valid up to `UNIT_COUNT`; 0 while translation is off.
static UNITS: [AtomicU64; MAX_IOMMU_UNITS] = [const { AtomicU64::new(0) }; MAX_IOMMU_UNITS];
static UNIT_COUNT: AtomicUsize = AtomicUsize::new(0);
/// Serializes the invalidation queues (their tails, slots and status words): a domain-selective
/// context-cache and IOTLB invalidation runs under the verified root-table lock, but an IOTLB-only
/// domain invalidation runs under one IOMMU table's lock, so invalidations of different domains may
/// race on a unit.
static INVALIDATION_LOCK: AtomicBool = AtomicBool::new(false);
/// One invalidation queue per unit: one 4 KiB page (IQA.QS = 0) of 256 128-bit or 128 256-bit
/// descriptors, as `QI_SHIFT` says.
#[repr(C, align(4096))]
struct InvalidationQueue([u64; REGISTER_PAGE / 8]);
static mut QUEUES: [InvalidationQueue; MAX_IOMMU_UNITS] = [const { InvalidationQueue([0; REGISTER_PAGE / 8]) }; MAX_IOMMU_UNITS];
/// log2 of each unit's descriptor size in bytes: `QI_SHIFT_128` or `QI_SHIFT_256`.
static QI_SHIFT: [AtomicU32; MAX_IOMMU_UNITS] = [const { AtomicU32::new(QI_SHIFT_128) }; MAX_IOMMU_UNITS];
/// The next free slot of each unit's queue; IQT holds it shifted left by `QI_SHIFT`.
static QI_TAIL: [AtomicUsize; MAX_IOMMU_UNITS] = [const { AtomicUsize::new(0) }; MAX_IOMMU_UNITS];
/// The word each unit's invalidation wait descriptor writes `QI_DONE` to.
static QI_STATUS: [AtomicU32; MAX_IOMMU_UNITS] = [const { AtomicU32::new(QI_PENDING) }; MAX_IOMMU_UNITS];
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

const VER_REG: usize = 0x00;
const CAP_REG: usize = 0x08;
const ECAP_REG: usize = 0x10;
const GCMD_REG: usize = 0x18;
const GSTS_REG: usize = 0x1c;
const RTADDR_REG: usize = 0x20;
const FSTS_REG: usize = 0x34;
const IQH_REG: usize = 0x80;
const IQT_REG: usize = 0x88;
const IQA_REG: usize = 0x90;
const IRTA_REG: usize = 0xb8;

const CAP_RWBF: u64 = 1 << 4;
const CAP_CM: u64 = 1 << 7;
const CAP_SAGAW_4_LEVEL: u64 = 1 << 10;
const CAP_DWD: u64 = 1 << 54;
const CAP_DRD: u64 = 1 << 55;
const CAP_ND_16_BIT: u64 = 6;
const ECAP_C: u64 = 1 << 0;
const ECAP_QI: u64 = 1 << 1;
const ECAP_IR: u64 = 1 << 3;
const ECAP_SMTS: u64 = 1 << 43;

/// TE, SRTP, QIE, IRE, SIRTP: GSTS reports them as TES, RTPS, QIES, IRES, IRTPS at the same positions.
const GCMD_TE: u32 = 1 << 31;
const GCMD_SRTP: u32 = 1 << 30;
const GCMD_QIE: u32 = 1 << 26;
const GCMD_IRE: u32 = 1 << 25;
const GCMD_SIRTP: u32 = 1 << 24;
/// GSTS bits whose GCMD counterparts are one-shot commands; a GCMD write must not repeat them.
const GSTS_ONE_SHOT: u32 = (1 << 30) | (1 << 29) | (1 << 27) | (1 << 24);

/// IQA.DW (bit 11): 256-bit descriptors; IQA.QS (bits 2:0) stays 0, one 4 KiB page.
const IQA_DW: u64 = 1 << 11;
/// Descriptor sizes: IQH and IQT hold the slot index shifted left by 4 (128-bit) or 5 (256-bit).
const QI_SHIFT_128: u32 = 4;
const QI_SHIFT_256: u32 = 5;
/// Queued-invalidation descriptors: the type in bits 3:0 and the DID in bits 31:16 of quadword 0;
/// every other quadword is 0 except the wait descriptor's status address in quadword 1.
const QI_DID_SHIFT: u32 = 16;
/// Context-cache invalidate descriptor (type 1), granularity G in bits 5:4.
const QI_CC: u64 = 0x1;
const QI_CC_GLOBAL: u64 = 1 << 4;
const QI_CC_DOMAIN: u64 = 2 << 4;
/// IOTLB invalidate descriptor (type 2), granularity G in bits 5:4, drain writes DW (bit 6), drain reads DR (bit 7).
const QI_IOTLB: u64 = 0x2;
const QI_IOTLB_GLOBAL: u64 = 1 << 4;
const QI_IOTLB_DOMAIN: u64 = 2 << 4;
const QI_IOTLB_DW: u64 = 1 << 6;
const QI_IOTLB_DR: u64 = 1 << 7;
/// Interrupt entry cache invalidate descriptor (type 4) with G (bit 4) = 0: global.
const QI_IEC_GLOBAL: u64 = 0x4;
/// Invalidation wait descriptor (type 5) with SW (bit 5): writes its status data (bits 63:32) to the
/// status address (quadword 1, bits 63:2) once every earlier descriptor in the queue has completed.
const QI_WAIT: u64 = 0x5;
const QI_WAIT_SW: u64 = 1 << 5;
const QI_WAIT_STATUS_DATA_SHIFT: u32 = 32;
const QI_PENDING: u32 = 0;
const QI_DONE: u32 = 1;

const FSTS_PFO: u32 = 1 << 0;
const FSTS_PPF: u32 = 1 << 1;
/// Invalidation queue error, invalidation completion error, invalidation time-out error.
const FSTS_IQE: u32 = 1 << 4;
const FSTS_ICE: u32 = 1 << 5;
const FSTS_ITE: u32 = 1 << 6;
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

/// Queues `descriptor`, then an invalidation wait descriptor that writes `QI_DONE` to the unit's
/// status word once every earlier descriptor has completed, and moves IQT past both. The caller
/// holds `INVALIDATION_LOCK`, or is `init` before the other CPUs start, and awaits each submission
/// (`qi_wait`) before the next, so the queue is empty here and never fills; the tail stays even, so
/// the pair never wraps.
fn qi_submit(unit: usize, base: u64, descriptor: u64) {
    let shift = QI_SHIFT[unit].load(Ordering::Relaxed);
    let words = 1usize << (shift - 3);
    let tail = QI_TAIL[unit].load(Ordering::Relaxed);
    let status = QI_STATUS[unit].as_ptr();
    let slots = unsafe { (&raw mut QUEUES[unit].0).cast::<u64>().add(tail * words) };
    let wait = [QI_WAIT | QI_WAIT_SW | ((QI_DONE as u64) << QI_WAIT_STATUS_DATA_SHIFT), status as u64, 0, 0];
    let descriptor = [descriptor, 0, 0, 0];
    unsafe {
        ptr::write_volatile(status, QI_PENDING);
        for i in 0..words {
            ptr::write_volatile(slots.add(i), descriptor[i]);
            ptr::write_volatile(slots.add(words + i), wait[i]);
        }
    }
    // Both descriptors and the reset status reach memory before the tail write publishes them.
    veriflat_iommu_flush_to_memory(slots as usize, 2 << shift);
    veriflat_iommu_flush_to_memory(status as usize, size_of::<u32>());
    fence(Ordering::SeqCst);
    let tail = (tail + 2) % (REGISTER_PAGE >> shift);
    QI_TAIL[unit].store(tail, Ordering::Relaxed);
    write64(base, IQT_REG, (tail as u64) << shift);
}

/// Waits, unbounded like `global_command`, until the unit writes `QI_DONE` for the last `qi_submit`.
/// An invalidation queue error (FSTS.IQE), invalidation completion error (ICE) or invalidation
/// time-out error (ITE) panics, naming the unit, rather than waiting for a status write that the
/// stopped queue may never make.
fn qi_wait(unit: usize, base: u64) {
    let status = QI_STATUS[unit].as_ptr();
    loop {
        // Drops a stale cached copy when some unit does not snoop CPU caches.
        veriflat_iommu_flush_to_memory(status as usize, size_of::<u32>());
        if unsafe { ptr::read_volatile(status) } == QI_DONE {
            return;
        }
        let fsts = read32(base, FSTS_REG);
        assert!(fsts & (FSTS_IQE | FSTS_ICE | FSTS_ITE) == 0, "VT-d at {:#x}: invalidation queue error, FSTS {:#x} IQH {:#x} IQT {:#x}", base, fsts, read64(base, IQH_REG), read64(base, IQT_REG));
        core::hint::spin_loop();
    }
}

/// Queues `descriptor` on one unit and waits for it.
fn qi_sync(unit: usize, base: u64, descriptor: u64) {
    qi_submit(unit, base, descriptor);
    qi_wait(unit, base);
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
        init_unit(i, base, root_table);
        UNITS[i].store(base, Ordering::Release);
    }
    UNIT_COUNT.store(units.len(), Ordering::Release);
    log::info!("VT-d translation enabled on {} unit(s), root table {:#x}", units.len(), root_table);
}

fn init_unit(unit: usize, base: u64, root_table: u64) {
    let ver = read32(base, VER_REG);
    let cap = read64(base, CAP_REG);
    let ecap = read64(base, ECAP_REG);
    let shift = if ecap & ECAP_SMTS != 0 { QI_SHIFT_256 } else { QI_SHIFT_128 };
    log::info!("VT-d at {:#x}: VER {}.{} CAP {:#x} ECAP {:#x}, queued invalidation with {}-bit descriptors", base, (ver >> 4) & 0xf, ver & 0xf, cap, ecap, 8 << shift);
    assert!(cap & CAP_CM == 0, "VT-d caching mode: attach would need an invalidation the model does not issue");
    assert!(cap & CAP_RWBF == 0, "VT-d requires write-buffer flushing, which the model does not issue");
    assert!(cap & 0x7 >= CAP_ND_16_BIT, "VT-d supports fewer than 2^16 domain IDs");
    assert!(cap & CAP_SAGAW_4_LEVEL != 0, "VT-d does not support 4-level tables");
    assert!(cap & CAP_DRD != 0 && cap & CAP_DWD != 0, "VT-d at {:#x}: CAP {:#x} lacks DMA read or write draining (CAP.DRD, CAP.DWD), which every IOTLB invalidation needs", base, cap);
    assert!(ecap & ECAP_QI != 0, "VT-d at {:#x}: ECAP {:#x} lacks queued invalidation (ECAP.QI), which every invalidation needs: a unit of major version 6 or later ignores register-based invalidation", base, ecap);
    let (records, count) = fault_records(base);
    assert!(records + 16 * count <= REGISTER_PAGE, "VT-d registers beyond the mapped page");
    assert!(read32(base, GSTS_REG) & (GCMD_TE | GCMD_IRE | GCMD_QIE) == 0, "VT-d translation, interrupt remapping or queued invalidation already enabled");
    assert!(ecap & ECAP_IR != 0, "VT-d does not support interrupt remapping");

    assert!(root_table & !RTADDR_RTA_MASK == 0, "VT-d root table {:#x} is not a 4 KiB-aligned 48-bit address", root_table);

    // Queued invalidation, before the first invalidation: an empty queue (IQT = 0; IQH reads 0 while
    // QIES is 0) at `QUEUES[unit]`, with stale queue errors cleared (FSTS is write-1-to-clear).
    write32(base, FSTS_REG, FSTS_IQE | FSTS_ICE | FSTS_ITE);
    QI_SHIFT[unit].store(shift, Ordering::Relaxed);
    QI_TAIL[unit].store(0, Ordering::Relaxed);
    write64(base, IQT_REG, 0);
    let queue = unsafe { &raw const QUEUES[unit] } as u64;
    write64(base, IQA_REG, queue | if shift == QI_SHIFT_256 { IQA_DW } else { 0 });
    global_command(base, GCMD_QIE);
    assert!(read64(base, IQH_REG) == 0, "VT-d at {:#x}: invalidation queue head {:#x} is not 0 once enabled", base, read64(base, IQH_REG));

    // TTM = 00: legacy-mode root table. After SRTP, invalidate the context cache, then the IOTLB
    // (a unit with CAP.ESRTPS = 0 invalidates neither on SRTP).
    write64(base, RTADDR_REG, root_table);
    global_command(base, GCMD_SRTP);
    qi_sync(unit, base, QI_CC | QI_CC_GLOBAL);
    qi_sync(unit, base, QI_IOTLB | QI_IOTLB_GLOBAL | QI_IOTLB_DR | QI_IOTLB_DW);
    global_command(base, GCMD_TE);

    // xAPIC destinations (EIME = 0). After SIRTP, invalidate the interrupt entry cache globally (a
    // unit with CAP.ESIRTPS = 0 does not on SIRTP), then enable remapping.
    write64(base, IRTA_REG, (&raw const IRT) as u64 | IRTA_SIZE_256);
    global_command(base, GCMD_SIRTP);
    qi_sync(unit, base, QI_IEC_GLOBAL);
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
/// the model's `IommuTLB::invalidate_domain` states both effects. The context-cache invalidation
/// has completed on every unit before any IOTLB invalidation is queued.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_iommu_invalidate_domain(did: usize) {
    let did = domain_id(did) << QI_DID_SHIFT;
    acquire_invalidation_lock();
    for (unit, base) in units().enumerate() {
        qi_submit(unit, base, QI_CC | QI_CC_DOMAIN | did);
    }
    for (unit, base) in units().enumerate() {
        qi_wait(unit, base);
    }
    invalidate_iotlb_domain(did);
    release_invalidation_lock();
}

/// Empties one domain's IOTLB on every unit and waits, with only domain-selective IOTLB
/// invalidation; the context cache is untouched.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_iommu_invalidate_iotlb_domain(did: usize) {
    let did = domain_id(did) << QI_DID_SHIFT;
    acquire_invalidation_lock();
    invalidate_iotlb_domain(did);
    release_invalidation_lock();
}

/// Domain-selective IOTLB invalidation of `did` (shifted into place) on every unit: queued on all,
/// then awaited on all, under `INVALIDATION_LOCK`. Every IOTLB invalidation drains the pending DMA
/// reads and writes of the domain (DR, DW), so no DMA that used a dropped translation completes
/// after the invalidation returns; `init_unit` requires CAP.DRD and CAP.DWD on every unit.
fn invalidate_iotlb_domain(did: u64) {
    for (unit, base) in units().enumerate() {
        qi_submit(unit, base, QI_IOTLB | QI_IOTLB_DOMAIN | QI_IOTLB_DR | QI_IOTLB_DW | did);
    }
    for (unit, base) in units().enumerate() {
        qi_wait(unit, base);
    }
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

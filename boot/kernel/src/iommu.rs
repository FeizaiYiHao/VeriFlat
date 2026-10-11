//! VT-d DMA remapping over the verified kernel's root table.
//!
//! The verified kernel owns the root table: `KernelK.irt` is a legacy-mode VT-d image pinned at
//! `KERNEL_IRT_OFFSET`, and its syscalls only write entries. This module points the remapping
//! unit at that image, enables translation, and implements the IOTLB hook. The model relies on
//! hardware properties that `init` checks:
//!
//! - CAP.CM = 0: not-present entries are never cached, so `pci_attach_dma` needs no invalidation.
//! - CAP.ND >= 6: 16-bit domain IDs, because the model's domain ID is the B/D/F.
//! - CAP.SAGAW bit 2: 4-level second-level tables, the address width the model writes.
//! - ECAP.C = 1: table walks snoop CPU caches, so the hardware reads what the model stores. An
//!   emulated remapping unit (under a hypervisor) reads guest memory directly and is accepted
//!   with C = 0. Supporting C = 0 hardware needs a cache-line flush after every store the unit
//!   may read, including the zeroing of IOMMU table pages.

use core::ptr;
use core::sync::atomic::{AtomicU64, Ordering};

use crate::boot;

/// Register base of the remapping unit; 0 while translation is off.
static BASE: AtomicU64 = AtomicU64::new(0);

const CAP_REG: usize = 0x08;
const ECAP_REG: usize = 0x10;
const GCMD_REG: usize = 0x18;
const GSTS_REG: usize = 0x1c;
const RTADDR_REG: usize = 0x20;
const CCMD_REG: usize = 0x28;
const FSTS_REG: usize = 0x34;

const CAP_CM: u64 = 1 << 7;
const CAP_SAGAW_4_LEVEL: u64 = 1 << 10;
const CAP_DWD: u64 = 1 << 54;
const CAP_DRD: u64 = 1 << 55;
const CAP_ND_16_BIT: u64 = 6;
const ECAP_C: u64 = 1 << 0;

/// TE, SRTP: GSTS reports them as TES, RTPS at the same positions.
const GCMD_TE: u32 = 1 << 31;
const GCMD_SRTP: u32 = 1 << 30;
/// GSTS bits whose GCMD counterparts are one-shot commands; a GCMD write must not repeat them.
const GSTS_ONE_SHOT: u32 = (1 << 30) | (1 << 29) | (1 << 27) | (1 << 24);

const CCMD_ICC: u64 = 1 << 63;
const CCMD_GLOBAL: u64 = 1 << 61;
const CCMD_DOMAIN: u64 = 2 << 61;

const IOTLB_IVT: u64 = 1 << 63;
const IOTLB_GLOBAL: u64 = 1 << 60;
const IOTLB_DOMAIN: u64 = 2 << 60;
const IOTLB_DR: u64 = 1 << 49;
const IOTLB_DW: u64 = 1 << 48;

const FSTS_PFO: u32 = 1 << 0;
const FSTS_PPF: u32 = 1 << 1;
const FRCD_F: u64 = 1 << 63;

const REGISTER_PAGE: usize = 4096;

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

/// Issues a persistent GCMD command (TE) or a one-shot one (SRTP) and waits until GSTS reports it.
fn global_command(base: u64, command: u32) {
    write32(base, GCMD_REG, (read32(base, GSTS_REG) & !GSTS_ONE_SHOT) | command);
    while read32(base, GSTS_REG) & command == 0 {
        core::hint::spin_loop();
    }
}

fn invalidate_context_cache(base: u64, command: u64) {
    write64(base, CCMD_REG, CCMD_ICC | command);
    while read64(base, CCMD_REG) & CCMD_ICC != 0 {
        core::hint::spin_loop();
    }
}

fn invalidate_iotlb(base: u64, command: u64) {
    let cap = read64(base, CAP_REG);
    let drain = if cap & CAP_DRD != 0 { IOTLB_DR } else { 0 } | if cap & CAP_DWD != 0 { IOTLB_DW } else { 0 };
    let reg = iotlb_reg(base);
    write64(base, reg, IOTLB_IVT | drain | command);
    while read64(base, reg) & IOTLB_IVT != 0 {
        core::hint::spin_loop();
    }
}

/// CPUID.01H:ECX[31]: a hypervisor emulates this machine, and with it the remapping unit.
fn under_hypervisor() -> bool {
    core::arch::x86_64::__cpuid(1).ecx & (1 << 31) != 0
}

/// Points the remapping unit at the verified root table at `root_table` and enables translation.
/// From here on a function's DMA faults until `pci_attach_dma` gives it a context entry. Runs on
/// CPU 0 before the other CPUs start.
pub fn init(root_table: u64) {
    let Some(base) = boot::get_boot_info().iommu_base else {
        log::warn!("no VT-d remapping unit: DMA is not translated");
        return;
    };
    let cap = read64(base, CAP_REG);
    let ecap = read64(base, ECAP_REG);
    log::info!("VT-d at {:#x}: CAP {:#x} ECAP {:#x}", base, cap, ecap);
    assert!(cap & CAP_CM == 0, "VT-d caching mode: attach would need an invalidation the model does not issue");
    assert!(cap & 0x7 >= CAP_ND_16_BIT, "VT-d supports fewer than 2^16 domain IDs");
    assert!(cap & CAP_SAGAW_4_LEVEL != 0, "VT-d does not support 4-level tables");
    let (records, count) = fault_records(base);
    assert!(iotlb_reg(base) + 8 <= REGISTER_PAGE && records + 16 * count <= REGISTER_PAGE, "VT-d registers beyond the mapped page");
    assert!(read32(base, GSTS_REG) & GCMD_TE == 0, "VT-d translation already enabled");
    assert!(ecap & ECAP_C != 0 || under_hypervisor(), "VT-d table walks do not snoop CPU caches");

    // TTM = 00: legacy-mode root table. After SRTP, invalidate the context cache, then the IOTLB.
    write64(base, RTADDR_REG, root_table);
    global_command(base, GCMD_SRTP);
    invalidate_context_cache(base, CCMD_GLOBAL);
    invalidate_iotlb(base, IOTLB_GLOBAL);
    global_command(base, GCMD_TE);
    BASE.store(base, Ordering::Release);
    log::info!("VT-d translation enabled, root table {:#x}", root_table);
}

/// Empties one domain's IOTLB. The verified kernel calls it, under the root-table lock, right after
/// it clears that domain's context entry, so the context cache (not in the model) is dropped first.
#[unsafe(no_mangle)]
pub extern "C" fn veriflat_iommu_invalidate_domain(did: usize) {
    let base = BASE.load(Ordering::Acquire);
    if base == 0 {
        return;
    }
    let did = did as u64 & 0xffff;
    invalidate_context_cache(base, CCMD_DOMAIN | did);
    invalidate_iotlb(base, IOTLB_DOMAIN | (did << 32));
}

/// `edu` registers and its DMA buffer window.
const EDU_ID: usize = 0x00;
const EDU_DMA_SRC: usize = 0x80;
const EDU_DMA_DST: usize = 0x88;
const EDU_DMA_COUNT: usize = 0x90;
const EDU_DMA_CMD: usize = 0x98;
const EDU_DMA_RUN: u64 = 1;
const EDU_BUFFER: u64 = 0x40000;
const EDU_ID_MAGIC: u32 = 0xed;

/// I/O virtual address the probe reads; the verified kernel never maps IOMMU tables.
const PROBE_IOVA: u64 = 0x10_0000;
/// TSC cycles to wait for the device (it runs DMA from a 100 ms timer).
const PROBE_TIMEOUT: u64 = 20_000_000_000;

/// The B/D/F of the DMA test device, when it and the remapping unit are both present.
pub fn dma_test_device() -> Option<u16> {
    let device = boot::get_boot_info().dma_test_device?;
    (BASE.load(Ordering::Acquire) != 0).then_some(device.bdf)
}

/// Test only: has the DMA test device read 8 bytes at `PROBE_IOVA` and returns the VT-d fault
/// reason the read caused (2: context entry not present, 6: read through a non-present
/// second-level entry), or 0 if it was translated.
pub fn dma_probe() -> Option<u8> {
    let device = boot::get_boot_info().dma_test_device?;
    let base = BASE.load(Ordering::Acquire);
    if base == 0 {
        return None;
    }
    let mmio = device.mmio;
    assert!(read32(mmio, EDU_ID) & 0xff == EDU_ID_MAGIC, "DMA test device is not edu");
    let (records, count) = fault_records(base);
    for i in 0..count {
        write64(base, records + 16 * i + 8, FRCD_F);
    }
    write32(base, FSTS_REG, FSTS_PFO);

    write64(mmio, EDU_DMA_SRC, PROBE_IOVA);
    write64(mmio, EDU_DMA_DST, EDU_BUFFER);
    write64(mmio, EDU_DMA_COUNT, 8);
    write64(mmio, EDU_DMA_CMD, EDU_DMA_RUN);
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while read64(mmio, EDU_DMA_CMD) & EDU_DMA_RUN != 0 {
        assert!(unsafe { core::arch::x86_64::_rdtsc() } - start < PROBE_TIMEOUT, "DMA test device did not finish");
        core::hint::spin_loop();
    }

    let fsts = read32(base, FSTS_REG);
    if fsts & FSTS_PPF == 0 {
        return Some(0);
    }
    let record = records + 16 * ((fsts >> 8) & 0xff) as usize;
    let upper = read64(base, record + 8);
    assert!(upper & 0xffff == device.bdf as u64, "VT-d fault from another requester {:#x}", upper & 0xffff);
    write64(base, record + 8, FRCD_F);
    Some((upper >> 32) as u8)
}

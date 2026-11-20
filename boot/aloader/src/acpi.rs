//! ACPI.

use core::ptr;
use core::mem;

use acpi::{AcpiTables, AcpiTable, PhysicalMapping};
use acpi::handler::AcpiHandler;
use acpi::madt::{Madt, MadtEntry};
use acpi::mcfg::Mcfg;
use acpi::sdt::{Signature, SdtHeader};
use astd::boot::{MAX_CPUS, MAX_IOMMU_UNITS};
use astd::heapless::Vec as ArrayVec;

#[derive(Clone, Debug)]
struct NullAcpiHandler {}

#[derive(Debug)]
#[repr(C, packed)]
struct Dmar {
    header: SdtHeader,

    host_address_width: u8,
    flags: u8,
    _reserved: [u8; 10],
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct RemappingHeader {
    struct_type: u16,
    length: u16,
}

#[derive(Debug)]
struct RemappingPtrIter {
    cur: *const u8,
    limit: *const u8,
}

/// DMA Remapping Hardware Unit Definition
///
/// Section 8.3
#[derive(Debug)]
#[repr(C, packed)]
struct Drhd {
    header: RemappingHeader,
    flags: u8,
    size: u8,
    segment_number: u16,
    register_base_address: u64,
}

impl NullAcpiHandler {
    fn new() -> Self {
        Self {}
    }
}

impl AcpiHandler for NullAcpiHandler {
    unsafe fn map_physical_region<T>(&self, physical_address: usize, size: usize) -> PhysicalMapping<Self, T> {
        let p = ptr::NonNull::new_unchecked(physical_address as *mut T);
        PhysicalMapping::new(
            physical_address,
            p,
            size,
            size,
            self.clone(),
        )
    }

    fn unmap_physical_region<T>(_region: &PhysicalMapping<Self, T>) {
        // no-op
    }
}

impl Dmar {
    fn iter_remapping_structs(&self) -> RemappingPtrIter {
        let entries_length = self.header.length as usize - mem::size_of::<Self>();
        let start = unsafe {
            (self as *const Self).add(1) as *const u8
        };
        let limit = unsafe {
            start.add(entries_length)
        };
        RemappingPtrIter {
            cur: start,
            limit,
        }
    }
}

unsafe impl AcpiTable for Dmar {
    const SIGNATURE: Signature = Signature::DMAR;

    fn header(&self) -> &SdtHeader {
        &self.header
    }
}

impl Iterator for RemappingPtrIter {
    type Item = &'static RemappingHeader;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur >= self.limit {
            return None;
        }

        let header = unsafe {
            &*(self.cur as *const RemappingHeader)
        };
        self.cur = unsafe {
            self.cur.add(header.length as usize)
        };

        log::info!("Header: {:?}", header);

        Some(header)
    }
}

impl RemappingHeader {
    const TYPE_DRHD: u16 = 0;

    fn as_drhd<'a>(&self) -> Option<&'a Drhd> {
        if self.struct_type != Self::TYPE_DRHD {
            return None;
        }

        let p = self as *const RemappingHeader as *const Drhd;
        let r = unsafe { &*p };
        Some(r)
    }
}

/// The ACPI tables, found from the RSDP that the bootloader passed (multiboot2 tags 14 and 15, which a UEFI
/// bootloader provides, or the PVH start info), else by searching the BIOS area, where a UEFI machine has none.
fn tables() -> AcpiTables<NullAcpiHandler> {
    let handler = NullAcpiHandler::new();
    unsafe {
        match crate::boot::get_rsdp_address() {
            Some(address) => AcpiTables::from_rsdp(handler, address).expect("invalid RSDP from the bootloader"),
            None => AcpiTables::search_for_rsdp_bios(handler).expect("failed to find RSDP"),
        }
    }
}

/// Local APIC IDs of the enabled processors listed in the MADT, in table order: Processor Local APIC (type 0) and
/// Processor Local x2APIC (type 9) entries alike, since firmware that hands over in x2APIC mode may list processors only
/// as type 9; an ID listed twice counts once. IDs above 254 are refused with a warning (the processor stays down):
/// the kernel takes 8-bit IDs and 255 is the xAPIC broadcast ID.
pub fn probe_cpus() -> ArrayVec<u8, MAX_CPUS> {
    let acpi = tables();
    let madt = acpi.find_table::<Madt>().expect("failed to find MADT");

    let mut ids: ArrayVec<u8, MAX_CPUS> = ArrayVec::new();
    let (mut type0, mut type9) = (0usize, 0usize);
    for entry in madt.get().entries() {
        let (apic_id, flags) = match entry {
            MadtEntry::LocalApic(lapic) => {
                type0 += 1;
                (lapic.apic_id as u32, lapic.flags)
            }
            MadtEntry::LocalX2Apic(x2apic) => {
                type9 += 1;
                (x2apic.x2apic_id, x2apic.flags)
            }
            _ => continue,
        };
        if flags & 1 == 0 {
            continue;
        }
        if apic_id > 254 {
            log::warn!("APIC ID {} is above 254, which VeriFlat does not support; that processor stays down", apic_id);
            continue;
        }
        if ids.iter().any(|&id| id as u32 == apic_id) {
            continue;
        }
        if ids.push(apic_id as u8).is_err() {
            log::warn!("more than {} processors; ignoring APIC ID {}", MAX_CPUS, apic_id);
        }
    }
    log::info!("MADT: {} local APIC and {} local x2APIC entries, {} enabled processors taken", type0, type9, ids.len());
    ids
}

/// Register bases of the VT-d remapping units, in DMAR order, and the DMAR host address width in bits (the
/// physical addresses DMA can reach). VeriFlat's isolation needs DMA remapping, so a machine without a DMAR table
/// or a DRHD entry does not boot. PCI segment groups other than 0 are not supported: the kernel's requester IDs
/// have no segment.
pub fn probe_iommu() -> (ArrayVec<u64, MAX_IOMMU_UNITS>, u8) {
    let acpi = tables();

    log::info!("ACPI: {:?}", acpi);

    let dmar = acpi.find_table::<Dmar>().expect("no DMAR table: VeriFlat needs VT-d DMA remapping");
    log::info!("DMAR: {:#?}", *dmar);

    let mut units = ArrayVec::new();
    for drhd in dmar.iter_remapping_structs().filter_map(|header| header.as_drhd()) {
        let (segment, base) = (drhd.segment_number, drhd.register_base_address);
        assert!(segment == 0, "DRHD for PCI segment {} is not supported", segment);
        units.push(base).expect("more DRHD entries than MAX_IOMMU_UNITS");
    }
    assert!(!units.is_empty(), "DMAR has no DRHD entry: VeriFlat needs VT-d DMA remapping");
    let width = dmar.host_address_width + 1;
    log::info!("DMAR host address width: {} bits", width);
    (units, width)
}

/// The PCI ECAM (MMCONFIG) windows of the MCFG table as `(base, size)`; empty without an MCFG.
pub fn probe_mmconfig() -> ArrayVec<(u64, u64), 8> {
    let acpi = tables();
    let mut windows = ArrayVec::new();
    if let Ok(mcfg) = acpi.find_table::<Mcfg>() {
        for entry in mcfg.get().entries() {
            let (base, start, end) = (entry.base_address, entry.bus_number_start, entry.bus_number_end);
            let size = (end as u64 - start as u64 + 1) << 20;
            log::info!("MMCONFIG {:#x}..{:#x} (buses {}..={})", base, base + size, start, end);
            windows.push((base, size)).expect("more than 8 MCFG entries");
        }
    }
    windows
}

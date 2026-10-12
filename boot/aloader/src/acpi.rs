//! ACPI.

use core::ptr;
use core::mem;

use acpi::{AcpiTables, AcpiTable, PhysicalMapping};
use acpi::handler::AcpiHandler;
use acpi::madt::{Madt, MadtEntry};
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

/// Local APIC IDs of the enabled processors listed in the MADT, in table order.
pub fn probe_cpus() -> ArrayVec<u8, MAX_CPUS> {
    let handler = NullAcpiHandler::new();
    let acpi = unsafe {
        AcpiTables::search_for_rsdp_bios(handler).expect("failed to find RSDP")
    };
    let madt = acpi.find_table::<Madt>().expect("failed to find MADT");

    let mut ids = ArrayVec::new();
    for entry in madt.get().entries() {
        if let MadtEntry::LocalApic(lapic) = entry {
            let (apic_id, flags) = (lapic.apic_id, lapic.flags);
            if flags & 1 != 0 && ids.push(apic_id).is_err() {
                log::warn!("more than {} processors; ignoring APIC ID {}", MAX_CPUS, apic_id);
            }
        }
    }
    ids
}

/// Register bases of the VT-d remapping units, in DMAR order. VeriFlat's isolation needs DMA
/// remapping, so a machine without a DMAR table or a DRHD entry does not boot. PCI segment groups
/// other than 0 are not supported: the kernel's requester IDs have no segment.
pub fn probe_iommu() -> ArrayVec<u64, MAX_IOMMU_UNITS> {
    let handler = NullAcpiHandler::new();
    let acpi = unsafe {
        AcpiTables::search_for_rsdp_bios(handler).expect("failed to find RSDP")
    };

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
    units
}

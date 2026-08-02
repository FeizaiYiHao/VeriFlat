use vstd::prelude::*;

verus! {

use crate::*;

pub const PCI_BUS_COUNT: usize = 256;
pub const PCI_DEVICE_COUNT: usize = 32;
pub const PCI_FUNCTION_COUNT: usize = 8;
pub const PCI_DEVFN_COUNT: usize = PCI_DEVICE_COUNT * PCI_FUNCTION_COUNT;

pub const VTD_ENTRY_SIZE: usize = 16;
pub const VTD_TABLE_SIZE: usize = PAGE_SZ_4K;
pub const VTD_CONTEXT_ADDRESS_MASK: usize = MEM_MASK as usize;
pub const VTD_CONTEXT_TRANSLATION_TYPE_MASK: usize = 0x3;
pub const VTD_CONTEXT_ADDRESS_WIDTH_MASK: usize = 0x7;
pub const VTD_CONTEXT_DID_MASK: usize = 0xffff;
pub const VTD_CONTEXT_AW_4_LEVEL: usize = 0x2;

pub type Seq3<A> = Seq<Seq<Seq<A>>>;

pub const IOMMU_ROOT_TABLE_HARDWARE_PAGES: usize = 1 + PCI_BUS_COUNT;
/// A total `usize` process owner occupies one machine word, so 65,536 owner
/// slots occupy exactly 128 pages on this 64-bit target.
pub const IOMMU_ROOT_TABLE_METADATA_PAGES: usize = 128;
pub const IOMMU_ROOT_TABLE_STATIC_PAGES: usize =
    IOMMU_ROOT_TABLE_HARDWARE_PAGES + IOMMU_ROOT_TABLE_METADATA_PAGES;
/// Kept as a literal because Verus checks executable `usize` constant
/// arithmetic for overflow; the compile-time layout assertions below tie it
/// back to the actual structure.
pub const IOMMU_ROOT_TABLE_STATIC_SIZE: usize = 1_576_960;

pub open spec fn pci_bdf_valid(bus: usize, device: usize, function: usize) -> bool {
    &&& bus < PCI_BUS_COUNT
    &&& device < PCI_DEVICE_COUNT
    &&& function < PCI_FUNCTION_COUNT
}

pub open spec fn pci_devfn(device: usize, function: usize) -> usize
    recommends
        device < PCI_DEVICE_COUNT,
        function < PCI_FUNCTION_COUNT,
{
    (device * PCI_FUNCTION_COUNT + function) as usize
}

/// We do not allocate VT-d domain IDs: an exclusively owned PCI function has
/// a stable, globally unique 16-bit BDF encoding.
pub open spec fn pci_bdf_did(bus: usize, device: usize, function: usize) -> usize
    recommends pci_bdf_valid(bus, device, function),
{
    (bus * PCI_DEVFN_COUNT + device * PCI_FUNCTION_COUNT + function) as usize
}

/// Common 128-bit legacy VT-d root/context-entry representation. This is an
/// internal encoding detail; clients use the two `spec_index_*` interfaces.
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C)]
struct VtdLegacyEntry {
    lower: usize,
    upper: usize,
}

impl VtdLegacyEntry {
    closed spec fn present(&self) -> bool {
        self.lower & 1 == 1
    }

    closed spec fn address(&self) -> PAddr {
        self.lower & VTD_CONTEXT_ADDRESS_MASK
    }

    closed spec fn translation_type(&self) -> usize {
        (self.lower >> 2) & VTD_CONTEXT_TRANSLATION_TYPE_MASK
    }

    closed spec fn address_width(&self) -> usize {
        self.upper & VTD_CONTEXT_ADDRESS_WIDTH_MASK
    }

    closed spec fn domain_id(&self) -> usize {
        (self.upper >> 8) & VTD_CONTEXT_DID_MASK
    }
}

/// One 4KiB legacy context table, indexed by device/function (devfn).
#[repr(C, align(4096))]
struct IommuContextTable {
    entries: Array<VtdLegacyEntry, PCI_DEVFN_COUNT>,
}

impl IommuContextTable {
    closed spec fn wf(&self) -> bool {
        self.entries.wf()
    }

    closed spec fn entry(&self, device: usize, function: usize) -> VtdLegacyEntry
        recommends
            self.wf(),
            device < PCI_DEVICE_COUNT,
            function < PCI_FUNCTION_COUNT,
    {
        self.entries.spec_index(pci_devfn(device, function))
    }
}

/// Runtime ownership metadata.  The nesting deliberately mirrors B/D/F
/// rather than flattening BDF, so every function has one total owner slot.
#[repr(C)]
struct IommuDeviceMetadata {
    functions: Array<RwLockProcessPtr, PCI_FUNCTION_COUNT>,
}

impl IommuDeviceMetadata {
    closed spec fn wf(&self) -> bool {
        self.functions.wf()
    }
}

#[repr(C)]
struct IommuBusMetadata {
    devices: Array<IommuDeviceMetadata, PCI_DEVICE_COUNT>,
}

impl IommuBusMetadata {
    closed spec fn wf(&self) -> bool {
        &&& self.devices.wf()
        &&& forall|device: usize|
            #![trigger self.devices.spec_index(device).wf()]
            device < PCI_DEVICE_COUNT
            ==> self.devices.spec_index(device).wf()
    }
}

/// Fully static legacy VT-d root-table image:
///   * first page: 256 root entries;
///   * next 256 pages: one context table for every bus;
///   * final 3-D array: one owner slot for every B/D/F.
///
/// The value must be pinned at `table_base`; copying or moving it after the
/// root entries are initialized would invalidate their embedded addresses.
#[repr(C, align(4096))]
pub struct IommuRootTable {
    root_entries: Array<VtdLegacyEntry, PCI_BUS_COUNT>,
    context_tables: Array<IommuContextTable, PCI_BUS_COUNT>,
    metadata: Array<IommuBusMetadata, PCI_BUS_COUNT>,
    table_base: Ghost<PAddr>,
}

impl IommuRootTable {
    closed spec fn context_table_address(&self, bus: usize) -> PAddr
        recommends bus < PCI_BUS_COUNT,
    {
        (self.table_base@ + VTD_TABLE_SIZE * (bus + 1)) as usize
    }

    closed spec fn context_entry(
        &self,
        bus: usize,
        device: usize,
        function: usize,
    ) -> VtdLegacyEntry
        recommends
            self.context_tables.wf(),
            pci_bdf_valid(bus, device, function),
            self.context_tables.spec_index(bus).wf(),
    {
        self.context_tables.spec_index(bus).entry(device, function)
    }

    /// Logical hardware interface. `None` means the context entry is not
    /// present; `Some(root)` exposes only its second-level page-table root.
    pub closed spec fn iommu_roots(&self) -> Seq3<Option<PageTableRoot>> {
        Seq::new(PCI_BUS_COUNT as nat, |bus: int|
            Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
                Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| {
                    let context = self.context_entry(
                        bus as usize,
                        device as usize,
                        function as usize,
                    );
                    if context.present() {
                        Some(context.address())
                    } else {
                        None
                    }
                })
            )
        )
    }

    /// Total logical ownership interface. Every BDF slot has a process owner,
    /// independently of whether its context entry is currently present.
    pub closed spec fn owners(&self) -> Seq3<RwLockProcessPtr> {
        Seq::new(PCI_BUS_COUNT as nat, |bus: int|
            Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
                Seq::new(PCI_FUNCTION_COUNT as nat, |function: int|
                    self.metadata.spec_index(bus as usize)
                        .devices.spec_index(device as usize)
                        .functions.spec_index(function as usize)
                )
            )
        )
    }

    /// Indexes the logical second-level root selected by one PCI function.
    /// `None` means that the corresponding context entry is not present.
    pub closed spec fn spec_index_iommu_root(
        &self,
        bus: usize,
        device: usize,
        function: usize,
    ) -> Option<PageTableRoot>
        recommends
            self.wf(),
            pci_bdf_valid(bus, device, function),
    {
        self.iommu_roots()[bus as int][device as int][function as int]
    }

    /// Indexes the total process owner of one PCI function.
    pub closed spec fn spec_index_owner(
        &self,
        bus: usize,
        device: usize,
        function: usize,
    ) -> RwLockProcessPtr
        recommends
            self.wf(),
            pci_bdf_valid(bus, device, function),
    {
        self.owners()[bus as int][device as int][function as int]
    }

    #[verifier::opaque]
    pub closed spec fn wf(&self) -> bool {
        &&& self.root_entries.wf()
        &&& self.context_tables.wf()
        &&& self.metadata.wf()
        &&& self.iommu_roots().len() == PCI_BUS_COUNT
        &&& self.owners().len() == PCI_BUS_COUNT
        &&& self.table_base@ % VTD_TABLE_SIZE == 0
        &&& self.table_base@ <= usize::MAX - IOMMU_ROOT_TABLE_STATIC_SIZE
        &&& forall|bus: usize|
            #![trigger self.root_entries.spec_index(bus)]
            bus < PCI_BUS_COUNT
            ==> {
                let root = self.root_entries.spec_index(bus);
                &&& root.present()
                &&& root.address() == self.context_table_address(bus)
                &&& root.lower == (self.context_table_address(bus) | 1)
                &&& root.upper == 0
            }
        &&& forall|bus: usize|
            #![trigger self.context_tables.spec_index(bus).wf()]
            bus < PCI_BUS_COUNT
            ==> self.context_tables.spec_index(bus).wf()
        &&& forall|bus: usize|
            #![trigger self.metadata.spec_index(bus).wf()]
            bus < PCI_BUS_COUNT
            ==> self.metadata.spec_index(bus).wf()
        &&& forall|bus: usize|
            #![trigger self.iommu_roots()[bus as int]]
            #![trigger self.owners()[bus as int]]
            bus < PCI_BUS_COUNT
            ==> {
                &&& self.iommu_roots()[bus as int].len() == PCI_DEVICE_COUNT
                &&& self.owners()[bus as int].len() == PCI_DEVICE_COUNT
            }
        &&& forall|bus: usize, device: usize|
            #![trigger self.iommu_roots()[bus as int][device as int]]
            #![trigger self.owners()[bus as int][device as int]]
            bus < PCI_BUS_COUNT && device < PCI_DEVICE_COUNT
            ==> {
                &&& self.iommu_roots()[bus as int][device as int].len()
                    == PCI_FUNCTION_COUNT
                &&& self.owners()[bus as int][device as int].len()
                    == PCI_FUNCTION_COUNT
            }
        &&& forall|bus: usize, device: usize, function: usize|
            #![trigger self.iommu_roots()[bus as int][device as int][function as int]]
            pci_bdf_valid(bus, device, function)
            ==> {
                let context = self.context_entry(bus, device, function);
                let iommu_root =
                    self.iommu_roots()[bus as int][device as int][function as int];
                &&& self.owners()[bus as int][device as int][function as int]
                    == self.metadata.spec_index(bus).devices.spec_index(device)
                        .functions.spec_index(function)
                &&& iommu_root is None ==> {
                    &&& context.lower == 0
                    &&& context.upper == 0
                }
                &&& iommu_root is Some ==> {
                    let root = iommu_root.unwrap();
                    &&& context.present()
                    &&& context.address() == root
                    &&& context.lower == (root | 1)
                    &&& context.translation_type() == 0
                    &&& context.address_width() == VTD_CONTEXT_AW_4_LEVEL
                    &&& context.domain_id() == pci_bdf_did(bus, device, function)
                    &&& context.upper
                        == ((pci_bdf_did(bus, device, function) << 8)
                            | VTD_CONTEXT_AW_4_LEVEL)
                }
            }
    }
}

}

// Compile-time checks for the hardware layout and the stated memory budget.
const ASSERT_VTD_ENTRY_SIZE: [(); VTD_ENTRY_SIZE] =
    [(); core::mem::size_of::<VtdLegacyEntry>()];
const ASSERT_VTD_CONTEXT_TABLE_SIZE: [(); VTD_TABLE_SIZE] =
    [(); core::mem::size_of::<IommuContextTable>()];
const ASSERT_VTD_CONTEXT_TABLE_ALIGNMENT: [(); VTD_TABLE_SIZE] =
    [(); core::mem::align_of::<IommuContextTable>()];
const ASSERT_IOMMU_CONTEXT_TABLES_OFFSET: [(); VTD_TABLE_SIZE] =
    [(); core::mem::offset_of!(IommuRootTable, context_tables)];
const ASSERT_IOMMU_METADATA_OFFSET: [(); IOMMU_ROOT_TABLE_HARDWARE_PAGES * VTD_TABLE_SIZE] =
    [(); core::mem::offset_of!(IommuRootTable, metadata)];
const ASSERT_IOMMU_ROOT_TABLE_SIZE: [(); IOMMU_ROOT_TABLE_STATIC_SIZE] =
    [(); core::mem::size_of::<IommuRootTable>()];
const ASSERT_IOMMU_ROOT_TABLE_ALIGNMENT: [(); VTD_TABLE_SIZE] =
    [(); core::mem::align_of::<IommuRootTable>()];

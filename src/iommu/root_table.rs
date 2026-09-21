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

fn iommu_context_table_address(
    table_base: PAddr,
    bus: usize,
) -> (ret: PAddr)
    requires
        bus < PCI_BUS_COUNT,
        table_base % VTD_TABLE_SIZE == 0,
        0 < VTD_TABLE_SIZE,
        table_base as int
            + VTD_TABLE_SIZE as int * (bus as int + 1)
            <= usize::MAX as int,
    ensures
        ret as int == table_base as int
            + VTD_TABLE_SIZE as int * (bus as int + 1),
        ret % VTD_TABLE_SIZE == 0,
{
    let offset = VTD_TABLE_SIZE * (bus + 1);
    let ret = table_base + offset;
    proof {
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(bus as int + 1, table_base as int, VTD_TABLE_SIZE as int);
    }
    ret
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
    fn disabled() -> (ret: Self)
        ensures
            ret.lower == 0,
            ret.upper == 0,
            !ret.present(),
    {
        let ret = Self { lower: 0, upper: 0 };
        assert(0usize & 1usize != 1usize) by (bit_vector);
        ret
    }

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
    closed spec fn all_disabled(&self) -> bool {
        &&& self.wf()
        &&& forall|device: usize, function: usize|
            #![trigger self.entry(device, function)]
            device < PCI_DEVICE_COUNT
            && function < PCI_FUNCTION_COUNT
            ==> {
                &&& self.entry(device, function).lower == 0
                &&& self.entry(device, function).upper == 0
                &&& !self.entry(device, function).present()
            }
    }

    fn new_disabled() -> (ret: Self)
        ensures
            ret.all_disabled(),
    {
        let ret = Self {
            entries: Array::new_with_init_value(
                VtdLegacyEntry::disabled(),
            ),
        };
        ret
    }

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
    fn new_owner(owner_process: RwLockProcessPtr) -> (ret: Self)
        ensures
            ret.wf(),
            forall|function: usize|
                #![trigger ret.functions.spec_index(function)]
                function < PCI_FUNCTION_COUNT
                ==> ret.functions.spec_index(function) == owner_process,
    {
        let ret = Self {
            functions: Array::new_with_init_value(owner_process),
        };
        ret
    }

    closed spec fn wf(&self) -> bool {
        self.functions.wf()
    }
}

#[repr(C)]
struct IommuBusMetadata {
    devices: Array<IommuDeviceMetadata, PCI_DEVICE_COUNT>,
}

impl IommuBusMetadata {
    closed spec fn all_owned_by(
        &self,
        owner_process: RwLockProcessPtr,
    ) -> bool {
        &&& self.wf()
        &&& forall|device: usize, function: usize|
            #![trigger self.devices.spec_index(device)
                .functions.spec_index(function)]
            device < PCI_DEVICE_COUNT
            && function < PCI_FUNCTION_COUNT
            ==> self.devices.spec_index(device)
                .functions.spec_index(function) == owner_process
    }

    fn new_owner(owner_process: RwLockProcessPtr) -> (ret: Self)
        ensures
            ret.all_owned_by(owner_process),
    {
        let mut devices:
            Array<IommuDeviceMetadata, PCI_DEVICE_COUNT> = Array::new();
        let mut device = 0;
        while device < PCI_DEVICE_COUNT
            invariant
                0 <= device <= PCI_DEVICE_COUNT,
                devices.wf(),
                forall|old_device: usize|
                    #![trigger devices.spec_index(old_device).wf()]
                    old_device < device
                    ==> devices.spec_index(old_device).wf(),
                forall|old_device: usize, function: usize|
                    #![trigger devices.spec_index(old_device)
                        .functions.spec_index(function)]
                    old_device < device
                    && function < PCI_FUNCTION_COUNT
                    ==> devices.spec_index(old_device)
                        .functions.spec_index(function) == owner_process,
            decreases PCI_DEVICE_COUNT - device,
        {
            devices.set(device, IommuDeviceMetadata::new_owner(owner_process));
            device = device + 1;
        }
        let ret = Self { devices };
        ret
    }

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
    pub fn new_disabled(
        table_base: PAddr,
        owner_process: RwLockProcessPtr,
    ) -> (ret: Self)
        requires
            table_base % VTD_TABLE_SIZE == 0,
            table_base as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int
                <= MEM_MASK as int,
            table_base as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int
                <= usize::MAX as int,
            0 < VTD_TABLE_SIZE,
        ensures
            ret.wf(),
            forall|bus: usize, device: usize, function: usize|
                #![trigger ret.spec_index_iommu_root(bus, device, function)]
                pci_bdf_valid(bus, device, function)
                ==> ret.spec_index_iommu_root(bus, device, function) is None,
            forall|bus: usize, device: usize, function: usize|
                #![trigger ret.spec_index_owner(bus, device, function)]
                pci_bdf_valid(bus, device, function)
                ==> ret.spec_index_owner(bus, device, function) == owner_process,
    {
        let mut root_entries: Array<VtdLegacyEntry, PCI_BUS_COUNT> =
            Array::new();
        let mut context_tables:
            Array<IommuContextTable, PCI_BUS_COUNT> = Array::new();
        let mut metadata: Array<IommuBusMetadata, PCI_BUS_COUNT> =
            Array::new();
        let mut bus = 0;
        while bus < PCI_BUS_COUNT
            invariant
                0 <= bus <= PCI_BUS_COUNT,
                root_entries.wf(),
                context_tables.wf(),
                metadata.wf(),
                table_base % VTD_TABLE_SIZE == 0,
                table_base as int
                    + IOMMU_ROOT_TABLE_STATIC_SIZE as int
                    <= MEM_MASK as int,
                table_base as int
                    + IOMMU_ROOT_TABLE_STATIC_SIZE as int
                    <= usize::MAX as int,
                0 < VTD_TABLE_SIZE,
                forall|old_bus: usize|
                    #![trigger root_entries.spec_index(old_bus)]
                    old_bus < bus
                    ==> {
                        let address: usize =
                            (table_base + VTD_TABLE_SIZE
                                * (old_bus + 1)) as usize;
                        &&& root_entries.spec_index(old_bus).lower
                            == (address | 1)
                        &&& root_entries.spec_index(old_bus).upper == 0
                        &&& root_entries.spec_index(old_bus).present()
                        &&& root_entries.spec_index(old_bus).address()
                            == address
                    },
                forall|old_bus: usize|
                    #![trigger context_tables.spec_index(old_bus)
                        .all_disabled()]
                    old_bus < bus
                    ==> context_tables.spec_index(old_bus).all_disabled(),
                forall|old_bus: usize|
                    #![trigger context_tables.spec_index(old_bus).wf()]
                    old_bus < bus
                    ==> context_tables.spec_index(old_bus).wf(),
                forall|old_bus: usize, device: usize, function: usize|
                    #![trigger context_tables.spec_index(old_bus)
                        .entry(device, function)]
                    old_bus < bus
                    && device < PCI_DEVICE_COUNT
                    && function < PCI_FUNCTION_COUNT
                    ==> {
                        &&& context_tables.spec_index(old_bus)
                            .entry(device, function).lower == 0
                        &&& context_tables.spec_index(old_bus)
                            .entry(device, function).upper == 0
                        &&& !context_tables.spec_index(old_bus)
                            .entry(device, function).present()
                    },
                forall|old_bus: usize|
                    #![trigger metadata.spec_index(old_bus)
                        .all_owned_by(owner_process)]
                    old_bus < bus
                    ==> metadata.spec_index(old_bus)
                        .all_owned_by(owner_process),
                forall|old_bus: usize|
                    #![trigger metadata.spec_index(old_bus).wf()]
                    old_bus < bus
                    ==> metadata.spec_index(old_bus).wf(),
                forall|old_bus: usize, device: usize, function: usize|
                    #![trigger metadata.spec_index(old_bus)
                        .devices.spec_index(device)
                        .functions.spec_index(function)]
                    old_bus < bus
                    && device < PCI_DEVICE_COUNT
                    && function < PCI_FUNCTION_COUNT
                    ==> metadata.spec_index(old_bus)
                        .devices.spec_index(device)
                        .functions.spec_index(function) == owner_process,
            decreases PCI_BUS_COUNT - bus,
        {
            assert(VTD_TABLE_SIZE as int == 4096) by (compute);
            assert(
                IOMMU_ROOT_TABLE_STATIC_SIZE as int == 1_576_960
            )
                by (compute);
            assert(
                4096 * (bus as int + 1) <= 1_048_576
            ) by {
            }
            assert(
                table_base as int
                    + 4096 * (bus as int + 1)
                    <= MEM_MASK as int
            ) by {
                assert(
                    table_base as int + 1_576_960
                        <= MEM_MASK as int
                );
            }
            assert(
                table_base as int
                    + 4096 * (bus as int + 1)
                    <= usize::MAX as int
            ) by {
                assert(
                    table_base as int + 1_576_960
                        <= usize::MAX as int
                );
            }
            let context_address =
                iommu_context_table_address(table_base, bus);
            assert({
                &&& (context_address | 1)
                    & VTD_CONTEXT_ADDRESS_MASK == context_address
                &&& (context_address | 1) & 1 == 1
            }) by (bit_vector)
                requires
                    context_address % VTD_TABLE_SIZE == 0,
                    context_address <= MEM_MASK as usize,
            ;
            root_entries.set(
                bus,
                VtdLegacyEntry {
                    lower: context_address | 1,
                    upper: 0,
                },
            );
            let context_table = IommuContextTable::new_disabled();
            context_tables.set(bus, context_table);
            let bus_metadata =
                IommuBusMetadata::new_owner(owner_process);
            metadata.set(bus, bus_metadata);
            bus = bus + 1;
        }
        let ret = Self {
            root_entries,
            context_tables,
            metadata,
            table_base: Ghost(table_base),
        };
        assert(ret.iommu_roots().len() == PCI_BUS_COUNT) by {
        }
        assert(ret.owners().len() == PCI_BUS_COUNT) by {
        }
        assert(
            ret.table_base.view()
                <= usize::MAX - IOMMU_ROOT_TABLE_STATIC_SIZE
        ) by {
            assert(
                ret.table_base.view() as int
                    + IOMMU_ROOT_TABLE_STATIC_SIZE as int
                    <= usize::MAX as int
            );
        }
        assert(ret.wf()) by {
            reveal(IommuRootTable::wf);
        }
        assert(
            forall|bus: usize, device: usize, function: usize|
                #![trigger ret.spec_index_iommu_root(
                    bus, device, function)]
                pci_bdf_valid(bus, device, function)
                ==> ret.spec_index_iommu_root(
                    bus, device, function) is None
        ) by {
        }
        assert(
            forall|bus: usize, device: usize, function: usize|
                #![trigger ret.spec_index_owner(
                    bus, device, function)]
                pci_bdf_valid(bus, device, function)
                ==> ret.spec_index_owner(
                    bus, device, function) == owner_process
        ) by {
        }
        ret
    }

    closed spec fn context_table_address(&self, bus: usize) -> PAddr
        recommends bus < PCI_BUS_COUNT,
    {
        (self.table_base.view() + VTD_TABLE_SIZE * (bus + 1)) as usize
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
                    let context = self.context_entry(bus as usize, device as usize, function as usize);
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
        self.iommu_roots().spec_index(bus as int).spec_index(device as int).spec_index(function as int)
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
        self.owners().spec_index(bus as int).spec_index(device as int).spec_index(function as int)
    }

    #[verifier::opaque]
    pub closed spec fn wf(&self) -> bool {
        &&& self.root_entries.wf()
        &&& self.context_tables.wf()
        &&& self.metadata.wf()
        &&& self.iommu_roots().len() == PCI_BUS_COUNT
        &&& self.owners().len() == PCI_BUS_COUNT
        &&& self.table_base.view() % VTD_TABLE_SIZE == 0
        &&& self.table_base.view() <= usize::MAX - IOMMU_ROOT_TABLE_STATIC_SIZE
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
            #![trigger self.iommu_roots().spec_index(bus as int)]
            #![trigger self.owners().spec_index(bus as int)]
            bus < PCI_BUS_COUNT
            ==> {
                &&& self.iommu_roots().spec_index(bus as int).len() == PCI_DEVICE_COUNT
                &&& self.owners().spec_index(bus as int).len() == PCI_DEVICE_COUNT
            }
        &&& forall|bus: usize, device: usize|
            #![trigger self.iommu_roots().spec_index(bus as int).spec_index(device as int)]
            #![trigger self.owners().spec_index(bus as int).spec_index(device as int)]
            bus < PCI_BUS_COUNT && device < PCI_DEVICE_COUNT
            ==> {
                &&& self.iommu_roots().spec_index(bus as int).spec_index(device as int).len()
                    == PCI_FUNCTION_COUNT
                &&& self.owners().spec_index(bus as int).spec_index(device as int).len()
                    == PCI_FUNCTION_COUNT
            }
        &&& forall|bus: usize, device: usize, function: usize|
            #![trigger self.iommu_roots().spec_index(bus as int).spec_index(device as int).spec_index(function as int)]
            pci_bdf_valid(bus, device, function)
            ==> {
                let context = self.context_entry(bus, device, function);
                let iommu_root =
                    self.iommu_roots().spec_index(bus as int).spec_index(device as int).spec_index(function as int);
                &&& self.owners().spec_index(bus as int).spec_index(device as int).spec_index(function as int)
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

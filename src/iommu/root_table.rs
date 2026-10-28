use vstd::prelude::*;
use vstd::assert_seqs_equal;

verus! {
use crate::*;

pub const PCI_BUS_COUNT: usize = 256;
pub const PCI_DEVICE_COUNT: usize = 32;
pub const PCI_FUNCTION_COUNT: usize = 8;
pub const PCI_DEVFN_COUNT: usize = PCI_DEVICE_COUNT * PCI_FUNCTION_COUNT;
/// One context entry and one owner slot for every B/D/F.
pub const PCI_BDF_COUNT: usize = PCI_BUS_COUNT * PCI_DEVFN_COUNT;

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
/// Kept as a literal because Verus checks executable `usize` constant
/// arithmetic for overflow; the compile-time layout assertions below tie it
/// back to the actual structure.
pub const IOMMU_ROOT_TABLE_STATIC_SIZE: usize = 1_576_960;

pub open spec fn pci_bdf_valid(bus: usize, device: usize, function: usize) -> bool {
    &&& bus < PCI_BUS_COUNT
    &&& device < PCI_DEVICE_COUNT
    &&& function < PCI_FUNCTION_COUNT
}

/// Stable, globally unique 16-bit BDF encoding. It indexes the flat
/// context-entry and owner-slot arrays below and is the function's candidate
/// VT-d domain ID; a present context entry may carry any valid domain ID.
pub open spec fn pci_bdf_did(bus: usize, device: usize, function: usize) -> usize
    recommends
        pci_bdf_valid(bus, device, function),
{
    (bus * PCI_DEVFN_COUNT + device * PCI_FUNCTION_COUNT + function) as usize
}

/// Total inverse of `pci_bdf_did` on valid DIDs: the B/D/F whose candidate DID is `did`.
pub open spec fn pci_bdf_of_did(did: VtdDomainId) -> PciBdf {
    (did / PCI_DEVFN_COUNT, (did % PCI_DEVFN_COUNT) / PCI_FUNCTION_COUNT, did % PCI_FUNCTION_COUNT)
}

/// Lexicographic B/D/F order; on valid B/D/Fs it is the flat slot order of `pci_bdf_did`.
pub open spec fn pci_bdf_lt(a: PciBdf, b: PciBdf) -> bool { a.0 < b.0 || (a.0 == b.0 && (a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))) }

/// `s` with the one B/D/F slot replaced by `v`.
pub open spec fn seq3_update<A>(s: Seq3<A>, bus: int, device: int, function: int, v: A) -> Seq3<A> {
    Seq::new(PCI_BUS_COUNT as nat, |b: int| Seq::new(PCI_DEVICE_COUNT as nat, |d: int|
        Seq::new(PCI_FUNCTION_COUNT as nat, |f: int| if b == bus && d == device && f == function { v } else { s[b][d][f] })))
}

/// The B/D/F view of a flat per-function sequence indexed by `pci_bdf_did`.
pub open spec fn seq3_from_flat<A>(flat: Seq<A>) -> Seq3<A> {
    Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| flat[pci_bdf_did(bus as usize, device as usize, function as usize) as int])))
}

fn iommu_context_table_address(table_base: PAddr, bus: usize) -> (ret: PAddr)
    requires
        bus < PCI_BUS_COUNT,
        table_base % VTD_TABLE_SIZE == 0,
        0 < VTD_TABLE_SIZE,
        table_base as int + VTD_TABLE_SIZE as int * (bus as int + 1) <= usize::MAX as int,
    ensures
        ret as int == table_base as int + VTD_TABLE_SIZE as int * (bus as int + 1),
        ret % VTD_TABLE_SIZE == 0,
{
    let offset = VTD_TABLE_SIZE * (bus + 1);
    let ret = table_base + offset;
    proof { vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(bus as int + 1, table_base as int, VTD_TABLE_SIZE as int); }
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

    closed spec fn present(&self) -> bool { self.lower & 1 == 1 }
    closed spec fn address(&self) -> PAddr { self.lower & VTD_CONTEXT_ADDRESS_MASK }
    closed spec fn translation_type(&self) -> usize { (self.lower >> 2) & VTD_CONTEXT_TRANSLATION_TYPE_MASK }
    closed spec fn address_width(&self) -> usize { self.upper & VTD_CONTEXT_ADDRESS_WIDTH_MASK }
    closed spec fn domain_id(&self) -> usize { (self.upper >> 8) & VTD_CONTEXT_DID_MASK }

    /// The logical second-level root exposed by a context entry.
    closed spec fn iommu_root(&self) -> Option<PageTableRoot> {
        if self.present() { Some(self.address()) } else { None }
    }

    /// The logical VT-d domain ID exposed by a context entry.
    closed spec fn iommu_did(&self) -> Option<VtdDomainId> {
        if self.present() { Some(self.domain_id()) } else { None }
    }
}

/// Fully static legacy VT-d root-table image:
///   * first page: 256 root entries;
///   * next 256 pages: the 256 context tables, one page per bus, kept as one
///     flat per-function entry array indexed by `pci_bdf_did`;
///   * final 128 pages: one owner slot for every B/D/F, indexed the same way.
///
/// The flat arrays keep the pinned hardware layout byte-identical to nested
/// per-bus tables while letting one slot be rewritten in place.  The value
/// must be pinned at `table_base`; copying or moving it after the root entries
/// are initialized would invalidate their embedded addresses.
#[repr(C, align(4096))]
pub struct IommuRootTable {
    root_entries: Array<VtdLegacyEntry, PCI_BUS_COUNT>,
    context_entries: Array<VtdLegacyEntry, PCI_BDF_COUNT>,
    owner_slots: Array<RwLockProcessPtr, PCI_BDF_COUNT>,
    table_base: Ghost<PAddr>,
}

impl IommuRootTable {
    pub fn new_disabled(table_base: PAddr, owner_process: RwLockProcessPtr) -> (ret: Self)
        requires
            table_base % VTD_TABLE_SIZE == 0,
            table_base as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
            table_base as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
            0 < VTD_TABLE_SIZE,
        ensures
            ret.wf(),
            ret.table_base() == table_base,
            forall|bus: usize, device: usize, function: usize|
                #![trigger ret.spec_index_iommu_root(bus, device, function)]
                pci_bdf_valid(bus, device, function) ==> ret.spec_index_iommu_root(bus, device, function) is None,
            forall|bus: usize, device: usize, function: usize|
                #![trigger ret.spec_index_owner(bus, device, function)]
                pci_bdf_valid(bus, device, function) ==> ret.spec_index_owner(bus, device, function) == owner_process,
    {
        let mut root_entries: Array<VtdLegacyEntry, PCI_BUS_COUNT> = Array::new();
        let mut bus = 0;
        while bus < PCI_BUS_COUNT
            invariant
                0 <= bus <= PCI_BUS_COUNT,
                root_entries.wf(),
                table_base % VTD_TABLE_SIZE == 0,
                table_base as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
                table_base as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
                0 < VTD_TABLE_SIZE,
                forall|old_bus: usize|
                    #![trigger root_entries.spec_index(old_bus)]
                    old_bus < bus ==> {
                        let address: usize = (table_base + VTD_TABLE_SIZE * (old_bus + 1)) as usize;
                        &&& root_entries.spec_index(old_bus).lower == (address | 1)
                        &&& root_entries.spec_index(old_bus).upper == 0
                        &&& root_entries.spec_index(old_bus).present()
                        &&& root_entries.spec_index(old_bus).address() == address
                    },
            decreases PCI_BUS_COUNT - bus,
        {
            assert(VTD_TABLE_SIZE as int == 4096) by (compute);
            let context_address = iommu_context_table_address(table_base, bus);
            assert({
                &&& (context_address | 1) & VTD_CONTEXT_ADDRESS_MASK == context_address
                &&& (context_address | 1) & 1 == 1
            }) by (bit_vector)
                requires
                    context_address % VTD_TABLE_SIZE == 0,
                    context_address <= MEM_MASK as usize,
            ;
            root_entries.set(bus, VtdLegacyEntry { lower: context_address | 1, upper: 0 });
            bus = bus + 1;
        }
        let context_entries: Array<VtdLegacyEntry, PCI_BDF_COUNT> = Array::new_with_init_value(VtdLegacyEntry::disabled());
        let owner_slots: Array<RwLockProcessPtr, PCI_BDF_COUNT> = Array::new_with_init_value(owner_process);
        let ret = Self { root_entries, context_entries, owner_slots, table_base: Ghost(table_base) };
        assert(ret.wf()) by { reveal(IommuRootTable::wf); }
        ret
    }

    /// Physical address the table is pinned at; also its lock minor.
    pub closed spec fn table_base(&self) -> PAddr { self.table_base.view() }

    closed spec fn context_table_address(&self, bus: usize) -> PAddr
        recommends
            bus < PCI_BUS_COUNT,
    {
        (self.table_base.view() + VTD_TABLE_SIZE * (bus + 1)) as usize
    }

    /// Logical hardware interface. `None` means the context entry is not
    /// present; `Some(root)` exposes only its second-level page-table root.
    pub closed spec fn iommu_roots(&self) -> Seq3<Option<PageTableRoot>> {
        seq3_from_flat(self.context_entries.view().map_values(|context: VtdLegacyEntry| context.iommu_root()))
    }

    /// Total logical ownership interface. Every BDF slot has a process owner,
    /// independently of whether its context entry is currently present.
    pub closed spec fn owners(&self) -> Seq3<RwLockProcessPtr> { seq3_from_flat(self.owner_slots.view()) }

    /// Logical domain-ID interface. `None` means the context entry is not
    /// present; `Some(did)` exposes the VT-d domain ID the entry carries.
    pub closed spec fn iommu_dids(&self) -> Seq3<Option<VtdDomainId>> {
        seq3_from_flat(self.context_entries.view().map_values(|context: VtdLegacyEntry| context.iommu_did()))
    }

    /// Indexes the logical second-level root selected by one PCI function.
    /// `None` means that the corresponding context entry is not present.
    pub open spec fn spec_index_iommu_root(&self, bus: usize, device: usize, function: usize) -> Option<PageTableRoot>
        recommends
            self.wf(),
            pci_bdf_valid(bus, device, function),
    {
        self.iommu_roots().spec_index(bus as int).spec_index(device as int).spec_index(function as int)
    }

    /// Indexes the VT-d domain ID of one PCI function's context entry.
    /// `None` means that the corresponding context entry is not present.
    pub open spec fn spec_index_iommu_did(&self, bus: usize, device: usize, function: usize) -> Option<VtdDomainId>
        recommends
            self.wf(),
            pci_bdf_valid(bus, device, function),
    {
        self.iommu_dids().spec_index(bus as int).spec_index(device as int).spec_index(function as int)
    }

    /// Indexes the total process owner of one PCI function.
    pub open spec fn spec_index_owner(&self, bus: usize, device: usize, function: usize) -> RwLockProcessPtr
        recommends
            self.wf(),
            pci_bdf_valid(bus, device, function),
    {
        self.owners().spec_index(bus as int).spec_index(device as int).spec_index(function as int)
    }

    #[verifier::opaque]
    pub closed spec fn wf(&self) -> bool {
        &&& self.root_entries.wf()
        &&& self.context_entries.wf()
        &&& self.owner_slots.wf()
        &&& self.table_base.view() % VTD_TABLE_SIZE == 0
        &&& self.table_base.view() <= usize::MAX - IOMMU_ROOT_TABLE_STATIC_SIZE
        &&& forall|bus: usize|
            #![trigger self.root_entries.spec_index(bus)]
            bus < PCI_BUS_COUNT ==> {
                let root = self.root_entries.spec_index(bus);
                &&& root.present()
                &&& root.address() == self.context_table_address(bus)
                &&& root.lower == (self.context_table_address(bus) | 1)
                &&& root.upper == 0
            }
        &&& forall|slot: usize|
            #![trigger self.context_entries.spec_index(slot)]
            slot < PCI_BDF_COUNT ==> {
                let context = self.context_entries.spec_index(slot);
                &&& !context.present() ==> context.lower == 0 && context.upper == 0
                &&& context.present() ==> {
                    &&& context.lower == (context.address() | 1)
                    // TT = 00 blocks ATS translation requests, so no device-TLB is ever populated; the model has no device-TLB state for that reason.
                    &&& context.translation_type() == 0
                    &&& context.address_width() == VTD_CONTEXT_AW_4_LEVEL
                    &&& context.upper == ((context.domain_id() << 8) | VTD_CONTEXT_AW_4_LEVEL)
                }
            }
    }

    /// A present context entry carries both a root and a valid domain ID.
    pub proof fn context_wf_at(&self, bus: usize, device: usize, function: usize)
        requires
            self.wf(),
            pci_bdf_valid(bus, device, function),
        ensures
            self.spec_index_iommu_did(bus, device, function) is Some == self.spec_index_iommu_root(bus, device, function) is Some,
            self.spec_index_iommu_did(bus, device, function) is Some ==> vtd_domain_id_valid(self.spec_index_iommu_did(bus, device, function)->0),
    {
        reveal(IommuRootTable::wf);
        assert(bus * PCI_DEVFN_COUNT + device * PCI_FUNCTION_COUNT + function < PCI_BDF_COUNT) by (nonlinear_arith)
            requires
                pci_bdf_valid(bus, device, function),
        ;
        let upper = self.context_entries.spec_index(pci_bdf_did(bus, device, function)).upper;
        assert((upper >> 8) & VTD_CONTEXT_DID_MASK < 65536) by (bit_vector);
    }

    /// The context-entry array of `wf` has one entry per B/D/F.
    proof fn wf_len_at(&self)
        requires self.wf()
        ensures self.context_entries.wf()
    { reveal(IommuRootTable::wf); }

    /// Trusted store boundary: publishes context entry `slot` with two aligned
    /// volatile 64-bit stores, `upper` (DID/AW) first and `lower` (root|P) last,
    /// so a remapping unit never observes P with a stale upper word.
    #[verifier::external_body]
    fn publish_context_entry(&mut self, slot: usize, lower: usize, upper: usize)
        requires
            old(self).context_entries.wf(),
            slot < PCI_BDF_COUNT,
        ensures
            final(self).context_entries.view() == old(self).context_entries.view().update(slot as int, VtdLegacyEntry { lower, upper }),
            final(self).root_entries == old(self).root_entries,
            final(self).owner_slots == old(self).owner_slots,
            final(self).table_base == old(self).table_base,
    {
        let entry = &mut self.context_entries.ar[slot];
        unsafe { core::ptr::write_volatile(&mut entry.upper as *mut usize, upper); }
        unsafe { core::ptr::write_volatile(&mut entry.lower as *mut usize, lower); }
    }

    /// Trusted store boundary: clears context entry `slot` with two aligned
    /// volatile 64-bit stores, the P-containing `lower` word first, then `upper`.
    #[verifier::external_body]
    fn clear_context_entry(&mut self, slot: usize)
        requires
            old(self).context_entries.wf(),
            slot < PCI_BDF_COUNT,
        ensures
            final(self).context_entries.view() == old(self).context_entries.view().update(slot as int, VtdLegacyEntry { lower: 0, upper: 0 }),
            final(self).root_entries == old(self).root_entries,
            final(self).owner_slots == old(self).owner_slots,
            final(self).table_base == old(self).table_base,
    {
        let entry = &mut self.context_entries.ar[slot];
        unsafe { core::ptr::write_volatile(&mut entry.lower as *mut usize, 0); }
        unsafe { core::ptr::write_volatile(&mut entry.upper as *mut usize, 0); }
    }

    /// Flat slot of one B/D/F, shared by the context entries and the owner slots.
    pub fn pci_bdf_slot(bus: usize, device: usize, function: usize) -> (ret: usize)
        requires
            pci_bdf_valid(bus, device, function),
        ensures
            ret == pci_bdf_did(bus, device, function),
            ret < PCI_BDF_COUNT,
            pci_bdf_of_did(ret) == (bus, device, function),
    {
        bus * PCI_DEVFN_COUNT + device * PCI_FUNCTION_COUNT + function
    }

    /// The B/D/F whose candidate DID is `did`.
    pub fn did_pci_bdf(did: VtdDomainId) -> (ret: PciBdf)
        requires
            vtd_domain_id_valid(did),
        ensures
            ret == pci_bdf_of_did(did),
            pci_bdf_valid(ret.0, ret.1, ret.2),
            pci_bdf_did(ret.0, ret.1, ret.2) == did,
    {
        (did / PCI_DEVFN_COUNT, (did % PCI_DEVFN_COUNT) / PCI_FUNCTION_COUNT, did % PCI_FUNCTION_COUNT)
    }

    pub fn owner(&self, bus: usize, device: usize, function: usize) -> (ret: RwLockProcessPtr)
        requires
            self.wf(),
            pci_bdf_valid(bus, device, function),
        ensures
            ret == self.spec_index_owner(bus, device, function),
    {
        proof { reveal(IommuRootTable::wf); }
        *self.owner_slots.get(Self::pci_bdf_slot(bus, device, function))
    }

    /// Whether the context entry of one B/D/F is present, i.e. DMA translation is attached.
    pub fn is_attached(&self, bus: usize, device: usize, function: usize) -> (ret: bool)
        requires
            self.wf(),
            pci_bdf_valid(bus, device, function),
        ensures
            ret == self.spec_index_iommu_root(bus, device, function) is Some,
    {
        proof { reveal(IommuRootTable::wf); }
        self.context_entries.get(Self::pci_bdf_slot(bus, device, function)).lower & 1 == 1
    }

    /// The VT-d domain ID of one B/D/F's context entry, `None` if not present.
    pub fn iommu_did(&self, bus: usize, device: usize, function: usize) -> (ret: Option<VtdDomainId>)
        requires
            self.wf(),
            pci_bdf_valid(bus, device, function),
        ensures
            ret == self.spec_index_iommu_did(bus, device, function),
            ret is Some ==> vtd_domain_id_valid(ret->0),
    {
        proof { assert(self.context_entries.wf()) by { self.wf_len_at(); }; }
        let context = self.context_entries.get(Self::pci_bdf_slot(bus, device, function));
        proof {
            let upper = context.upper;
            assert((upper >> 8) & VTD_CONTEXT_DID_MASK < 65536) by (bit_vector);
        }
        if context.lower & 1 == 1 { Some((context.upper >> 8) & VTD_CONTEXT_DID_MASK) } else { None }
    }

    /// Hands the B/D/F slot to `owner`; the context entry is untouched.
    pub fn set_owner(&mut self, bus: usize, device: usize, function: usize, owner: RwLockProcessPtr)
        requires
            old(self).wf(),
            pci_bdf_valid(bus, device, function),
        ensures
            final(self).wf(),
            final(self).table_base() == old(self).table_base(),
            final(self).iommu_roots() == old(self).iommu_roots(),
            final(self).iommu_dids() == old(self).iommu_dids(),
            final(self).owners() == seq3_update(old(self).owners(), bus as int, device as int, function as int, owner),
            forall|b: usize, d: usize, f: usize| #![trigger final(self).spec_index_owner(b, d, f)] #![trigger final(self).spec_index_iommu_root(b, d, f)]
                #![trigger final(self).spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                &&& final(self).spec_index_owner(b, d, f) == if (b, d, f) == (bus, device, function) { owner } else { old(self).spec_index_owner(b, d, f) }
                &&& final(self).spec_index_iommu_root(b, d, f) == old(self).spec_index_iommu_root(b, d, f)
                &&& final(self).spec_index_iommu_did(b, d, f) == old(self).spec_index_iommu_did(b, d, f)
            },
    {
        proof { reveal(IommuRootTable::wf); }
        self.owner_slots.set(Self::pci_bdf_slot(bus, device, function), owner);
        proof {
            let pre = old(self).owners();
            let post = seq3_update(pre, bus as int, device as int, function as int, owner);
            assert_seqs_equal!(self.owners() == post, b => {
                assert_seqs_equal!(self.owners()[b] == post[b], d => {
                    assert_seqs_equal!(self.owners()[b][d] == post[b][d], f => {});
                });
            });
        }
    }

    /// Clears the context entry of one B/D/F so the device no longer translates.
    pub fn detach(&mut self, bus: usize, device: usize, function: usize)
        requires
            old(self).wf(),
            pci_bdf_valid(bus, device, function),
        ensures
            final(self).wf(),
            final(self).table_base() == old(self).table_base(),
            final(self).owners() == old(self).owners(),
            final(self).iommu_roots() == seq3_update(old(self).iommu_roots(), bus as int, device as int, function as int, None),
            final(self).iommu_dids() == seq3_update(old(self).iommu_dids(), bus as int, device as int, function as int, None),
            forall|b: usize, d: usize, f: usize| #![trigger final(self).spec_index_owner(b, d, f)] #![trigger final(self).spec_index_iommu_root(b, d, f)]
                #![trigger final(self).spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                &&& final(self).spec_index_owner(b, d, f) == old(self).spec_index_owner(b, d, f)
                &&& final(self).spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { None } else { old(self).spec_index_iommu_root(b, d, f) }
                &&& final(self).spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { None } else { old(self).spec_index_iommu_did(b, d, f) }
            },
    {
        proof { reveal(IommuRootTable::wf); }
        self.clear_context_entry(Self::pci_bdf_slot(bus, device, function));
        assert(0usize & 1usize != 1usize) by (bit_vector);
        proof {
            let pre = old(self).iommu_roots();
            let pre_dids = old(self).iommu_dids();
            let post = seq3_update(pre, bus as int, device as int, function as int, None);
            let post_dids = seq3_update(pre_dids, bus as int, device as int, function as int, None);
            assert_seqs_equal!(self.iommu_roots() == post, b => {
                assert_seqs_equal!(self.iommu_roots()[b] == post[b], d => {
                    assert_seqs_equal!(self.iommu_roots()[b][d] == post[b][d], f => {});
                });
            });
            assert_seqs_equal!(self.iommu_dids() == post_dids, b => {
                assert_seqs_equal!(self.iommu_dids()[b] == post_dids[b], d => {
                    assert_seqs_equal!(self.iommu_dids()[b][d] == post_dids[b][d], f => {});
                });
            });
        }
    }

    /// Points the absent context entry of one B/D/F at the 4-level
    /// second-stage root `root`, in VT-d domain `did`.
    pub fn attach(&mut self, bus: usize, device: usize, function: usize, root: PageTableRoot, did: VtdDomainId)
        requires
            old(self).wf(),
            pci_bdf_valid(bus, device, function),
            page_ptr_valid(root),
            vtd_domain_id_valid(did),
            old(self).spec_index_iommu_root(bus, device, function) is None,
        ensures
            final(self).wf(),
            final(self).table_base() == old(self).table_base(),
            final(self).owners() == old(self).owners(),
            final(self).iommu_roots() == seq3_update(old(self).iommu_roots(), bus as int, device as int, function as int, Some(root)),
            final(self).iommu_dids() == seq3_update(old(self).iommu_dids(), bus as int, device as int, function as int, Some(did)),
            forall|b: usize, d: usize, f: usize| #![trigger final(self).spec_index_owner(b, d, f)] #![trigger final(self).spec_index_iommu_root(b, d, f)]
                #![trigger final(self).spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                &&& final(self).spec_index_owner(b, d, f) == old(self).spec_index_owner(b, d, f)
                &&& final(self).spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { Some(root) } else { old(self).spec_index_iommu_root(b, d, f) }
                &&& final(self).spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { Some(did) } else { old(self).spec_index_iommu_did(b, d, f) }
            },
    {
        proof { reveal(IommuRootTable::wf); }
        assert({
            &&& (root | 1) & 1 == 1
            &&& (root | 1) & VTD_CONTEXT_ADDRESS_MASK == root
            &&& ((root | 1) >> 2) & VTD_CONTEXT_TRANSLATION_TYPE_MASK == 0
            &&& ((did << 8) | VTD_CONTEXT_AW_4_LEVEL) & VTD_CONTEXT_ADDRESS_WIDTH_MASK == VTD_CONTEXT_AW_4_LEVEL
            &&& (((did << 8) | VTD_CONTEXT_AW_4_LEVEL) >> 8) & VTD_CONTEXT_DID_MASK == did
        }) by (bit_vector)
            requires
                root % 4096 == 0,
                root / 4096 < 2 * 1024 * 1024,
                did < 65536,
        ;
        self.publish_context_entry(Self::pci_bdf_slot(bus, device, function), root | 1, (did << 8) | VTD_CONTEXT_AW_4_LEVEL);
        proof {
            let pre = old(self).iommu_roots();
            let pre_dids = old(self).iommu_dids();
            let post = seq3_update(pre, bus as int, device as int, function as int, Some(root));
            let post_dids = seq3_update(pre_dids, bus as int, device as int, function as int, Some(did));
            assert_seqs_equal!(self.iommu_roots() == post, b => {
                assert_seqs_equal!(self.iommu_roots()[b] == post[b], d => {
                    assert_seqs_equal!(self.iommu_roots()[b][d] == post[b][d], f => {});
                });
            });
            assert_seqs_equal!(self.iommu_dids() == post_dids, b => {
                assert_seqs_equal!(self.iommu_dids()[b] == post_dids[b], d => {
                    assert_seqs_equal!(self.iommu_dids()[b][d] == post_dids[b][d], f => {});
                });
            });
        }
    }

    /// The lexicographically first B/D/F other than `removed` that `owner` owns and whose present context entry carries `did`.
    pub fn first_attached_owned(&self, owner: RwLockProcessPtr, did: VtdDomainId, removed: Option<PciBdf>) -> (ret: Option<PciBdf>)
        requires
            self.wf(),
        ensures
            ret matches Some(bdf) ==> {
                &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
                &&& Some(bdf) != removed
                &&& self.spec_index_owner(bdf.0, bdf.1, bdf.2) == owner
                &&& self.spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == Some(did)
            },
            forall|b: usize, d: usize, f: usize| #![trigger self.spec_index_owner(b, d, f)] #![trigger self.spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) && (ret is None || pci_bdf_lt((b, d, f), ret.unwrap())) && Some((b, d, f)) != removed && self.spec_index_owner(b, d, f) == owner
                ==> self.spec_index_iommu_did(b, d, f) != Some(did),
            forall|b: usize, d: usize, f: usize| #![trigger self.spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) ==> (self.spec_index_iommu_did(b, d, f) is Some) == (self.spec_index_iommu_root(b, d, f) is Some),
    {
        proof { assert(self.context_entries.view().len() == PCI_BDF_COUNT) by { self.wf_len_at(); }; }
        let mut bus: usize = 0;
        let mut device: usize = 0;
        let mut function: usize = 0;
        while bus < PCI_BUS_COUNT
            invariant
                self.wf(),
                self.context_entries.view().len() == PCI_BDF_COUNT,
                bus <= PCI_BUS_COUNT,
                device < PCI_DEVICE_COUNT,
                function < PCI_FUNCTION_COUNT,
                bus == PCI_BUS_COUNT ==> device == 0 && function == 0,
                forall|b: usize, d: usize, f: usize| #![trigger self.spec_index_owner(b, d, f)] #![trigger self.spec_index_iommu_did(b, d, f)]
                    pci_bdf_valid(b, d, f) && pci_bdf_lt((b, d, f), (bus, device, function)) && Some((b, d, f)) != removed && self.spec_index_owner(b, d, f) == owner
                    ==> self.spec_index_iommu_did(b, d, f) != Some(did),
            decreases PCI_BUS_COUNT - bus, PCI_DEVICE_COUNT - device, PCI_FUNCTION_COUNT - function,
        {
            let is_removed = match removed { Some(r) => r.0 == bus && r.1 == device && r.2 == function, None => false };
            if !is_removed && self.owner(bus, device, function) == owner {
                let current = self.iommu_did(bus, device, function);
                if current.is_some() && current.unwrap() == did { return Some((bus, device, function)); }
            }
            if function + 1 < PCI_FUNCTION_COUNT {
                function = function + 1;
            } else if device + 1 < PCI_DEVICE_COUNT {
                function = 0;
                device = device + 1;
            } else {
                function = 0;
                device = 0;
                bus = bus + 1;
            }
        }
        None
    }

    /// Clears the context entry of every B/D/F that `owner` owns and hands its slot to `recipient`; other slots are untouched.
    pub fn detach_owned_contexts(&mut self, owner: RwLockProcessPtr, recipient: RwLockProcessPtr)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).table_base() == old(self).table_base(),
            owner == recipient ==> final(self).owners() == old(self).owners(),
            forall|b: usize, d: usize, f: usize| #![trigger old(self).spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) ==> (old(self).spec_index_iommu_did(b, d, f) is Some) == (old(self).spec_index_iommu_root(b, d, f) is Some),
            forall|b: usize, d: usize, f: usize| #![trigger final(self).spec_index_owner(b, d, f)] #![trigger final(self).spec_index_iommu_root(b, d, f)]
                #![trigger final(self).spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                let owned = old(self).spec_index_owner(b, d, f) == owner;
                &&& final(self).spec_index_owner(b, d, f) == if owned { recipient } else { old(self).spec_index_owner(b, d, f) }
                &&& final(self).spec_index_iommu_root(b, d, f) == if owned { None } else { old(self).spec_index_iommu_root(b, d, f) }
                &&& final(self).spec_index_iommu_did(b, d, f) == if owned { None } else { old(self).spec_index_iommu_did(b, d, f) }
            },
    {
        let mut bus: usize = 0;
        let mut device: usize = 0;
        let mut function: usize = 0;
        while bus < PCI_BUS_COUNT
            invariant
                self.wf(),
                self.table_base() == old(self).table_base(),
                owner == recipient ==> self.owners() == old(self).owners(),
                bus <= PCI_BUS_COUNT,
                device < PCI_DEVICE_COUNT,
                function < PCI_FUNCTION_COUNT,
                bus == PCI_BUS_COUNT ==> device == 0 && function == 0,
                forall|b: usize, d: usize, f: usize| #![trigger self.spec_index_owner(b, d, f)] #![trigger self.spec_index_iommu_root(b, d, f)]
                    #![trigger self.spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                    let owned = pci_bdf_lt((b, d, f), (bus, device, function)) && old(self).spec_index_owner(b, d, f) == owner;
                    &&& self.spec_index_owner(b, d, f) == if owned { recipient } else { old(self).spec_index_owner(b, d, f) }
                    &&& self.spec_index_iommu_root(b, d, f) == if owned { None } else { old(self).spec_index_iommu_root(b, d, f) }
                    &&& self.spec_index_iommu_did(b, d, f) == if owned { None } else { old(self).spec_index_iommu_did(b, d, f) }
                },
            decreases PCI_BUS_COUNT - bus, PCI_DEVICE_COUNT - device, PCI_FUNCTION_COUNT - function,
        {
            if self.owner(bus, device, function) == owner {
                self.detach(bus, device, function);
                if recipient != owner { self.set_owner(bus, device, function, recipient); }
            }
            if function + 1 < PCI_FUNCTION_COUNT {
                function = function + 1;
            } else if device + 1 < PCI_DEVICE_COUNT {
                function = 0;
                device = device + 1;
            } else {
                function = 0;
                device = 0;
                bus = bus + 1;
            }
        }
        proof { assert(old(self).context_entries.view().len() == PCI_BDF_COUNT) by { old(self).wf_len_at(); }; }
    }
}

/// The whole table is one lock; its payload is pinned one 4K page after the
/// lock word, so `table_base` is the lock's `#[repr(C)]` value offset.
pub type IommuRootTableLock = RwLock<IommuRootTable, (), (), NO_KILL_STATE>;

impl LockInvTrait for IommuRootTable {
    open spec fn inv(&self) -> bool { self.wf() }
}

impl LockOwnerIdTrait for IommuRootTable {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::None }
}

impl LockMajorTrait for IommuRootTable {
    open spec fn lock_major_1(&self) -> LockMajorId { IOMMU_ROOT_TABLE_LOCK_MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { IOMMU_ROOT_TABLE_LOCK_MAJOR }
    open spec fn lock_major_3(&self) -> LockMajorId { IOMMU_ROOT_TABLE_LOCK_MAJOR }
    open spec fn lock_major_default(&self) -> LockMajorId { IOMMU_ROOT_TABLE_LOCK_MAJOR }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl LockMinorTrait for IommuRootTable {
    open spec fn lock_minor(&self) -> LockMinorId { seq![self.table_base()] }
}

impl LockIdTrait for IommuRootTable {
    open spec fn lock_id(&self) -> LockId {
        LockId { container: LockOwnerId::None, process: LockOwnerId::None, major: IOMMU_ROOT_TABLE_LOCK_MAJOR, minor: seq![self.table_base()] }
    }
}

/// Held-lock alignment of the single root-table lock, keyed by its table base.
#[verifier::opaque]
pub open spec fn iommu_root_table_typed_lock_map_aligned(lock: IommuRootTableLock, held_locks: Map<PAddr, TypedHeldLock>, thread_id: LockThreadId) -> bool {
    &&& forall|table_base: PAddr| #![trigger held_locks.dom().contains(table_base)] held_locks.dom().contains(table_base) ==> {
        &&& table_base == lock.view().table_base()
        &&& lock.wlocked_by_thread(thread_id)
        &&& held_locks.index(table_base).lock_id == lock.lock_id()
        &&& held_locks.index(table_base).mode is Write
    }
    &&& lock.locked_by_thread(thread_id) ==> held_locks.dom().contains(lock.view().table_base())
}
}

// Compile-time checks for the hardware layout and the stated memory budget.
// The lock word occupies the page before the pinned table.
const ASSERT_IOMMU_ROOT_TABLE_LOCK_SIZE: [(); VTD_TABLE_SIZE + IOMMU_ROOT_TABLE_STATIC_SIZE] = [(); core::mem::size_of::<IommuRootTableLock>()];
const ASSERT_VTD_ENTRY_SIZE: [(); VTD_ENTRY_SIZE] = [(); core::mem::size_of::<VtdLegacyEntry>()];
// Each context-entry word is one aligned 64-bit store: `lower` at offset 0, `upper` at offset 8.
const ASSERT_VTD_ENTRY_WORD_SIZE: [(); 8] = [(); core::mem::size_of::<usize>()];
const ASSERT_VTD_ENTRY_ALIGNMENT: [(); 8] = [(); core::mem::align_of::<VtdLegacyEntry>()];
const ASSERT_VTD_ENTRY_UPPER_OFFSET: [(); 8] = [(); core::mem::offset_of!(VtdLegacyEntry, upper)];
const ASSERT_IOMMU_CONTEXT_ENTRIES_SIZE: [(); PCI_BUS_COUNT * VTD_TABLE_SIZE] = [(); core::mem::size_of::<Array<VtdLegacyEntry, PCI_BDF_COUNT>>()];
const ASSERT_IOMMU_CONTEXT_ENTRIES_OFFSET: [(); VTD_TABLE_SIZE] = [(); core::mem::offset_of!(IommuRootTable, context_entries)];
const ASSERT_IOMMU_OWNER_SLOTS_OFFSET: [(); IOMMU_ROOT_TABLE_HARDWARE_PAGES * VTD_TABLE_SIZE] = [(); core::mem::offset_of!(IommuRootTable, owner_slots)];
const ASSERT_IOMMU_ROOT_TABLE_SIZE: [(); IOMMU_ROOT_TABLE_STATIC_SIZE] = [(); core::mem::size_of::<IommuRootTable>()];
const ASSERT_IOMMU_ROOT_TABLE_ALIGNMENT: [(); VTD_TABLE_SIZE] = [(); core::mem::align_of::<IommuRootTable>()];

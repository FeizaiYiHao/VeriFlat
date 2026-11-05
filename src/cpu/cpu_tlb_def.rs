use vstd::prelude::*;

use crate::*;
use super::cpu_cr3_pcid::CpuCr3Pcid;

verus! {
/// Cached translations, shared by the CPU TLBs and the IOTLB. Only the IOTLB folds its paging-structure caches in; a CPU
/// keeps them in `PagingStructureCache`. A 2M translation the hardware splits into 4K TLB entries is represented by its
/// `tlb_2m` entry keyed by the 2M base: a PCID- or domain-wide invalidation drops every split entry, and an INVPCID
/// individual-address invalidation of any address inside a large page drops every entry of that page (Intel SDM), so
/// the split is not observable.
/// One past the last of the `count` addresses, 4K apart or 2M apart by `stride_2m`, that a per-address flush from `va` names.
pub open spec fn va_range_flush_end(va: VAddr, count: usize, stride_2m: bool) -> int { va as int + count as int * (if stride_2m { 0x200000int } else { 4096int }) }

/// A per-address flush of `count` pages from `va` drops the 4K translation at `x`: the flush is 4K apart and names `x`.
pub open spec fn va_range_flush_drops_4k(va: VAddr, count: usize, stride_2m: bool, x: VAddr) -> bool {
    !stride_2m && spec_va_4k_valid(x) && va <= x && (x as int) < va_range_flush_end(va, count, stride_2m)
}

/// A per-address flush of `count` pages from `va` drops the 2M translation at `x`: it names an address in that 2M page.
pub open spec fn va_range_flush_drops_2m(va: VAddr, count: usize, stride_2m: bool, x: VAddr) -> bool {
    spec_va_2m_valid(x) && (va as int) < x as int + 0x200000 && (x as int) < va_range_flush_end(va, count, stride_2m)
}

/// A per-address flush of `count` pages from `va` drops the 1G translation at `x`: it names an address in that 1G page.
pub open spec fn va_range_flush_drops_1g(va: VAddr, count: usize, stride_2m: bool, x: VAddr) -> bool {
    spec_va_1g_valid(x) && (va as int) < x as int + 0x40000000 && (x as int) < va_range_flush_end(va, count, stride_2m)
}

/// Every translation `tlb` caches is one `old_tlb` caches alike that a per-address flush of `count` pages from `va` does
/// not drop: the TLB of one `(cpu, pcid)` right after such a flush when its walker cannot refill it.
pub open spec fn single_tlb_va_range_flushed_kept(old_tlb: SingleTLB, tlb: SingleTLB, va: VAddr, count: usize, stride_2m: bool) -> bool {
    &&& forall|x: VAddr| #![trigger tlb.tlb_4k().dom().contains(x)] #![trigger tlb.tlb_4k().spec_index(x)] tlb.tlb_4k().dom().contains(x)
        ==> !va_range_flush_drops_4k(va, count, stride_2m, x) && old_tlb.tlb_4k().contains_pair(x, tlb.tlb_4k().spec_index(x))
    &&& forall|x: VAddr| #![trigger tlb.tlb_2m().dom().contains(x)] #![trigger tlb.tlb_2m().spec_index(x)] tlb.tlb_2m().dom().contains(x)
        ==> !va_range_flush_drops_2m(va, count, stride_2m, x) && old_tlb.tlb_2m().contains_pair(x, tlb.tlb_2m().spec_index(x))
    &&& forall|x: VAddr| #![trigger tlb.tlb_1g().dom().contains(x)] #![trigger tlb.tlb_1g().spec_index(x)] tlb.tlb_1g().dom().contains(x)
        ==> !va_range_flush_drops_1g(va, count, stride_2m, x) && old_tlb.tlb_1g().contains_pair(x, tlb.tlb_1g().spec_index(x))
}

pub ghost struct SingleTLB {
    pub tlb_4k: Map<VAddr, TLBEntry>,
    pub tlb_2m: Map<VAddr, TLBEntry>,
    pub tlb_1g: Map<VAddr, TLBEntry>,
}

impl SingleTLB {
    pub open spec fn tlb_4k(&self) -> Map<VAddr, TLBEntry> { self.tlb_4k }
    pub open spec fn tlb_2m(&self) -> Map<VAddr, TLBEntry> { self.tlb_2m }
    pub open spec fn tlb_1g(&self) -> Map<VAddr, TLBEntry> { self.tlb_1g }

    pub open spec fn is_empty(&self) -> bool {
        &&& self.tlb_4k().dom() == Set::<VAddr>::empty()
        &&& self.tlb_2m().dom() == Set::<VAddr>::empty()
        &&& self.tlb_1g().dom() == Set::<VAddr>::empty()
    }
}

/// K only, never projected into U: the user-half directory entries the page walker of one `(cpu, pcid)` remembers.
/// `pml4e` maps VA bits 47:39 to an L3 page, `pdpte` bits 47:30 to an L2 page, and `pde` bits 47:21, one 2M window, to
/// an L1 page.
pub ghost struct PagingStructureCache {
    pub pml4e: Map<L4Index, PageMapPtr>,
    pub pdpte: Map<(L4Index, L3Index), PageMapPtr>,
    pub pde: Map<(L4Index, L3Index, L2Index), PageMapPtr>,
}

impl PagingStructureCache {
    /// No directory entry is remembered.
    pub open spec fn is_empty(&self) -> bool {
        &&& self.pml4e.dom() == Set::<L4Index>::empty()
        &&& self.pdpte.dom() == Set::<(L4Index, L3Index)>::empty()
        &&& self.pde.dom() == Set::<(L4Index, L3Index, L2Index)>::empty()
    }
}

pub struct CpuTLB {
    pub cpu_tlbs: Ghost<Map<(CpuId, Pcid), SingleTLB>>,
    pub structure_caches: Ghost<Map<(CpuId, Pcid), PagingStructureCache>>,
}

impl CpuTLB {
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.inv(),
            forall|cpu_id: CpuId, pcid: Pcid| #![trigger ret.spec_index((cpu_id, pcid))] index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> ret.spec_index((cpu_id, pcid)).is_empty(),
            forall|cpu_id: CpuId, pcid: Pcid| #![trigger ret.structure_cache((cpu_id, pcid))] index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> ret.structure_cache((cpu_id, pcid)).is_empty(),
    {
        let ghost cpu_ids = Set::range(0usize, NUM_CPUS);
        let ghost pcids = Set::range(0usize, PCID_MAX);
        let ghost pcids_for_cpu = |cpu_id: CpuId| { pcids.map_by(|pcid: Pcid| (cpu_id, pcid), |key: (CpuId, Pcid)| key.1) };
        let ghost keys = cpu_ids.map_flatten_by(pcids_for_cpu, |key: (CpuId, Pcid)| key.0);
        let ret = Self {
            cpu_tlbs: Ghost(Map::new(keys, |_key: (CpuId, Pcid)| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })),
            structure_caches: Ghost(Map::new(keys, |_key: (CpuId, Pcid)| PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() })),
        };
        assert(ret.inv()) by { reveal(CpuTLB::inv); };
        ret
    }

    /// PCIDE is enabled by boot. Non-default translations are non-global.
    /// The caller binds `cpu_id` to this executing CPU; kernel mappings stay
    /// accessible across the write. Bit 63 requests retention of translations.
    /// The walker may refill a flushed `(cpu_id, pcid)` at once, but only with present leaves and present directory entries
    /// of `next_table`, the table of `k` that `cr3` roots; a write naming no tracked table leaves it empty.
    #[verifier::external_body]
    pub(super) fn write_cr3_pcid(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, flush: bool, hardware: &mut CpuCr3Pcid, Ghost(k): Ghost<KernelK>,
        Ghost(next_table): Ghost<Option<RwLockPageTableRoot>>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            lctx.kernel_view_locking_state() is Release,
            next_table matches Some(ptr) ==> k.pt_mp.dom().contains(ptr) && k.pt_mp.spec_index(ptr).view().cr3 == cr3,
        ensures
            final(self).inv(),
            final(hardware).cr3() == cr3,
            final(hardware).pcid() == pcid,
            final(hardware).current_cr3 == old(hardware).current_cr3,
            final(hardware).current_pcid == old(hardware).current_pcid,
            !flush ==> *final(self) == *old(self),
            forall|other_cpu: CpuId, other_pcid: Pcid|
                #![trigger final(self).spec_index((other_cpu, other_pcid))]
                #![trigger old(self).spec_index((other_cpu, other_pcid))]
                #![trigger final(self).structure_cache((other_cpu, other_pcid))]
                #![trigger old(self).structure_cache((other_cpu, other_pcid))]
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) && (other_cpu != cpu_id || other_pcid != pcid)
                    ==> final(self).spec_index((other_cpu, other_pcid)) == old(self).spec_index((other_cpu, other_pcid))
                    && final(self).structure_cache((other_cpu, other_pcid)) == old(self).structure_cache((other_cpu, other_pcid)),
            final(self).view() == if flush { old(self).view().insert((cpu_id, pcid), final(self).spec_index((cpu_id, pcid))) } else { old(self).view() },
            final(self).structure_caches.view() == if flush {
                old(self).structure_caches.view().insert((cpu_id, pcid), final(self).structure_cache((cpu_id, pcid)))
            } else { old(self).structure_caches.view() },
            flush ==> match next_table {
                Some(ptr) => single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).spec_index((cpu_id, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), ptr))
                    && single_structure_cache_subset_of_present_pagetable(final(self).structure_cache((cpu_id, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), ptr)),
                None => final(self).spec_index((cpu_id, pcid)).is_empty() && final(self).structure_cache((cpu_id, pcid)).is_empty(),
            },
    {
        let value = cr3 | pcid | if flush { 0 } else { PCID_ENABLE_MASK };
        unsafe { core::arch::asm!("mov cr3, {}", in(reg) value, options(nostack, preserves_flags)); }
        hardware.hardware = Ghost((cr3, pcid));
        if flush {
            self.cpu_tlbs = Ghost(self.cpu_tlbs.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
            self.structure_caches = Ghost(self.structure_caches.view().insert((cpu_id, pcid), PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }));
        }
    }

    pub closed spec fn view(&self) -> Map<(CpuId, Pcid), SingleTLB> { self.cpu_tlbs.view() }
    pub open spec fn spec_index(&self, index: (CpuId, Pcid)) -> SingleTLB
        recommends
            index_valid(NUM_CPUS, index.0),
            pcid_valid(index.1)
    {
        self.view().spec_index((index.0, index.1))
    }

    /// The paging-structure cache of `(cpu, pcid)`; K only.
    #[verifier::inline]
    pub open spec fn structure_cache(&self, index: (CpuId, Pcid)) -> PagingStructureCache { self.structure_caches.view().spec_index(index) }

    /// One TLB and one structure cache per valid (cpu, pcid).
    #[verifier::opaque]
    pub open spec fn inv(&self) -> bool {
        &&& forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger self.view().dom().contains((cpu_id, pcid))]
            self.view().dom().contains((cpu_id, pcid)) <==> index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid)
        &&& self.structure_caches.view().dom() == self.view().dom()
    }
}
}

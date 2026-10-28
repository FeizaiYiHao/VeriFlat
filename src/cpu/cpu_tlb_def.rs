use vstd::prelude::*;

use crate::*;
use super::cpu_cr3_pcid::CpuCr3Pcid;

verus! {
/// Paging-structure caches are folded in: every modeled invalidation is PCID- or domain-wide and also clears them; shared by the CPU TLBs and the IOTLB.
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
pub struct CpuTLB {
    pub cpu_tlbs: Ghost<Map<(CpuId, Pcid), SingleTLB>>,
}

impl CpuTLB {
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.inv(),
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger ret.spec_index((cpu_id, pcid))]
                index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> ret.spec_index((cpu_id, pcid)).is_empty(),
    {
        let ghost cpu_ids = Set::range(0usize, NUM_CPUS);
        let ghost pcids = Set::range(0usize, PCID_MAX);
        let ghost pcids_for_cpu = |cpu_id: CpuId| { pcids.map_by(|pcid: Pcid| (cpu_id, pcid), |key: (CpuId, Pcid)| key.1) };
        let ghost keys = cpu_ids.map_flatten_by(pcids_for_cpu, |key: (CpuId, Pcid)| key.0);
        let ret = Self { cpu_tlbs: Ghost(Map::new(keys, |_key: (CpuId, Pcid)| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })) };
        assert(ret.inv()) by { reveal(CpuTLB::inv); };
        ret
    }

    /// PCIDE is enabled by boot. Non-default translations are non-global.
    /// The caller binds `cpu_id` to this executing CPU; kernel mappings stay
    /// accessible across the write. Bit 63 requests retention of translations.
    /// The walker may refill a flushed `(cpu_id, pcid)` at once, but only with present leaves of `next_table`, the table of
    /// `k` that `cr3` roots; a write naming no tracked table leaves it empty.
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
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) && (other_cpu != cpu_id || other_pcid != pcid)
                    ==> final(self).spec_index((other_cpu, other_pcid)) == old(self).spec_index((other_cpu, other_pcid)),
            final(self).view() == if flush { old(self).view().insert((cpu_id, pcid), final(self).spec_index((cpu_id, pcid))) } else { old(self).view() },
            flush ==> match next_table {
                Some(ptr) => single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).spec_index((cpu_id, pcid)), pagetable_c(k.pt_mp, k.pt_lower.view(), ptr)),
                None => final(self).spec_index((cpu_id, pcid)).is_empty(),
            },
    {
        let value = cr3 | pcid | if flush { 0 } else { PCID_ENABLE_MASK };
        unsafe { core::arch::asm!("mov cr3, {}", in(reg) value, options(nostack, preserves_flags)); }
        hardware.hardware = Ghost((cr3, pcid));
        if flush {
            self.cpu_tlbs = Ghost(self.cpu_tlbs.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
        }
    }

    pub closed spec fn view(&self) -> Map<(CpuId, Pcid), SingleTLB> { self.cpu_tlbs.view() }
    pub open spec fn spec_index(&self, index: (CpuId, Pcid)) -> SingleTLB
        recommends
            index_valid(NUM_CPUS, index.0),
            usize_in_range::<PCID_MAX>(index.1)
    {
        self.view().spec_index((index.0, index.1))
    }
    #[verifier::opaque]
    pub open spec fn inv(&self) -> bool {
        &&& forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger self.view().dom().contains((cpu_id, pcid))]
            self.view().dom().contains((cpu_id, pcid)) <==> index_valid(NUM_CPUS, cpu_id) && usize_in_range::<PCID_MAX>(pcid)
    }
}
}

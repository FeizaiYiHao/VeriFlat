use vstd::prelude::*;
use crate::*;

// Platform implementation: send an NMI, invalidate the specified non-global
// PCID on the target CPU without taking locks, and wait for completion.
unsafe extern "C" {
    fn veriflat_remote_flush_pcid(cpu_id: usize, pcid: usize);
    fn veriflat_local_flush_all_pcids();
}

verus! {
impl CpuTLB {
    #[verifier::external_body]
    pub fn flush_remote_pcid(&mut self, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != lctx.cpu_id(),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            final(self).spec_index((cpu_id, pcid)).is_empty(),
            forall|c: CpuId, p: Pcid| #![trigger final(self).spec_index((c, p))] #![trigger old(self).spec_index((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(self).spec_index((c, p)) == old(self).spec_index((c, p)),
    {
        unsafe { veriflat_remote_flush_pcid(cpu_id, pcid); }
        self.cpu_tlbs = Ghost(self.cpu_tlbs.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
    }

    /// Invalidate every non-default PCID of the calling cpu before it goes Off.
    #[verifier::external_body]
    pub fn flush_all_local_pcids(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view().dom() == old(self).view().dom(),
            forall|p: Pcid| #![trigger final(self).spec_index((cpu_id, p))] pcid_valid(p) && p != KERNEL_DEFAULT_PCID ==> final(self).spec_index((cpu_id, p)).is_empty(),
            forall|key: (CpuId, Pcid)| #![trigger final(self).view()[key]] old(self).view().dom().contains(key)
                ==> final(self).view()[key] == if key.0 == cpu_id && key.1 != KERNEL_DEFAULT_PCID { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old(self).view()[key] },
            forall|c: CpuId, p: Pcid| #![trigger final(self).spec_index((c, p))] #![trigger old(self).spec_index((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p == KERNEL_DEFAULT_PCID) ==> final(self).spec_index((c, p)) == old(self).spec_index((c, p)),
    {
        unsafe { veriflat_local_flush_all_pcids(); }
        let ghost old_tlbs = self.cpu_tlbs.view();
        self.cpu_tlbs = Ghost(Map::new(
            old_tlbs.dom(),
            |k: (CpuId, Pcid)| if k.0 == cpu_id && k.1 != KERNEL_DEFAULT_PCID { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old_tlbs.index(k) },
        ));
    }
}
}

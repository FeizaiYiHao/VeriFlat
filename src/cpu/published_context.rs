use vstd::prelude::*;
use crate::*;

verus! {
pub type CpuPublishedArray = [AtomicPcidCr3; NUM_CPUS];

impl KernelK {
    pub fn load_published_pcid_cr3(&self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageTableRoot, Pcid))
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            ret == self.cpu_published[cpu_id as int].view(),
            self.inv() ==> (page_ptr_valid(ret.0) && pcid_valid(ret.1)),
            // A remote reader holding the hardware PCID entry excludes the
            // owner CPU's hardware/publication mismatch window.
            self.inv() && typed_lock_maps_aligned(self, old(lctx)) && cpu_id != old(lctx).cpu_id()
                && typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, self.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid), TypedLockMode::Write)
                ==> ret == (self.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, self.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
    {
        let ret = self.cpu_published[cpu_id].load(Tracked(&mut *lctx));
        assert(self.inv() ==> (page_ptr_valid(ret.0) && pcid_valid(ret.1))) by { reveal(cpu_published_wf); };
        assert(self.inv() && typed_lock_maps_aligned(self, old(lctx)) && cpu_id != old(lctx).cpu_id()
            && typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, self.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid), TypedLockMode::Write)
            ==> ret == (self.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, self.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)) by { reveal(cpu_published_wf); };
        ret
    }
}
}

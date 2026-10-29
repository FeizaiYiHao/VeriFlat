use vstd::prelude::*;
use crate::*;

verus! {
pub type CpuHwCr3PcidArray = [AtomicPcidCr3; NUM_CPUS];

impl KernelK {
    pub fn load_hw_cr3_pcid(&self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageTableRoot, Pcid))
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            ret == self.cpu_hw_cr3_pcid[cpu_id as int].view(),
            self.inv() ==> (page_ptr_valid(ret.0) && pcid_valid(ret.1)),
            // A remote reader holding the hardware PCID entry excludes the
            // owner CPU's window where its hardware CR3/PCID and its hardware cr3/pcid word differ.
            self.inv() && typed_lock_maps_aligned(self, old(lctx)) && cpu_id != old(lctx).cpu_id()
                && typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, self.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid), TypedLockMode::Write)
                ==> ret == (self.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, self.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
    {
        let ret = self.cpu_hw_cr3_pcid[cpu_id].load(Tracked(&mut *lctx));
        proof { if self.inv() { cpu_hw_cr3_pcid_wf_at(self.cpu_hw_cr3_pcid, self.cpu_arr, self.pcid_needflush, cpu_id); } }
        ret
    }
}
}

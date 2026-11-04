use vstd::prelude::*;
use crate::*;

verus! {
/// Every entry `(cpu_id, pcid)` is well formed, pinned to its slot, and write-held exactly when it names a valid holder cpu.
#[verifier::opaque]
pub open spec fn pcid_needflush_wf(pcid_needflush: PcidNeedFlushArray) -> bool {
    &&& pcid_needflush.inv()
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger pcid_needflush.spec_index(cpu_id, pcid)]
        index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> {
            let entry = pcid_needflush.spec_index(cpu_id, pcid);
            &&& entry.inv()
            &&& entry.view().index() == (cpu_id, pcid)
            // The entry's ghost names its holder cpu exactly while the entry is write-held.
            &&& entry.wlocked() == (entry.view_ghost() is Some)
            &&& (entry.view_ghost() is Some ==> index_valid(NUM_CPUS, entry.view_ghost().unwrap()))
        }
}

pub proof fn pcid_needflush_wf_implies_array_inv(pcid_needflush: PcidNeedFlushArray)
    requires pcid_needflush_wf(pcid_needflush)
    ensures pcid_needflush.inv()
{ reveal(pcid_needflush_wf); }

/// Entry `(cpu_id, pcid)` is well formed, pinned to its slot, and write-held exactly when it names a valid holder cpu.
pub proof fn pcid_needflush_wf_at(pcid_needflush: PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid)
    requires
        pcid_needflush_wf(pcid_needflush),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
    ensures
        ({
            let entry = pcid_needflush.spec_index(cpu_id, pcid);
            &&& entry.inv()
            &&& entry.view().index() == (cpu_id, pcid)
            &&& entry.wlocked() == (entry.view_ghost() is Some)
            &&& (entry.view_ghost() is Some ==> index_valid(NUM_CPUS, entry.view_ghost().unwrap()))
        }),
{ reveal(pcid_needflush_wf); }
}

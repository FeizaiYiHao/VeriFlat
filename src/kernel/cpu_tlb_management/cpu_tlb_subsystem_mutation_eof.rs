use vstd::prelude::*;
use crate::*;

verus! {
/// S of `pcid_needflush_array_clear`: only entry `(cpu_id, pcid)` changes, by clearing its flush flag; it stays well formed
/// and keeps its lock and holder cpu.
#[verifier::opaque]
pub open spec fn pcid_needflush_array_clear_eof_transition_framing(pre: PcidNeedFlushArray, post: PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid) -> bool {
    &&& post.spec_index(cpu_id, pcid).inv()
    &&& post.spec_index(cpu_id, pcid).view() == (PcidNeedFlush { needflush: false, ..pre.spec_index(cpu_id, pcid).view() })
    &&& post.spec_index(cpu_id, pcid).view().index() == pre.spec_index(cpu_id, pcid).view().index()
    &&& post.spec_index(cpu_id, pcid).locking_thread() == pre.spec_index(cpu_id, pcid).locking_thread()
    &&& post.spec_index(cpu_id, pcid).view_ghost() == pre.spec_index(cpu_id, pcid).view_ghost()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> post.spec_index(c, p) == pre.spec_index(c, p)
}

/// EOF closure of `pcid_needflush_array_clear`: the cleared entry keeps its slot, lock, and holder cpu.
pub proof fn pcid_needflush_array_clear_eof(pre: PcidNeedFlushArray, post: PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid)
    requires
        pcid_needflush_wf(pre),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid_needflush_array_clear_eof_transition_framing(pre, post, cpu_id, pcid),
    ensures pcid_needflush_wf(post),
{ reveal(pcid_needflush_array_clear_eof_transition_framing); reveal(pcid_needflush_wf); }
}

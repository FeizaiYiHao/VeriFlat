use vstd::prelude::*;
use crate::*;

verus! {
/// Container `owner` at depth `depth > 0` of thread `thread_ptr`'s ancestor chain has its parent, one level up, as the chain's previous entry.
pub(super) proof fn refund_unmap_4k_quota_parent_facts(krnl: KernelK, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize)
    requires
        krnl.inv(),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.ctn_mp.dom().contains(owner),
        krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        0 < depth <= krnl.thr_mp.spec_index(thread_ptr).view().container_depth,
        if depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container }
        else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
    ensures
        ({
            let parent = krnl.ctn_mp.spec_index(owner).view_rodata().view().parent;
            &&& parent is Some
            &&& krnl.ctn_mp.dom().contains(parent.unwrap())
            &&& krnl.ctn_mp.spec_index(parent.unwrap()).view_rodata().view().depth == depth - 1
            &&& krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int - 1) == parent.unwrap()
        }),
{
    reveal(container_thread_wf); reveal(container_root_wf); reveal(container_children_depth_wf); reveal(container_uppertree_seq_wf);
    reveal(container_perms_wf); reveal(container_tree_fields_wf);
}
}

use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// EOF closure of `create_entry_l4`: no user window changes its holder, since the new L3 page is empty and every other walk
    /// is unchanged.
    pub(super) proof fn create_entry_l4_eof_window_locks_unchanged(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l3`: the 512 windows of the new L2 page start unlocked, so no user window changes its holder;
    /// every other walk is unchanged.
    pub(super) proof fn create_entry_l3_eof_window_locks_unchanged(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
            forall|i: L2Index| #![trigger post.lower.l2_lock_of(page_map_ptr).lock_state(i)] pei_valid(i) ==> post.lower.l2_lock_of(page_map_ptr).lock_state(i) is None,
    {
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
        reveal(PageTableHigher::disjoint_l4);
        reveal(PageTableC::wf_l3);
    }
}
} // verus!

use vstd::prelude::*;
use crate::*;

verus! {
/// Loop state of `build_new_child_structure` before range index `i`, from the entry state `pre` with local context `pre_lctx` to
/// `cur` with local context `cur_lctx`: held pages, processes, endpoints, IOMMU tables, page tables other than the child table
/// `pagetable_ptr` and held windows are unchanged; only windows of the child table join the window lock map, and held windows keep
/// their entries; every range page before `i` has its source window held in `entry_lctx`, its child window held and an L1 table.
#[verifier::opaque]
pub(super) open spec fn build_new_child_structure_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext, range: VaRange4K,
    source_pagetable_ptr: RwLockPageTableRoot, pagetable_ptr: RwLockPageTableRoot, entry_lctx: LocalContext, i: usize) -> bool
{
    &&& held_pages_unchanged(pre.pg_arr, cur.pg_arr, pre_lctx)
    &&& held_processes_unchanged(pre.prc_mp, cur.prc_mp, pre_lctx)
    &&& held_endpoints_unchanged(pre.ep_mp, cur.ep_mp, pre_lctx)
    &&& held_iommu_tables_unchanged(pre.it_mp, cur.it_mp, pre_lctx)
    &&& held_pagetables_unchanged_except(pre.pt_mp, cur.pt_mp, pre_lctx, set![pagetable_ptr])
    &&& held_pagetable_windows_unchanged(pre.pt_mp, pre.pt_lower.view(), cur.pt_mp, cur.pt_lower.view(), pre_lctx)
    &&& forall|p: RwLockPageTableRoot, w: WindowVa|
        #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        p != pagetable_ptr ==> cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) == pre_lctx.pagetable_window_lock_map().dom().contains((p, w))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w))
    &&& forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < i ==> {
        &&& pei_valid(spec_v2l4index(range.view().spec_index(j))) && pei_valid(spec_v2l3index(range.view().spec_index(j))) && pei_valid(spec_v2l2index(range.view().spec_index(j)))
        &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.view().spec_index(j))
        &&& entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, window_of(range.view().spec_index(j))))
        &&& cur_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(range.view().spec_index(j))))
        &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)),
            spec_v2l2index(range.view().spec_index(j))) is Some
    }
}

/// The loop state after the directories of the range page `range[i]` were built from `mid` to `post`.
pub(super) proof fn build_new_child_structure_eol_step(pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext, post_lctx: &LocalContext,
    range: VaRange4K, source_pagetable_ptr: RwLockPageTableRoot, pagetable_ptr: RwLockPageTableRoot, entry_lctx: LocalContext, i: usize)
    requires
        build_new_child_structure_eol_loop_framing(pre, mid, pre_lctx, mid_lctx, range, source_pagetable_ptr, pagetable_ptr, entry_lctx, i),
        nonwindow_typed_lock_maps_unchanged(pre_lctx, mid_lctx),
        mid_lctx.thread_id() == pre_lctx.thread_id(),
        source_pagetable_ptr != pagetable_ptr,
        pre_lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> p == source_pagetable_ptr,
        i < range.len,
        entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, window_of(range.view().spec_index(i as int)))),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable_ptr).kernel_l4_end() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end(),
        nonwindow_typed_lock_maps_unchanged(mid_lctx, post_lctx),
        post_lctx.thread_id() == mid_lctx.thread_id(),
        held_processes_unchanged(mid.prc_mp, post.prc_mp, mid_lctx),
        held_endpoints_unchanged(mid.ep_mp, post.ep_mp, mid_lctx),
        held_pages_unchanged(mid.pg_arr, post.pg_arr, mid_lctx),
        held_iommu_tables_unchanged(mid.it_mp, post.it_mp, mid_lctx),
        held_pagetables_unchanged_except(mid.pt_mp, post.pt_mp, mid_lctx, set![pagetable_ptr]),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            mid_lctx.pagetable_window_lock_map().dom().contains((p, w)) && mid_lctx.pagetable_lock_map().dom().contains(p) && p != pagetable_ptr ==> {
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), p).window_view(w) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).window_view(w)
                &&& forall|v: VAddr|
                    #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p).mapping_4k().dom().contains(v)]
                    #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_4k().dom().contains(v)]
                    spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                        &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), p).mapping_4k().dom().contains(v) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_4k().dom().contains(v)
                        &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_4k().dom().contains(v)
                            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p).mapping_4k().spec_index(v) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_4k().spec_index(v)
                    }
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), p).mapping_2m().dom().contains(w.va) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                    ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p).mapping_2m().spec_index(w.va) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p).mapping_2m().spec_index(w.va)
            },
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        ({
            let va = range.view().spec_index(i as int);
            &&& pei_valid(spec_v2l4index(va)) && pei_valid(spec_v2l3index(va)) && pei_valid(spec_v2l2index(va))
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va)
            &&& post_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va)))
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
        }),
        forall|p: RwLockPageTableRoot, w: WindowVa|
            #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            p != pagetable_ptr ==> post_lctx.pagetable_window_lock_map().dom().contains((p, w)) == mid_lctx.pagetable_window_lock_map().dom().contains((p, w)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            mid_lctx.pagetable_window_lock_map().dom().contains((p, w))
                ==> post_lctx.pagetable_window_lock_map().dom().contains((p, w)) && post_lctx.pagetable_window_lock_map().index((p, w)) == mid_lctx.pagetable_window_lock_map().index((p, w)),
    ensures
        build_new_child_structure_eol_loop_framing(pre, post, pre_lctx, post_lctx, range, source_pagetable_ptr, pagetable_ptr, entry_lctx, (i + 1) as usize),
{
    reveal(build_new_child_structure_eol_loop_framing);
}

/// The loop state after the last range page gives the framing guarantees of `build_new_child_structure`.
pub(super) proof fn build_new_child_structure_eol_exit(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext, range: VaRange4K,
    source_pagetable_ptr: RwLockPageTableRoot, pagetable_ptr: RwLockPageTableRoot, entry_lctx: LocalContext)
    requires
        build_new_child_structure_eol_loop_framing(pre, cur, pre_lctx, cur_lctx, range, source_pagetable_ptr, pagetable_ptr, entry_lctx, range.len),
    ensures
        held_pages_unchanged(pre.pg_arr, cur.pg_arr, pre_lctx),
        held_processes_unchanged(pre.prc_mp, cur.prc_mp, pre_lctx),
        held_endpoints_unchanged(pre.ep_mp, cur.ep_mp, pre_lctx),
        held_iommu_tables_unchanged(pre.it_mp, cur.it_mp, pre_lctx),
        held_pagetables_unchanged_except(pre.pt_mp, cur.pt_mp, pre_lctx, set![pagetable_ptr]),
        held_pagetable_windows_unchanged(pre.pt_mp, pre.pt_lower.view(), cur.pt_mp, cur.pt_lower.view(), pre_lctx),
        forall|p: RwLockPageTableRoot, w: WindowVa|
            #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            p != pagetable_ptr ==> cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) == pre_lctx.pagetable_window_lock_map().dom().contains((p, w)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w)),
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
            &&& entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, window_of(range.view().spec_index(j))))
            &&& cur_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(range.view().spec_index(j))))
            &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)),
                spec_v2l2index(range.view().spec_index(j))) is Some
        },
{
    reveal(build_new_child_structure_eol_loop_framing);
}
}

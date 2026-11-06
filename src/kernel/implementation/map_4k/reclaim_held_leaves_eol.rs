use vstd::prelude::*;
use crate::*;

verus! {
/// Loop state of `reclaim_held_leaves` before leaf index `cursor`, from the entry state `pre` with local context `pre_lctx` to `cur`:
/// the local cpu keeps its hardware cr3/pcid word and running state; held containers, processes, IOMMU tables, CPUs and threads
/// other than `thrd_ptr` are unchanged; `thrd_ptr` changes only its 4K, 2M and 1G free-quota pending counters, which the `direct_*`
/// and `indirect_*` counters mirror; the table `pagetable` keeps its lock, kill mark, higher half apart from its L3 tables and 1G
/// mappings, its 1G mappings shrink, it keeps its 4K and 2M mappings, page closure, L2 page set, windows and L2 owners, its L2 entries
/// stay or are cleared, its held L3 and L2 entries stay, and it holds no 4K, 2M or 1G leaf before `cursor`.
#[verifier::opaque]
pub(super) open spec fn reclaim_held_leaves_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr,
    indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: usize, indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: usize, indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH],
    direct_1g: usize, cursor: (L4Index, L3Index, L2Index, L1Index)) -> bool
{
    let e = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let c = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable);
    let thrd = cur.thrd_mp.spec_index(thrd_ptr).view();
    &&& index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view() == pre.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view()
    &&& index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_op.view().view()[pre_lctx.cpu_id() as int] == pre.cpu_op.view().view()[pre_lctx.cpu_id() as int]
    &&& held_threads_unchanged_except(pre.thrd_mp, cur.thrd_mp, pre_lctx, set![thrd_ptr])
    &&& held_containers_unchanged(pre.ctn_mp, cur.ctn_mp, pre_lctx)
    &&& held_processes_unchanged(pre.prc_mp, cur.prc_mp, pre_lctx)
    &&& held_iommu_tables_unchanged(pre.it_mp, cur.it_mp, pre_lctx)
    &&& held_cpus_unchanged(pre.cpu_arr, cur.cpu_arr, pre_lctx)
    &&& cur.thrd_mp.dom().contains(thrd_ptr)
    &&& cur.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread()
    &&& cur.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed()
    &&& cur.thrd_mp.spec_index(thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(thrd_ptr).view_ghost()
    &&& thrd == (Thread {
        direct_free_quota_pending_4k: thrd.direct_free_quota_pending_4k, indirect_free_quota_pending_4k: thrd.indirect_free_quota_pending_4k,
        direct_free_quota_pending_2m: thrd.direct_free_quota_pending_2m, indirect_free_quota_pending_2m: thrd.indirect_free_quota_pending_2m,
        direct_free_quota_pending_1g: thrd.direct_free_quota_pending_1g, indirect_free_quota_pending_1g: thrd.indirect_free_quota_pending_1g, ..pre.thrd_mp.spec_index(thrd_ptr).view()
    })
    &&& direct_4k == thrd.direct_free_quota_pending_4k.view()
    &&& forall|depth: int| #![trigger indirect_4k[depth]] 0 <= depth < thrd.container_depth ==> indirect_4k[depth] == thrd.indirect_free_quota_pending_4k.view().spec_index(depth)
    &&& direct_2m == thrd.direct_free_quota_pending_2m.view()
    &&& forall|depth: int| #![trigger indirect_2m[depth]] 0 <= depth < thrd.container_depth ==> indirect_2m[depth] == thrd.indirect_free_quota_pending_2m.view().spec_index(depth)
    &&& direct_1g == thrd.direct_free_quota_pending_1g.view()
    &&& forall|depth: int| #![trigger indirect_1g[depth]] 0 <= depth < thrd.container_depth ==> indirect_1g[depth] == thrd.indirect_free_quota_pending_1g.view().spec_index(depth)
    &&& thrd.proc_pagetable_ptr == pagetable || pre_lctx.process_lock_map().dom().contains(cur.pt_mp.spec_index(pagetable).view().proc_ptr)
        && cur.prc_mp.spec_index(cur.pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == thrd.owning_container
    &&& cur.pt_mp.dom().contains(pagetable)
    &&& cur.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& cur.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& c.higher == (PageTableHigher { l3_tables: c.higher.l3_tables, mapping_1g: c.higher.mapping_1g, ..e.higher })
    &&& c.mapping_1g().submap_of(e.mapping_1g()) && c.mapping_4k() == e.mapping_4k() && c.mapping_2m() == e.mapping_2m() && c.page_closure() == e.page_closure()
    &&& c.lower.l2_perms.dom() == e.lower.l2_perms.dom() && c.lower.pagetable_window_locks == e.lower.pagetable_window_locks && c.lower.window_stale_cpus == e.lower.window_stale_cpus
    &&& c.lower.hidden_l1_tables_in_locked_windows()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_entry(p, i)] c.lower.l2_entry(p, i) == e.lower.l2_entry(p, i) || c.lower.l2_entry(p, i).is_empty()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_owner(p, i)] c.lower.l2_owner(p, i) == e.lower.l2_owner(p, i)
    &&& forall|l4i: L4Index| #![trigger c.spec_resolve_mapping_l4(l4i)] e.kernel_l4_end() <= l4i && pei_valid(l4i) ==> c.spec_resolve_mapping_l4(l4i) == e.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_l3(l4i, l3i)]
        e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> c.spec_held_l3(l4i, l3i) == e.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger c.spec_held_l2(l4i, l3i, l2i)]
        e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> c.spec_held_l2(l4i, l3i, l2i) == e.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_1g_l3(l4i, l3i)]
        e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !spec_l4_index_path_le(cursor, (l4i, l3i, 0, 0)) ==> c.spec_held_1g_l3(l4i, l3i) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger c.spec_held_2m_l2(l4i, l3i, l2i)]
        e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, 0)) ==> c.spec_held_2m_l2(l4i, l3i, l2i) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
            ==> c.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None
}

/// The loop state at `cur` gives what the leaf search and the leaf reclaims of `reclaim_held_leaves` need at `cur`.
pub(super) proof fn reclaim_held_leaves_eol_iteration_pre(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext, pagetable: RwLockPageTableRoot,
    thrd_ptr: RwLockThreadPtr, indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: usize, indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: usize,
    indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH], direct_1g: usize, cursor: (L4Index, L3Index, L2Index, L1Index))
    requires
        reclaim_held_leaves_eol_loop_framing(pre, cur, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, cursor),
        typed_lock_maps_unchanged(pre_lctx, cur_lctx),
        held_locks_order_below(&pre, pre_lctx, ALLOCATOR_CACHE_4K_MAJOR),
        pre_lctx.page_lock_map().dom().is_empty(),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> pre.cpu_op.view().view()[pre_lctx.cpu_id() as int] is InStep,
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
    ensures
        held_locks_order_below(&cur, cur_lctx, ALLOCATOR_CACHE_4K_MAJOR),
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_op.view().view()[pre_lctx.cpu_id() as int] is InStep,
        cur.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(cur.thrd_mp.spec_index(thrd_ptr)),
        cur.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        cur.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable || cur.prc_mp.spec_index(cur.pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == cur.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        direct_4k == cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger indirect_4k[depth]] 0 <= depth < cur.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect_4k[depth] == cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        direct_2m == cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger indirect_2m[depth]] 0 <= depth < cur.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect_2m[depth] == cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        direct_1g == cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|depth: int| #![trigger indirect_1g[depth]] 0 <= depth < cur.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect_1g[depth] == cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth),
        cur.pt_mp.dom().contains(pagetable),
        cur.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        cur.pt_mp.spec_index(pagetable).view() == (PageTableHigher { l3_tables: cur.pt_mp.spec_index(pagetable).view().l3_tables, mapping_1g: cur.pt_mp.spec_index(pagetable).view().mapping_1g, ..pre.pt_mp.spec_index(pagetable).view() }),
        whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
{
    reveal(reclaim_held_leaves_eol_loop_framing);
}

/// The loop state after the 4K leaf `next` at `va`, the first held leaf at or after `cursor`, was reclaimed from `mid` to `call` and
/// the step boundary went from `call` to `post`.
pub(super) proof fn reclaim_held_leaves_eol_step_4k(pre: KernelK, mid: KernelK, call: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext, call_lctx: &LocalContext,
    pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, va: VAddr, mid_indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], mid_direct_4k: usize,
    indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: usize, indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: usize, indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH],
    direct_1g: usize, cursor: (L4Index, L3Index, L2Index, L1Index), next: (L4Index, L3Index, L2Index, L1Index))
    requires
        reclaim_held_leaves_eol_loop_framing(pre, mid, pre_lctx, pagetable, thrd_ptr, mid_indirect_4k, mid_direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, cursor),
        typed_lock_maps_unchanged(pre_lctx, mid_lctx),
        mid_lctx.cpu_id() == pre_lctx.cpu_id(),
        typed_lock_maps_unchanged(mid_lctx, call_lctx),
        call_lctx.cpu_id() == mid_lctx.cpu_id(),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre_lctx.cpu_lock_map().dom().contains(pre_lctx.cpu_id()),
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> pre.cpu_op.view().view()[pre_lctx.cpu_id() as int] is InStep,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= next.0,
        pei_valid(next.0) && pei_valid(next.1) && pei_valid(next.2) && pei_valid(next.3),
        spec_l4_index_path_le(cursor, next),
        spec_va2index(va) == next,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(next.0, next.1, next.2) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && spec_l4_index_path_le(cursor, (i4, i3, i2, i1)) && !spec_l4_index_path_le(next, (i4, i3, i2, i1))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && spec_l4_index_path_le(cursor, (i4, i3, i2, 0)) && !spec_l4_index_path_le(next, (i4, i3, i2, 0))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) is None,
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3)]
            pei_valid(i4) && pei_valid(i3) && spec_l4_index_path_le(cursor, (i4, i3, 0, 0)) && !spec_l4_index_path_le(next, (i4, i3, 0, 0))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3) is None,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(next.0, next.1) is None,
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> call.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view() == mid.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view(),
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> call.cpu_op.view().view()[mid_lctx.cpu_id() as int] == mid.cpu_op.view().view()[mid_lctx.cpu_id() as int],
        held_threads_unchanged_except(mid.thrd_mp, call.thrd_mp, mid_lctx, set![thrd_ptr]),
        held_containers_unchanged(mid.ctn_mp, call.ctn_mp, mid_lctx),
        held_processes_unchanged(mid.prc_mp, call.prc_mp, mid_lctx),
        held_iommu_tables_unchanged(mid.it_mp, call.it_mp, mid_lctx),
        held_cpus_unchanged(mid.cpu_arr, call.cpu_arr, mid_lctx),
        call.thrd_mp.dom().contains(thrd_ptr),
        call.thrd_mp.spec_index(thrd_ptr).locking_thread() == mid.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        call.thrd_mp.spec_index(thrd_ptr).being_killed() == mid.thrd_mp.spec_index(thrd_ptr).being_killed(),
        call.thrd_mp.spec_index(thrd_ptr).view_ghost() == mid.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        call.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: call.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: call.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..mid.thrd_mp.spec_index(thrd_ptr).view() }),
        direct_4k == call.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger indirect_4k[depth]] 0 <= depth < call.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect_4k[depth] == call.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        call.pt_mp.dom().contains(pagetable),
        call.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread(),
        call.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable);
            let new_c = whole_pagetable(call.pt_mp, call.pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
                    ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
            &&& new_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
        }),
        kernel_step_boundary_framing(call, post, *call_lctx),
        forall|p: RwLockPageTableRoot| #![trigger call_lctx.pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(call_lctx.pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(call.pt_mp, call.pt_lower.view(), p),
    ensures
        reclaim_held_leaves_eol_loop_framing(pre, post, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, (next.0, next.1, next.2, (next.3 + 1) as usize)),
{
    reveal(reclaim_held_leaves_eol_loop_framing);
    index_path_successor_implies_path_le_drops_only_predecessor(next, (next.0, next.1, next.2, (next.3 + 1) as usize));
}

/// The loop state after the 2M leaf `next` at `va`, the first held leaf at or after `cursor`, was reclaimed from `mid` to `call` and
/// the step boundary went from `call` to `post`; the L2 entry of `next` holds no L1 page at `mid`.
pub(super) proof fn reclaim_held_leaves_eol_step_2m(pre: KernelK, mid: KernelK, call: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext, call_lctx: &LocalContext,
    pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, va: VAddr, indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: usize,
    mid_indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH], mid_direct_2m: usize, indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: usize, indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH],
    direct_1g: usize, cursor: (L4Index, L3Index, L2Index, L1Index), next: (L4Index, L3Index, L2Index, L1Index))
    requires
        reclaim_held_leaves_eol_loop_framing(pre, mid, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, mid_indirect_2m, mid_direct_2m, indirect_1g, direct_1g, cursor),
        typed_lock_maps_unchanged(pre_lctx, mid_lctx),
        mid_lctx.cpu_id() == pre_lctx.cpu_id(),
        typed_lock_maps_unchanged(mid_lctx, call_lctx),
        call_lctx.cpu_id() == mid_lctx.cpu_id(),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre_lctx.cpu_lock_map().dom().contains(pre_lctx.cpu_id()),
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> pre.cpu_op.view().view()[pre_lctx.cpu_id() as int] is InStep,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= next.0,
        pei_valid(next.0) && pei_valid(next.1) && pei_valid(next.2) && next.3 == 0,
        spec_l4_index_path_le(cursor, next),
        spec_v2l4index(va) == next.0 && spec_v2l3index(va) == next.1 && spec_v2l2index(va) == next.2,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_l2(next.0, next.1, next.2) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && spec_l4_index_path_le(cursor, (i4, i3, i2, i1)) && !spec_l4_index_path_le(next, (i4, i3, i2, i1))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && spec_l4_index_path_le(cursor, (i4, i3, i2, 0)) && !spec_l4_index_path_le(next, (i4, i3, i2, 0))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) is None,
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3)]
            pei_valid(i4) && pei_valid(i3) && spec_l4_index_path_le(cursor, (i4, i3, 0, 0)) && !spec_l4_index_path_le(next, (i4, i3, 0, 0))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3) is None,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(next.0, next.1) is None,
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> call.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view() == mid.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view(),
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> call.cpu_op.view().view()[mid_lctx.cpu_id() as int] == mid.cpu_op.view().view()[mid_lctx.cpu_id() as int],
        held_threads_unchanged_except(mid.thrd_mp, call.thrd_mp, mid_lctx, set![thrd_ptr]),
        held_containers_unchanged(mid.ctn_mp, call.ctn_mp, mid_lctx),
        held_processes_unchanged(mid.prc_mp, call.prc_mp, mid_lctx),
        held_iommu_tables_unchanged(mid.it_mp, call.it_mp, mid_lctx),
        held_cpus_unchanged(mid.cpu_arr, call.cpu_arr, mid_lctx),
        call.thrd_mp.dom().contains(thrd_ptr),
        call.thrd_mp.spec_index(thrd_ptr).locking_thread() == mid.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        call.thrd_mp.spec_index(thrd_ptr).being_killed() == mid.thrd_mp.spec_index(thrd_ptr).being_killed(),
        call.thrd_mp.spec_index(thrd_ptr).view_ghost() == mid.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        call.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: call.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: call.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..mid.thrd_mp.spec_index(thrd_ptr).view() }),
        direct_2m == call.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger indirect_2m[depth]] 0 <= depth < call.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect_2m[depth] == call.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        call.pt_mp.dom().contains(pagetable),
        call.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread(),
        call.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable);
            let new_c = whole_pagetable(call.pt_mp, call.pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& new_c.lower.l2_entry(old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
                    ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
        }),
        kernel_step_boundary_framing(call, post, *call_lctx),
        forall|p: RwLockPageTableRoot| #![trigger call_lctx.pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(call_lctx.pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(call.pt_mp, call.pt_lower.view(), p),
    ensures
        reclaim_held_leaves_eol_loop_framing(pre, post, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, (next.0, next.1, next.2, 512usize)),
{
    reveal(reclaim_held_leaves_eol_loop_framing);
}

/// The loop state after the 1G leaf `next` at `va`, the first held leaf at or after `cursor`, was reclaimed from `mid` to `call` and the step boundary went to `post`.
pub(super) proof fn reclaim_held_leaves_eol_step_1g(pre: KernelK, mid: KernelK, call: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext, call_lctx: &LocalContext,
    pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, va: VAddr, indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: usize, indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH],
    direct_2m: usize, mid_indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH], mid_direct_1g: usize, indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH], direct_1g: usize,
    cursor: (L4Index, L3Index, L2Index, L1Index), next: (L4Index, L3Index, L2Index, L1Index))
    requires
        reclaim_held_leaves_eol_loop_framing(pre, mid, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, indirect_2m, direct_2m, mid_indirect_1g, mid_direct_1g, cursor),
        typed_lock_maps_unchanged(pre_lctx, mid_lctx),
        mid_lctx.cpu_id() == pre_lctx.cpu_id(),
        typed_lock_maps_unchanged(mid_lctx, call_lctx),
        call_lctx.cpu_id() == mid_lctx.cpu_id(),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre_lctx.cpu_lock_map().dom().contains(pre_lctx.cpu_id()),
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> pre.cpu_op.view().view()[pre_lctx.cpu_id() as int] is InStep,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= next.0,
        pei_valid(next.0) && pei_valid(next.1) && next.2 == 0 && next.3 == 0,
        spec_l4_index_path_le(cursor, next),
        spec_v2l4index(va) == next.0 && spec_v2l3index(va) == next.1,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_l3(next.0, next.1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && spec_l4_index_path_le(cursor, (i4, i3, i2, i1)) && !spec_l4_index_path_le(next, (i4, i3, i2, i1))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && spec_l4_index_path_le(cursor, (i4, i3, i2, 0)) && !spec_l4_index_path_le(next, (i4, i3, i2, 0))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) is None,
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3)]
            pei_valid(i4) && pei_valid(i3) && spec_l4_index_path_le(cursor, (i4, i3, 0, 0)) && !spec_l4_index_path_le(next, (i4, i3, 0, 0))
                ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3) is None,
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> call.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view() == mid.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view(),
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> call.cpu_op.view().view()[mid_lctx.cpu_id() as int] == mid.cpu_op.view().view()[mid_lctx.cpu_id() as int],
        held_threads_unchanged_except(mid.thrd_mp, call.thrd_mp, mid_lctx, set![thrd_ptr]),
        held_containers_unchanged(mid.ctn_mp, call.ctn_mp, mid_lctx),
        held_processes_unchanged(mid.prc_mp, call.prc_mp, mid_lctx),
        held_iommu_tables_unchanged(mid.it_mp, call.it_mp, mid_lctx),
        held_cpus_unchanged(mid.cpu_arr, call.cpu_arr, mid_lctx),
        call.thrd_mp.dom().contains(thrd_ptr),
        call.thrd_mp.spec_index(thrd_ptr).locking_thread() == mid.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        call.thrd_mp.spec_index(thrd_ptr).being_killed() == mid.thrd_mp.spec_index(thrd_ptr).being_killed(),
        call.thrd_mp.spec_index(thrd_ptr).view_ghost() == mid.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        call.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_1g: call.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g,
            indirect_free_quota_pending_1g: call.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g, ..mid.thrd_mp.spec_index(thrd_ptr).view() }),
        direct_1g == call.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|depth: int| #![trigger indirect_1g[depth]] 0 <= depth < call.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect_1g[depth] == call.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth),
        call.pt_mp.dom().contains(pagetable),
        call.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread(),
        call.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable);
            let new_c = whole_pagetable(call.pt_mp, call.pt_lower.view(), pagetable);
            &&& new_c.lower == old_c.lower
            &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
            &&& new_c.mapping_1g() == old_c.mapping_1g().remove(va)
            &&& new_c.page_closure() == old_c.page_closure()
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_1g_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_held_1g_l3(l4i, l3i) == old_c.spec_held_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
            &&& new_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
        }),
        kernel_step_boundary_framing(call, post, *call_lctx),
        forall|p: RwLockPageTableRoot| #![trigger call_lctx.pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(call_lctx.pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(call.pt_mp, call.pt_lower.view(), p),
    ensures
        reclaim_held_leaves_eol_loop_framing(pre, post, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, (next.0, next.1, 511usize, 512usize)),
{
    reveal(reclaim_held_leaves_eol_loop_framing);
}

/// The loop state at `cur` where no held leaf remains at or after `cursor` gives the framing guarantees of `reclaim_held_leaves`.
pub(super) proof fn reclaim_held_leaves_eol_exit(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr,
    indirect_4k: [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: usize, indirect_2m: [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: usize, indirect_1g: [usize; MAX_CONTAINER_TREE_DEPTH], direct_1g: usize,
    cursor: (L4Index, L3Index, L2Index, L1Index))
    requires
        reclaim_held_leaves_eol_loop_framing(pre, cur, pre_lctx, pagetable, thrd_ptr, indirect_4k, direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, cursor),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && spec_l4_index_path_le(cursor, (i4, i3, i2, i1))
                ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && spec_l4_index_path_le(cursor, (i4, i3, i2, 0))
                ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) is None,
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3)]
            pei_valid(i4) && pei_valid(i3) && spec_l4_index_path_le(cursor, (i4, i3, 0, 0)) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3) is None,
    ensures
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view() == pre.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view(),
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_op.view().view()[pre_lctx.cpu_id() as int] == pre.cpu_op.view().view()[pre_lctx.cpu_id() as int],
        held_threads_unchanged_except(pre.thrd_mp, cur.thrd_mp, pre_lctx, set![thrd_ptr]),
        held_containers_unchanged(pre.ctn_mp, cur.ctn_mp, pre_lctx),
        held_processes_unchanged(pre.prc_mp, cur.prc_mp, pre_lctx),
        held_iommu_tables_unchanged(pre.it_mp, cur.it_mp, pre_lctx),
        held_cpus_unchanged(pre.cpu_arr, cur.cpu_arr, pre_lctx),
        cur.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        cur.thrd_mp.spec_index(thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        cur.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            direct_free_quota_pending_4k: cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k,
            direct_free_quota_pending_2m: cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m, indirect_free_quota_pending_2m: cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m,
            direct_free_quota_pending_1g: cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g, indirect_free_quota_pending_1g: cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g,
            ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        cur.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let new_c = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable);
            &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
            &&& new_c.mapping_1g().submap_of(old_c.mapping_1g()) && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i) || new_c.lower.l2_entry(p, i).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_1g_l3(l4i, l3i)] old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_1g_l3(l4i, l3i) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None
        }),
{
    reveal(reclaim_held_leaves_eol_loop_framing);
}
}

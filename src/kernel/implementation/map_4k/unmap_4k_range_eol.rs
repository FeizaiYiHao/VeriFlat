use vstd::prelude::*;
use crate::*;

verus! {
/// Reclaim-loop state of `unmap_4k_range` before range index `i`, from the entry state `pre` with local context `pre_lctx` to `cur`:
/// the local cpu `cpu_id` keeps its hardware cr3/pcid word, step mode and cpu object; held containers and processes are unchanged;
/// `thrd_ptr` changes only its 4K free-quota pending counters, which `direct` and `indirect` mirror, and records the flushed range;
/// the read-held table `pagetable` keeps its object, kill mark and this thread's read hold `pt_lock_id`; every held window of the
/// table keeps its lock, stale set, 2M leaf and visible L1 table, holds the range's leaves from `i` on non-present and none before
/// `i`, and keeps every other 4K leaf.
#[verifier::opaque]
pub(super) open spec fn unmap_4k_range_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId,
    range: VaRange4K, indirect: [usize; MAX_CONTAINER_TREE_DEPTH], direct: usize, i: usize, pt_lock_id: usize) -> bool
{
    let e = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let c = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable);
    let thrd = cur.thrd_mp.spec_index(thrd_ptr).view();
    &&& index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view() == pre.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view()
    &&& cur.cpu_op.view().view()[cpu_id as int] == pre.cpu_op.view().view()[cpu_id as int]
    &&& held_containers_unchanged(pre.ctn_mp, cur.ctn_mp, pre_lctx)
    &&& held_processes_unchanged(pre.prc_mp, cur.prc_mp, pre_lctx)
    &&& cur.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view()
    &&& cur.cpu_arr.spec_index(cpu_id).view().locking_thread() == pre.cpu_arr.spec_index(cpu_id).view().locking_thread()
    &&& cur.cpu_arr.spec_index(cpu_id).view().being_killed() == pre.cpu_arr.spec_index(cpu_id).view().being_killed()
    &&& cur.cpu_arr.spec_index(cpu_id).view().killer_info() == pre.cpu_arr.spec_index(cpu_id).view().killer_info()
    &&& cur.thrd_mp.dom().contains(thrd_ptr)
    &&& cur.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread()
    &&& cur.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed()
    &&& cur.thrd_mp.spec_index(thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(thrd_ptr).view_ghost()
    &&& thrd == (Thread {
        direct_free_quota_pending_4k: thrd.direct_free_quota_pending_4k, indirect_free_quota_pending_4k: thrd.indirect_free_quota_pending_4k, syscall_progress: thrd.syscall_progress,
        ..pre.thrd_mp.spec_index(thrd_ptr).view()
    })
    &&& thrd.syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: range, unmapped: range.len, flushed: true })
    &&& direct == thrd.direct_free_quota_pending_4k.view()
    &&& forall|d: int| #![trigger indirect[d]] #![trigger thrd.indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < thrd.container_depth
        ==> indirect[d] == thrd.indirect_free_quota_pending_4k.view().spec_index(d)
    &&& cur.pt_mp.dom().contains(pagetable)
    &&& cur.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view()
    &&& cur.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& cur.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(pre_lctx.thread_id(), pt_lock_id)
    &&& forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
        &&& c.window_view(w).lock_state == e.window_view(w).lock_state
        &&& c.window_view(w).stale_cpus is None
        &&& c.mapping_2m().dom().contains(w.va) == e.mapping_2m().dom().contains(w.va)
        &&& e.mapping_2m().dom().contains(w.va) ==> c.mapping_2m().spec_index(w.va) == e.mapping_2m().spec_index(w.va)
        &&& pei_valid(spec_v2l2index(w.va))
        &&& !e.lower.l2_entry_hides_l1(e.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            ==> !c.lower.l2_entry_hides_l1(c.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
    }
    &&& forall|w: WindowVa, j: int| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
        pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
            && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va) ==> {
        &&& c.mapping_4k().dom().contains(range.view().spec_index(j)) == (i <= j)
        &&& i <= j ==> !c.mapping_4k().spec_index(range.view().spec_index(j)).present
    }
    &&& forall|w: WindowVa, v: VAddr|
        #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), c.mapping_4k().dom().contains(v)]
        #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), e.mapping_4k().dom().contains(v)]
        pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va)
            && !range.view().contains(v) ==> {
        &&& c.mapping_4k().dom().contains(v) == e.mapping_4k().dom().contains(v)
        &&& e.mapping_4k().dom().contains(v) ==> c.mapping_4k().spec_index(v) == e.mapping_4k().spec_index(v)
    }
}

/// The loop state at `cur` gives what the reclaim of the range page `range[i]` in its held window needs at `cur`.
pub(super) proof fn unmap_4k_range_eol_iteration_pre(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId,
    range: VaRange4K, indirect: [usize; MAX_CONTAINER_TREE_DEPTH], direct: usize, i: usize, pt_lock_id: usize)
    requires
        unmap_4k_range_eol_loop_framing(pre, cur, pre_lctx, pagetable, thrd_ptr, cpu_id, range, indirect, direct, i, pt_lock_id),
        i < range.len,
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        pre.cpu_op.view().view()[cpu_id as int] is InStep,
        pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, window_of(range.view().spec_index(i as int)))),
        spec_va2index(window_of(range.view().spec_index(i as int)).va)
            == (spec_v2l4index(range.view().spec_index(i as int)), spec_v2l3index(range.view().spec_index(i as int)), spec_v2l2index(range.view().spec_index(i as int)), 0usize),
    ensures
        cur.cpu_op.view().view()[cpu_id as int] is InStep,
        cur.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(cur.thrd_mp.spec_index(thrd_ptr)),
        cur.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        cur.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        direct == cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger indirect[d]] 0 <= d < cur.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect[d] == cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        cur.pt_mp.dom().contains(pagetable),
        cur.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view(),
        cur.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(pre_lctx.thread_id(), pt_lock_id),
        ({
            let va = range.view().spec_index(i as int);
            let e = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let c = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable);
            &&& c.mapping_4k().dom().contains(va)
            &&& !c.mapping_4k().spec_index(va).present
            &&& c.window_view(window_of(va)).stale_cpus is None
            &&& c.lower.l2_owner(c.window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va)) == e.lower.l2_owner(e.window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
        }),
{
    reveal(unmap_4k_range_eol_loop_framing);
}

/// The loop state after the range page `range[i]` was reclaimed from `mid` to `post` in its held window.
pub(super) proof fn unmap_4k_range_eol_step(pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext, post_lctx: &LocalContext, pagetable: RwLockPageTableRoot,
    thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, range: VaRange4K, mid_indirect: [usize; MAX_CONTAINER_TREE_DEPTH], mid_direct: usize, indirect: [usize; MAX_CONTAINER_TREE_DEPTH], direct: usize,
    i: usize, pt_lock_id: usize)
    requires
        unmap_4k_range_eol_loop_framing(pre, mid, pre_lctx, pagetable, thrd_ptr, cpu_id, range, mid_indirect, mid_direct, i, pt_lock_id),
        held_locks_order_below(&mid, mid_lctx, ALLOCATOR_CACHE_4K_MAJOR),
        mid_lctx.page_lock_map().dom().is_empty(),
        typed_lock_maps_unchanged(pre_lctx, mid_lctx),
        mid_lctx.cpu_id() == pre_lctx.cpu_id(),
        mid_lctx.thread_id() == pre_lctx.thread_id(),
        cpu_id == pre_lctx.cpu_id(),
        typed_lock_map_contains_mode(pre_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        range.wf(),
        i < range.len,
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> post.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view() == mid.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view(),
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> post.cpu_op.view().view()[mid_lctx.cpu_id() as int] == mid.cpu_op.view().view()[mid_lctx.cpu_id() as int],
        typed_lock_maps_unchanged(mid_lctx, post_lctx),
        post_lctx.cpu_id() == mid_lctx.cpu_id(),
        post_lctx.thread_id() == mid_lctx.thread_id(),
        held_threads_unchanged_except(mid.thrd_mp, post.thrd_mp, mid_lctx, set![thrd_ptr]),
        held_containers_unchanged(mid.ctn_mp, post.ctn_mp, mid_lctx),
        held_processes_unchanged(mid.prc_mp, post.prc_mp, mid_lctx),
        held_cpus_unchanged(mid.cpu_arr, post.cpu_arr, mid_lctx),
        post.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == mid.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == mid.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view_ghost() == mid.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: post.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: post.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..mid.thrd_mp.spec_index(thrd_ptr).view() }),
        direct == post.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger indirect[depth]] 0 <= depth < post.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect[depth] == post.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        held_pagetables_unchanged(mid.pt_mp, post.pt_mp, mid_lctx),
        !whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(i as int)),
        forall|w: WindowVa| #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            let pre_c = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable);
            let post_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
            &&& post_c.window_view(w).lock_state == pre_c.window_view(w).lock_state
            &&& post_c.window_view(w).stale_cpus == pre_c.window_view(w).stale_cpus
            &&& post_c.mapping_2m().dom().contains(w.va) == pre_c.mapping_2m().dom().contains(w.va)
            &&& pre_c.mapping_2m().dom().contains(w.va) ==> post_c.mapping_2m().spec_index(w.va) == pre_c.mapping_2m().spec_index(w.va)
            &&& pei_valid(spec_v2l2index(w.va)) && !pre_c.lower.l2_entry_hides_l1(pre_c.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                ==> !post_c.lower.l2_entry_hides_l1(post_c.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va)
                && v != range.view().spec_index(i as int) ==> {
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
    ensures
        unmap_4k_range_eol_loop_framing(pre, post, pre_lctx, pagetable, thrd_ptr, cpu_id, range, indirect, direct, (i + 1) as usize, pt_lock_id),
        held_locks_order_below(&post, post_lctx, ALLOCATOR_CACHE_4K_MAJOR),
{
    reveal(unmap_4k_range_eol_loop_framing);
    range.wf_implies_view_index_is_start_plus_offset();
}

/// The loop state after the last range page gives the reclaim-loop guarantees of `unmap_4k_range`.
pub(super) proof fn unmap_4k_range_eol_exit(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId,
    range: VaRange4K, indirect: [usize; MAX_CONTAINER_TREE_DEPTH], direct: usize, pt_lock_id: usize)
    requires
        unmap_4k_range_eol_loop_framing(pre, cur, pre_lctx, pagetable, thrd_ptr, cpu_id, range, indirect, direct, range.len, pt_lock_id),
    ensures
        index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> cur.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view() == pre.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view(),
        cur.cpu_op.view().view()[cpu_id as int] == pre.cpu_op.view().view()[cpu_id as int],
        held_containers_unchanged(pre.ctn_mp, cur.ctn_mp, pre_lctx),
        held_processes_unchanged(pre.prc_mp, cur.prc_mp, pre_lctx),
        cur.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
        cur.cpu_arr.spec_index(cpu_id).view().locking_thread() == pre.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        cur.cpu_arr.spec_index(cpu_id).view().being_killed() == pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        cur.cpu_arr.spec_index(cpu_id).view().killer_info() == pre.cpu_arr.spec_index(cpu_id).view().killer_info(),
        cur.thrd_mp.dom().contains(thrd_ptr),
        cur.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        cur.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        cur.thrd_mp.spec_index(thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        cur.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            direct_free_quota_pending_4k: cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k,
            syscall_progress: cur.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        cur.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: range, unmapped: range.len, flushed: true }),
        direct == cur.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger indirect[d]] #![trigger cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < cur.thrd_mp.spec_index(thrd_ptr).view().container_depth
            ==> indirect[d] == cur.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        cur.pt_mp.dom().contains(pagetable),
        cur.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view(),
        cur.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed(),
        cur.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(pre_lctx.thread_id(), pt_lock_id),
        forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            let e = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let c = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable);
            &&& c.window_view(w).lock_state == e.window_view(w).lock_state
            &&& c.window_view(w).stale_cpus is None
            &&& c.mapping_2m().dom().contains(w.va) == e.mapping_2m().dom().contains(w.va)
            &&& e.mapping_2m().dom().contains(w.va) ==> c.mapping_2m().spec_index(w.va) == e.mapping_2m().spec_index(w.va)
            &&& pei_valid(spec_v2l2index(w.va))
            &&& !e.lower.l2_entry_hides_l1(e.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                ==> !c.lower.l2_entry_hides_l1(c.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        },
        forall|w: WindowVa, j: int| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
            pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
                && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va)
                ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j)),
        forall|w: WindowVa, v: VAddr|
            #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va)
                && !range.view().contains(v) ==> {
                &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    reveal(unmap_4k_range_eol_loop_framing);
}
}

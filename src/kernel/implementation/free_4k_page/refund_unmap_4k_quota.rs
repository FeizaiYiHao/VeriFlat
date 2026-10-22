use vstd::prelude::*;
use crate::*;
use super::free_quota_4k::return_free_quota_4k;
#[cfg(verus_keep_ghost)]
use super::refund_unmap_4k_quota_trace::refund_unmap_4k_step_pre_from_k;
#[cfg(verus_keep_ghost)]
use super::refund_unmap_4k_quota_eof::refund_unmap_4k_quota_parent_facts;

verus! {
/// Returns `thread_ptr`'s pending 4K quota at `depth` to `owner`'s allocator and records the quota step.
fn refund_unmap_4k_quota_level(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr, amount: usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        depth <= old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth,
        if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { owner == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container }
        else { old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        depth > 0 ==> old(krnl).ctn_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth - 1))
            && old(krnl).ctn_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth - 1)).view_rodata().view().depth == depth - 1,
        0 < amount,
        amount == old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().last().old_u == kernel_k_to_kernel_u(*old(krnl)),
        kernel_u_container_quota_4k_increased(final(steps).view().last().old_u, final(steps).view().last().new_u, old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { 0usize } else { old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() },
        final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() == if depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, 0usize) }
            else { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
        final(krnl).ctn_mp.dom().contains(owner),
        depth > 0 ==> final(krnl).ctn_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth - 1))
            && final(krnl).ctn_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth - 1)).view_rodata().view().depth == depth - 1,
{
    let mut counter = amount;
    assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
    proof {
        let origin = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
        assert(steps.snapshot_k().ctn_mp.dom().contains(origin) && (owner == origin || steps.snapshot_k().ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(owner))) by {
            container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_thread_wf_owned_thread_at(krnl.ctn_mp, krnl.thr_mp, origin, thread_ptr); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
            broadcast use vstd::seq::Seq::lemma_index_contains;
        };
    }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
    return_free_quota_4k(krnl, thread_ptr, owner, depth, allocator_ptr, &mut counter, Tracked(&mut *lctx), thread_perm, Tracked(&quota_perm));
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedHeldLock { lock_id: krnl.allc_4k_mp.spec_index(allocator_ptr).quota.lock_id(), mode: TypedLockMode::Write }); };
        assert(kernel_container_quota_4k_changed(&steps.snapshot_k(), &*krnl, owner, amount as int)) by {
            reveal(kernel_container_quota_4k_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
        };
        krnl.kernel_step_boundary_container_quota_4k_changed(&mut *lctx, &mut *steps, owner, amount as int, old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container);
        assert(krnl.ctn_mp.dom().contains(owner) && (depth > 0 ==> krnl.ctn_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth - 1))
            && krnl.ctn_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth - 1)).view_rodata().view().depth == depth - 1)) by {
            let origin = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
            let uppers = krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view();
            thread_perms_wf_at(krnl.thr_mp, thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_thread_wf_owned_thread_at(krnl.ctn_mp, krnl.thr_mp, origin, thread_ptr);
            container_uppertree_seq_wf_at(krnl.rt_ctn, krnl.ctn_mp, origin, owner); container_uppertree_seq_wf_at(krnl.rt_ctn, krnl.ctn_mp, origin, uppers[depth - 1]);
            broadcast use vstd::seq::Seq::lemma_index_contains;
        };
    }
}

/// Refunds `thread_ptr`'s pending 4K quota at `depth` to `owner`, clears that pending counter, and returns `owner`'s parent (or `owner` at depth 0).
fn refund_unmap_4k_quota_at_depth(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, thread_depth: usize, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>) -> (next_owner: RwLockContainerPtr)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        thread_depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth,
        old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().len() == thread_depth,
        depth <= thread_depth <= MAX_CONTAINER_TREE_DEPTH,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger old(indirect)[d]] #![trigger old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth
            ==> old(indirect)[d] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        depth < thread_depth ==> *old(direct) == 0,
        forall|d: int| #![trigger old(indirect)[d]] depth < d < thread_depth ==> old(indirect)[d] == 0,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        if depth == thread_depth { owner == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container } else { old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 1,
        final(steps).view().len() == old(steps).view().len() ==> final(steps).view() == old(steps).view(),
        final(steps).view().len() == old(steps).view().len() + 1 ==> {
            &&& final(steps).view() == old(steps).view().push(final(steps).view().last())
            &&& final(steps).view().last().old_u == kernel_k_to_kernel_u(*old(krnl))
            &&& kernel_u_container_quota_4k_increased(final(steps).view().last().old_u, final(steps).view().last().new_u, old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container)
        },
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 1,
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_map_majors_lt(final(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        typed_lock_map_majors_lt(final(lctx).page_lock_map(), QUOTA_4K_MAJOR),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().len() == thread_depth,
        *final(direct) == 0,
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger final(indirect)[d]] #![trigger final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth
            ==> final(indirect)[d] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        forall|d: int| #![trigger final(indirect)[d]] depth <= d < thread_depth ==> final(indirect)[d] == 0,
        final(krnl).ctn_mp.dom().contains(next_owner),
        depth > 0 ==> final(krnl).ctn_mp.spec_index(next_owner).view_rodata().view().depth == depth - 1,
        depth > 0 ==> final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int - 1) == next_owner,
{
    assert(krnl.ctn_mp.view().spec_index(owner).is_init() && krnl.ctn_mp.view().spec_index(owner).addr() == owner) by { container_perms_wf_at(krnl.ctn_mp, owner); };
    let ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
    let parent = ro.parent;
    let allocator_ptr = ro.allocator_ptr_4k;
    assert(depth > 0 ==> parent is Some && krnl.ctn_mp.dom().contains(parent.unwrap()) && krnl.ctn_mp.spec_index(parent.unwrap()).view_rodata().view().depth == depth - 1
        && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int - 1) == parent.unwrap()) by {
        if depth > 0 { refund_unmap_4k_quota_parent_facts(*krnl, thread_ptr, owner, depth); }
    };
    let counter = if depth == thread_depth { *direct } else { indirect[depth] };
    if counter != 0 {
        refund_unmap_4k_quota_level(krnl, thread_ptr, owner, depth, allocator_ptr, counter, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    } else {
        proof { held_kernel_objects_unchanged_reflexive(krnl, lctx); }
    }
    if depth == thread_depth { *direct = 0; } else { indirect[depth] = 0; }
    if depth > 0 { parent.unwrap() } else { owner }
}

pub fn refund_unmap_4k_quota(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger old(indirect)[d]] 0 <= d < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[d] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        index_valid(NUM_CPUS, old(lctx).cpu_id()),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), old(lctx).cpu_id(), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + MAX_CONTAINER_TREE_DEPTH + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let thread = old(krnl).thr_mp.spec_index(thread_ptr).view();
            &&& kernel_u_container_quota_4k_increased(old_u, final(steps).view()[j].new_u, thread.owning_container)
            &&& old_u.cpu_array[old(lctx).cpu_id() as int].lock_state is WriteLocked
            &&& old_u.cpu_array[old(lctx).cpu_id() as int].current_thread == old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_thread
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == thread.owning_container
            &&& old_u.thread_map[thread_ptr].owning_proc == thread.owning_proc
            &&& old_u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
            &&& old_u.process_map.dom().contains(thread.owning_proc)
            &&& old_u.process_map[thread.owning_proc].lock_state is WriteLocked
            &&& !old(krnl).prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(krnl).prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Write) ==> {
                &&& old_u.process_map[thread.owning_proc].pagetable is Some
                &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
            }
            &&& !old(krnl).prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(krnl).prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Read) ==> {
                &&& old_u.process_map[thread.owning_proc].pagetable is Some
                &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is ReadLocked
            }
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), thread.owning_container, TypedLockMode::Write) ==> {
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
            }
            &&& old_u.cpu_array[old(lctx).cpu_id() as int] == kernel_k_to_kernel_u(*old(krnl)).cpu_array[old(lctx).cpu_id() as int]
            &&& forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)] old(lctx).process_lock_map().dom().contains(p) ==> {
                &&& old_u.process_map.dom().contains(p)
                &&& old_u.process_map[p].lock_state == kernel_k_to_kernel_u(*old(krnl)).process_map[p].lock_state
                &&& old_u.process_map[p].killed == kernel_k_to_kernel_u(*old(krnl)).process_map[p].killed
                &&& old_u.process_map[p].owning_container == kernel_k_to_kernel_u(*old(krnl)).process_map[p].owning_container
            }
        },
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len(),
        final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + MAX_CONTAINER_TREE_DEPTH + 1,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        *final(direct) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == 0,
        forall|d: int| #![trigger final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth
            ==> final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().len() == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth,
{
    assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(thread_ptr).inv() && krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().len() == krnl.thr_mp.spec_index(thread_ptr).view().container_depth) by {
        thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
    };
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
    let thread_depth = thread.container_depth;
    let mut owner = thread.owning_container;
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx)
        && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx) && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_cpus_unchanged(krnl.cpu_arr, krnl.cpu_arr, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == thread_depth && thread_depth <= MAX_CONTAINER_TREE_DEPTH) by {
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, owner);
    };
    let mut remaining = thread_depth + 1;
    while remaining > 0
        invariant
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + thread_depth + 1 - remaining,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> {
                let old_u = steps.view()[j].old_u;
                let thread = old(krnl).thr_mp.spec_index(thread_ptr).view();
                &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, thread.owning_container)
                &&& old_u.cpu_array[old(lctx).cpu_id() as int].lock_state is WriteLocked
                &&& old_u.cpu_array[old(lctx).cpu_id() as int].current_thread == old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_thread
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
                &&& old_u.thread_map[thread_ptr].owning_container == thread.owning_container
                &&& old_u.thread_map[thread_ptr].owning_proc == thread.owning_proc
                &&& old_u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.process_map[thread.owning_proc].lock_state is WriteLocked
                &&& !old(krnl).prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(krnl).prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Write) ==> {
                    &&& old_u.process_map[thread.owning_proc].pagetable is Some
                    &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
                }
                &&& !old(krnl).prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(krnl).prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Read) ==> {
                    &&& old_u.process_map[thread.owning_proc].pagetable is Some
                    &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is ReadLocked
                }
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), thread.owning_container, TypedLockMode::Write) ==> {
                    &&& old_u.container_map.dom().contains(thread.owning_container)
                    &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
                }
                &&& old_u.cpu_array[old(lctx).cpu_id() as int] == kernel_k_to_kernel_u(*old(krnl)).cpu_array[old(lctx).cpu_id() as int]
                &&& forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)] old(lctx).process_lock_map().dom().contains(p) ==> {
                    &&& old_u.process_map.dom().contains(p)
                    &&& old_u.process_map[p].lock_state == kernel_k_to_kernel_u(*old(krnl)).process_map[p].lock_state
                    &&& old_u.process_map[p].killed == kernel_k_to_kernel_u(*old(krnl)).process_map[p].killed
                    &&& old_u.process_map[p].owning_container == kernel_k_to_kernel_u(*old(krnl)).process_map[p].owning_container
                }
            },
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            *direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(lctx.cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_map_majors_lt(lctx.page_lock_map(), QUOTA_4K_MAJOR),
            lctx.allocator_quota_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty(),
            lctx.allocator_quota_1g_lock_map().dom().is_empty(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            old(steps).nonlock_view().len() <= steps.nonlock_view().len(),
            steps.nonlock_view().len() <= old(steps).nonlock_view().len() + thread_depth + 1 - remaining,
            remaining <= thread_depth + 1,
            thread_depth <= MAX_CONTAINER_TREE_DEPTH,
            thread_depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth,
            krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().len() == thread_depth,
            krnl.ctn_mp.dom().contains(owner),
            remaining > 0 ==> krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == remaining - 1,
            remaining > 0 ==> (if remaining == thread_depth + 1 { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container } else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(remaining as int - 1) == owner }),
            remaining <= thread_depth ==> *direct == 0,
            forall|d: int| #![trigger indirect[d]] remaining <= d < thread_depth ==> indirect[d] == 0,
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            index_valid(NUM_CPUS, old(lctx).cpu_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), old(lctx).cpu_id(), TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        decreases remaining,
    {
        let depth = remaining - 1;
        proof { refund_unmap_4k_step_pre_from_k(&*krnl, &*old(krnl), &*lctx, &*old(lctx), thread_ptr); }
        owner = refund_unmap_4k_quota_at_depth(krnl, thread_ptr, owner, depth, thread_depth, indirect, direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
        remaining = depth;
    }
}
}

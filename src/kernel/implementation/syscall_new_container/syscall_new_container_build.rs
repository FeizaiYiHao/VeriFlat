use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_new_container_trace::new_container_share_steps_from_directory;

verus! {
/// Under the child table's big write lock, builds the L4, L3 and L2 directories on the walk to every page of `range` in the
/// child's table, page by page, recording at most three directory steps per page; the caller's thread funds the directory
/// pages, which move from the parent container into the child container. A new L2 page starts with the range's windows under
/// it held, and their perms join the returned map. Afterwards every page of `range` has its child window held and an L1 table,
/// and the source window that covers it is held in the entry context `entry_lctx`.
pub(super) fn build_new_container_child_structure(
    krnl: &mut KernelK, range: &VaRange4K, allocator_ptr: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, child_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, parent_container_ptr: RwLockContainerPtr, cpu_id: CpuId, source_pagetable_ptr: RwLockPageTableRoot, pagetable_ptr: RwLockPageTableRoot,
    Ghost(origin): Ghost<Share4kOrigin>, Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(container_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        parent_container_ptr != container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        parent_container_lock_perm.state() is WriteLock && parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        container_lock_perm.state() is WriteLock && container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_ptr),
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().pagetable == pagetable_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_ptr).view().zombie,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().len() <= 1,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1 + 3 * range.len,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *range, target_range: *range, shared: 0, origin }),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == thread_ptr && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == thread_ptr,
        share_4k_objects_k(*old(krnl), cpu_id).target == child_ptr && share_4k_objects_k(*old(krnl), cpu_id).target_container == container_ptr,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source == Some(parent_container_ptr),
        source_pagetable_ptr != pagetable_ptr,
        old(lctx).pagetable_lock_map().dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == child_ptr,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).is_empty(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
        held_locks_order_below(old(krnl), old(lctx), PAGE_TABLE_WINDOW_LOCK_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        range.wf(),
        range.len > 0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == source_pagetable_ptr,
        pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).wf(),
        entry_k.pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start),
        forall|j: int| #![trigger range.view().spec_index(j)]
            0 <= j < range.len ==> pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(range.view().spec_index(j)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                ==> entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, w)),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 3 * range.len,
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 3 * range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> share_4k_range_step(final(steps).view()[j], cpu_id),
        share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(parent_container_ptr).view() }),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(container_ptr).view() }),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        final(krnl).prc_mp.dom().contains(child_ptr),
        final(krnl).prc_mp.spec_index(child_ptr) == old(krnl).prc_mp.spec_index(child_ptr),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_locks_order_below(final(krnl), final(lctx), PAGE_TABLE_WINDOW_LOCK_MAJOR),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr]),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(thread_ptr)),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 3 * range.len <= final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == child_ptr,
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == Map::<VAddr, MapEntry>::empty(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == Map::<VAddr, MapEntry>::empty(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == Map::<VAddr, MapEntry>::empty(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> old(lctx).pagetable_window_lock_map().dom().contains((p, w)) || (p == pagetable_ptr && ret.view().dom().contains(w)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().dom().contains((p, w))
                && final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                ==> ret.view().dom().contains(w),
        forall|w: WindowVa| #![trigger ret.view().dom().contains(w)] ret.view().dom().contains(w) ==> {
            &&& va_range_2m_windows(*range).contains(w)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& ret.view().index(w).state() is WriteLock
            &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr)
                .window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
        },
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
            &&& spec_va2index(window_of(range.view().spec_index(j)).va) == (spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)), spec_v2l2index(range.view().spec_index(j)), 0usize)
            &&& entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, window_of(range.view().spec_index(j))))
            &&& final(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(range.view().spec_index(j))))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)),
                spec_v2l2index(range.view().spec_index(j))) is Some
        },
{
    broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
    let tracked mut window_perms: Map<WindowVa, LockPerm> = Map::tracked_empty();
    let range_len = range.len;
    let start_indices = va2index(range.start);
    let end_indices = va2index(range.index(range_len - 1));
    proof {
        va_range_2m_windows_contains_window_of_first_n_pages(*range, range.len as int);
        held_kernel_objects_unchanged_reflexive(krnl, lctx); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        range.va_range_lemma();
        spec_va_4k_valid_index_roundtrip(range.start); spec_va_4k_valid_index_roundtrip(range.view()[range.len - 1]);
    }
    let mut i: usize = 0;
    while i < range_len
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            nonwindow_typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            steps.snapshot_k() == *krnl,
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + 3 * i,
            old(steps).nonlock_view().len() <= steps.nonlock_view().len() <= old(steps).nonlock_view().len() + 3 * i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
            share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(*old(krnl), cpu_id),
            share_4k_objects_k(*old(krnl), cpu_id).source_thread == thread_ptr && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == thread_ptr,
            share_4k_objects_k(*old(krnl), cpu_id).target == child_ptr && share_4k_objects_k(*old(krnl), cpu_id).target_container == container_ptr,
            share_4k_objects_k(*old(krnl), cpu_id).transfer_source == Some(parent_container_ptr),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            held_locks_order_below(krnl, lctx, PAGE_TABLE_WINDOW_LOCK_MAJOR),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            krnl.ctn_mp.dom().contains(parent_container_ptr),
            krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost(),
            krnl.ctn_mp.spec_index(parent_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread(),
            krnl.ctn_mp.spec_index(parent_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
            krnl.ctn_mp.spec_index(parent_container_ptr).view() == (Container { owned_pages: krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(parent_container_ptr).view() }),
            krnl.ctn_mp.spec_index(container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost(),
            krnl.ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread(),
            krnl.ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
            krnl.ctn_mp.spec_index(container_ptr).view() == (Container { owned_pages: krnl.ctn_mp.spec_index(container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(container_ptr).view() }),
            krnl.ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata(),
            parent_container_ptr != container_ptr,
            old(krnl).ctn_mp.dom().contains(parent_container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
            !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
            parent_container_lock_perm.state() is WriteLock && parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
            parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
            container_lock_perm.state() is WriteLock && container_lock_perm.thread_id() == old(lctx).thread_id(),
            container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
            krnl.allc_4k_mp.dom().contains(allocator_ptr),
            old(krnl).prc_mp.dom().contains(child_ptr),
            old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().pagetable == pagetable_ptr,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
            !old(krnl).prc_mp.spec_index(child_ptr).view().zombie,
            krnl.prc_mp.dom().contains(child_ptr),
            krnl.prc_mp.spec_index(child_ptr) == old(krnl).prc_mp.spec_index(child_ptr),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pagetables_unchanged_except(old(krnl).pt_mp, krnl.pt_mp, old(lctx), set![pagetable_ptr]),
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), old(lctx)),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(thread_ptr).being_killed(),
            !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr)),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == parent_container_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view(),
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().len() <= 1,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1 + 3 * range_len,
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 3 * i <= krnl.thr_mp.spec_index(thread_ptr).view().quota_4k,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *range, target_range: *range, shared: 0, origin }),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            source_pagetable_ptr != pagetable_ptr,
            old(lctx).pagetable_lock_map().dom().contains(source_pagetable_ptr),
            krnl.pt_mp.dom().contains(pagetable_ptr),
            krnl.pt_mp.spec_index(pagetable_ptr).view().proc_ptr == child_ptr,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k() == Map::<VAddr, MapEntry>::empty(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m() == Map::<VAddr, MapEntry>::empty(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_1g() == Map::<VAddr, MapEntry>::empty(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            range.wf(),
            range.len == range_len,
            0 < range_len,
            i <= range_len,
            start_indices == spec_va2index(range.start),
            end_indices == spec_va2index(range.view()[range_len - 1]),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == source_pagetable_ptr,
            pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).wf(),
            entry_k.pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start),
            forall|j: int| #![trigger range.view().spec_index(j)]
                0 <= j < range.len ==> pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(range.view().spec_index(j)),
            forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
                va_range_2m_windows(*range).contains(w) && pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                    ==> entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, w)),
            forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
                lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) == (va_range_2m_windows(*range).contains(w)
                    && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                p != pagetable_ptr ==> lctx.pagetable_window_lock_map().dom().contains((p, w)) == old(lctx).pagetable_window_lock_map().dom().contains((p, w)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa|
                #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
                #![trigger va_range_2m_windows(*range).contains(w)]
                lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
                &&& window_perms.dom().contains(w)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == lctx.thread_id()
                &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr)
                    .window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
            },
            forall|w: WindowVa| #![trigger window_perms.dom().contains(w)] window_perms.dom().contains(w) ==> lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)),
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                &&& va_range_2m_windows(*range).contains(window_of(range.view().spec_index(j)))
                &&& spec_va2index(window_of(range.view().spec_index(j)).va) == (spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)), spec_v2l2index(range.view().spec_index(j)), 0usize)
            },
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < i ==> {
                &&& pei_valid(spec_v2l4index(range.view().spec_index(j))) && pei_valid(spec_v2l3index(range.view().spec_index(j))) && pei_valid(spec_v2l2index(range.view().spec_index(j)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.view().spec_index(j))
                &&& entry_lctx.pagetable_window_lock_map().dom().contains((source_pagetable_ptr, window_of(range.view().spec_index(j))))
                &&& lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(range.view().spec_index(j))))
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)),
                    spec_v2l2index(range.view().spec_index(j))) is Some
            },
        decreases range_len - i,
    {
        let cur_va = range.index(i);
        let cur = va2index(cur_va);
        let lo = if cur.0 == start_indices.0 && cur.1 == start_indices.1 { start_indices.2 } else { 0 };
        let hi = if cur.0 == end_indices.0 && cur.1 == end_indices.1 { end_indices.2 } else { 511 };
        proof {
            broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
            range.va_range_lemma();
            spec_va_4k_valid_index_roundtrip(cur_va); spec_va_4k_valid_index_roundtrip(range.start); spec_va_4k_valid_index_roundtrip(range.view()[range.len - 1]);
            spec_v2l4index_monotonic(range.start, cur_va);
            spec_index2va_le_implies_4k_indices_lex_le(start_indices, cur); spec_index2va_le_implies_4k_indices_lex_le(cur, end_indices);
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).higher.wf_mapping_1g_at(cur.0, cur.1);
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf_mapping_2m_at(cur.0, cur.1, cur.2);
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf_mapping_4k_at(cur.0, cur.1, cur.2, cur.3);
            pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).wf_mapping_4k_at(cur.0, cur.1, cur.2, cur.3);
        }
        let ghost before = steps.view();
        let Tracked(minted) = mmap_4k_build_one_structure(
            krnl, cur_va, lo, hi, allocator_ptr, thread_ptr, child_ptr, container_ptr, cpu_id, pagetable_ptr, Some(parent_container_ptr), Ghost(thread_ptr), Tracked(&mut *lctx),
            Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(Some(parent_container_lock_perm)), Tracked(Some(container_lock_perm)),
        );
        proof {
            new_container_share_steps_from_directory(&*steps, before, old(steps).view().len() as int, cpu_id);
            broadcast use Set::lemma_map_by_contains;
            let key_map = Map::new(minted.dom().map_by(|l2i: L2Index| WindowVa { va: spec_index2va((cur.0, cur.1, l2i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                |w: WindowVa| spec_v2l2index(w.va));
            let tracked moved = Map::<L2Index, LockPerm>::tracked_map_keys(minted, key_map);
            window_perms.tracked_union_prefer_right(moved);
        }
        i = i + 1;
    }
    Tracked(window_perms)
}
} // verus!

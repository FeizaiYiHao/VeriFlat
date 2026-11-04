use vstd::prelude::*;
use crate::*;
use super::reclaim_held_4k_page::reclaim_held_4k_page;

verus! {
/// Reclaim the held 4K leaves of the write-held `pagetable` in index order from its first user root entry. No user root entry
/// resolves, no CPU is listed stale for the table, no window of it is locked, and no L2 entry of it is locked or hides its L1
/// page. Each leaf's page is reclaimed and the leaf cleared in its own kernel step, which leaves the user view unchanged, so
/// the walk records no step. Unless `thrd_ptr` runs in `pagetable`, it holds the table's process, which shares its container.
/// Stops at the first held 2M leaf and returns its indices; returns None once no held leaf remains.
pub fn reclaim_held_4k_leaves(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
) -> (stopped_2m: Option<(L4Index, L3Index, L2Index)>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable || old(lctx).process_lock_map().dom().contains(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr)
            && old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
        }),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            let s = stopped_2m->Some_0;
            &&& stopped_2m is None ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None
            &&& stopped_2m is Some ==> old_c.kernel_l4_end() <= s.0 && pei_valid(s.0) && pei_valid(s.1) && pei_valid(s.2) && new_c.spec_held_2m_l2(s.0, s.1, s.2) is Some
            &&& stopped_2m is Some ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le((s.0, s.1, s.2, 0), (l4i, l3i, l2i, l1i))
                    ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None
        }),
{
    let ghost e = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    proof { krnl.default_pagetable_wf_at(pagetable); held_kernel_objects_unchanged_reflexive(krnl, lctx); }
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (KERNEL_MEM_END_L4INDEX, 0, 0, 0);
    loop
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            steps.view() == old(steps).view(),
            KERNEL_MEM_END_L4INDEX <= cursor.0 && pei_valid(cursor.0) && pei_valid(cursor.1) && pei_valid(cursor.2) && cursor.3 <= 512,
            e == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            e.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
            old(lctx).page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == old(lctx).thread_id(),
            thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            forall|l4i: L4Index| #![trigger e.spec_resolve_mapping_l4(l4i)] e.kernel_l4_end() <= l4i && pei_valid(l4i) ==> e.spec_resolve_mapping_l4(l4i) is None,
            forall|p: PageMapPtr, i: L2Index| #![trigger e.lower.l2_owner(p, i)] e.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> e.lower.l2_owner(p, i) is None,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            held_threads_unchanged_except(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx), set![thrd_ptr]),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            *direct == krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
            forall|depth: int| #![trigger indirect[depth]] 0 <= depth < krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth ==> indirect[depth] == krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
            krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable || old(lctx).process_lock_map().dom().contains(krnl.pt_mp.spec_index(pagetable).view().proc_ptr)
                && krnl.prc_mp.spec_index(krnl.pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container,
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            ({
                let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                &&& c.higher == e.higher && c.mapping_4k() == e.mapping_4k() && c.mapping_2m() == e.mapping_2m() && c.page_closure() == e.page_closure()
                &&& c.lower.l2_perms.dom() == e.lower.l2_perms.dom() && c.lower.pagetable_window_locks == e.lower.pagetable_window_locks && c.lower.window_stale_cpus == e.lower.window_stale_cpus
                &&& c.lower.hidden_l1_tables_in_locked_windows()
                &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_entry(p, i)] c.lower.l2_entry(p, i) == e.lower.l2_entry(p, i)
                &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_owner(p, i)] c.lower.l2_owner(p, i) == e.lower.l2_owner(p, i)
                &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger c.spec_held_l2(l4i, l3i, l2i)]
                    e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> c.spec_held_l2(l4i, l3i, l2i) == e.spec_held_l2(l4i, l3i, l2i)
                &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger c.spec_held_2m_l2(l4i, l3i, l2i)]
                    e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> c.spec_held_2m_l2(l4i, l3i, l2i) == e.spec_held_2m_l2(l4i, l3i, l2i)
                &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                    e.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) ==> c.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None
            }),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let found = pagetable_map_next_held_leaf_from(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, cursor, Tracked(&*lctx), pagetable_perm);
        if found.is_none() { return None; }
        let (next, is_2m, leaf) = found.unwrap();
        if is_2m { return Some((next.0, next.1, next.2)); }
        let va = index2va(next);
        let pg_ptr = leaf.addr;
        proof {
            assert(va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
            mapped_4k_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1, next.2, next.3);
            mapped_4k_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va); page_index_valid_imply_page_ptr_valid();
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            assert(krnl.pt_lower.view() =~= krnl.pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
        }
        reclaim_held_4k_page(krnl, pagetable, va, pg_ptr, thrd_ptr, cpu_id, indirect, direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
        proof {
            kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable));
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { index_path_successor_implies_path_le_drops_only_predecessor(next, cursor); }
    }
}
}

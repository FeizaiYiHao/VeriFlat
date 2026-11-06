use vstd::prelude::*;
use crate::*;
use super::reclaim_held_4k_page::reclaim_held_4k_page;
use super::reclaim_held_2m_page::reclaim_held_2m_page;
use super::reclaim_held_1g_page::reclaim_held_1g_page;
#[cfg(verus_keep_ghost)]
use super::reclaim_held_leaves_eol::*;

verus! {
/// Reclaim the held 4K, 2M and 1G leaves of the write-held `pagetable` in index order from its first user root entry. No user root
/// entry resolves, no CPU is listed stale for the table, no window of it is locked, and no L2 entry of it is locked or hides its
/// L1 page. Each leaf's page is reclaimed and the leaf cleared in its own kernel step, which leaves the user view unchanged, so
/// the walk records no step. Unless `thrd_ptr` runs in `pagetable`, it holds the table's process, which shares its container.
/// The freed quota units accumulate in `indirect_4k`/`direct_4k`, `indirect_2m`/`direct_2m` and `indirect_1g`/`direct_1g`.
pub fn reclaim_held_leaves(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect_4k: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: &mut usize,
    indirect_2m: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: &mut usize, indirect_1g: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct_1g: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
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
        *old(direct_4k) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect_4k)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect_4k)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        *old(direct_2m) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger old(indirect_2m)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect_2m)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        *old(direct_1g) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|depth: int| #![trigger old(indirect_1g)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect_1g)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth),
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
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k,
            direct_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m, indirect_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m,
            direct_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g, indirect_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g,
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
        }),
        *final(direct_4k) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect_4k)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect_4k)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        *final(direct_2m) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger final(indirect_2m)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect_2m)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        *final(direct_1g) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|depth: int| #![trigger final(indirect_1g)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect_1g)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
            &&& new_c.mapping_1g().submap_of(old_c.mapping_1g()) && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i) || new_c.lower.l2_entry(p, i).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index| #![trigger new_c.spec_resolve_mapping_l4(l4i)] old_c.kernel_l4_end() <= l4i && pei_valid(l4i) ==> new_c.spec_resolve_mapping_l4(l4i) == old_c.spec_resolve_mapping_l4(l4i)
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
    let ghost e = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    proof { krnl.default_pagetable_wf_at(pagetable); }
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (KERNEL_MEM_END_L4INDEX, 0, 0, 0);
    proof {
        assert(reclaim_held_leaves_eol_loop_framing(*old(krnl), *krnl, old(lctx), pagetable, thrd_ptr, *indirect_4k, *direct_4k, *indirect_2m, *direct_2m, *indirect_1g, *direct_1g, cursor)) by {
            reveal(reclaim_held_leaves_eol_loop_framing); held_kernel_objects_unchanged_reflexive(krnl, lctx);
        };
    }
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
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).pt_mp.dom().contains(pagetable),
            old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            forall|l4i: L4Index| #![trigger e.spec_resolve_mapping_l4(l4i)] e.kernel_l4_end() <= l4i && pei_valid(l4i) ==> e.spec_resolve_mapping_l4(l4i) is None,
            forall|p: PageMapPtr, i: L2Index| #![trigger e.lower.l2_owner(p, i)] e.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> e.lower.l2_owner(p, i) is None,
            reclaim_held_leaves_eol_loop_framing(*old(krnl), *krnl, old(lctx), pagetable, thrd_ptr, *indirect_4k, *direct_4k, *indirect_2m, *direct_2m, *indirect_1g, *direct_1g, cursor),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        proof { reclaim_held_leaves_eol_iteration_pre(*old(krnl), *krnl, old(lctx), lctx, pagetable, thrd_ptr, *indirect_4k, *direct_4k, *indirect_2m, *direct_2m, *indirect_1g, *direct_1g, cursor); }
        let found = pagetable_map_next_held_leaf_from(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, cursor, Tracked(&*lctx), pagetable_perm);
        if found.is_none() {
            proof { reclaim_held_leaves_eol_exit(*old(krnl), *krnl, old(lctx), pagetable, thrd_ptr, *indirect_4k, *direct_4k, *indirect_2m, *direct_2m, *indirect_1g, *direct_1g, cursor); }
            return;
        }
        let (next, kind, leaf) = found.unwrap();
        cursor = reclaim_held_leaf(krnl, pagetable, thrd_ptr, cpu_id, next, kind, leaf.addr, indirect_4k, direct_4k, indirect_2m, direct_2m, indirect_1g, direct_1g, Tracked(&mut *lctx),
            Tracked(&mut *steps), pagetable_perm, thread_perm, Ghost(*old(krnl)), Ghost(*old(lctx)), Ghost(cursor));
    }
}

/// Reclaim the held leaf `next` of kind `kind` on `pg_ptr`, the first at or after `cursor` in the write-held `pagetable`, and return the path past it; the walk summary from `k0`, `lctx0` moves there.
fn reclaim_held_leaf(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, next: (L4Index, L3Index, L2Index, L1Index), kind: HeldLeaf, pg_ptr: PagePtr,
    indirect_4k: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct_4k: &mut usize, indirect_2m: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct_2m: &mut usize,
    indirect_1g: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct_1g: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, Ghost(k0): Ghost<KernelK>, Ghost(lctx0): Ghost<LocalContext>, Ghost(cursor): Ghost<(L4Index, L3Index, L2Index, L1Index)>,
) -> (ret: (L4Index, L3Index, L2Index, L1Index))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_unchanged(&lctx0, old(lctx)),
        old(lctx).cpu_id() == lctx0.cpu_id(),
        old(lctx).thread_id() == lctx0.thread_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        lctx0.page_lock_map().dom().is_empty(),
        held_locks_order_below(&k0, &lctx0, ALLOCATOR_CACHE_4K_MAJOR),
        lctx0.scheduler_lock_map().dom().is_empty(),
        lctx0.cpu_offline_flag_lock_map().dom().is_empty(),
        lctx0.cpu_set_lock_map().dom().is_empty(),
        lctx0.pagetable_window_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, lctx0.cpu_id()) ==> k0.cpu_op.view().view()[lctx0.cpu_id() as int] is InStep,
        lctx0.cpu_lock_map().dom().contains(lctx0.cpu_id()),
        k0.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(k0.thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(lctx0.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == lctx0.thread_id(),
        thread_perm.view().lock_id() == k0.thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx0.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == lctx0.thread_id(),
        pagetable_perm.view().lock_id() == k0.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        k0.pt_mp.dom().contains(pagetable),
        whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        k0.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        reclaim_held_leaves_eol_loop_framing(k0, *old(krnl), &lctx0, pagetable, thrd_ptr, *old(indirect_4k), *old(direct_4k), *old(indirect_2m), *old(direct_2m), *old(indirect_1g), *old(direct_1g),
            cursor),
        ({
            let c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            &&& c.kernel_l4_end() <= next.0 && pei_valid(next.0) && pei_valid(next.1) && pei_valid(next.2) && pei_valid(next.3)
            &&& spec_l4_index_path_le(cursor, next)
            &&& kind is L1g ==> next.2 == 0 && next.3 == 0 && c.spec_held_1g_l3(next.0, next.1) is Some && c.spec_held_1g_l3(next.0, next.1)->0.addr == pg_ptr
            &&& kind is L2m ==> next.3 == 0 && c.spec_held_2m_l2(next.0, next.1, next.2) is Some && c.spec_held_2m_l2(next.0, next.1, next.2)->0.addr == pg_ptr
            &&& kind is L4k ==> c.spec_held_4k_l1(next.0, next.1, next.2, next.3) is Some && c.spec_held_4k_l1(next.0, next.1, next.2, next.3)->0.addr == pg_ptr
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger c.spec_held_4k_l1(i4, i3, i2, i1)]
                pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && spec_l4_index_path_le(cursor, (i4, i3, i2, i1)) && !spec_l4_index_path_le(next, (i4, i3, i2, i1)) ==> c.spec_held_4k_l1(i4, i3, i2, i1) is None
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger c.spec_held_2m_l2(i4, i3, i2)]
                pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && spec_l4_index_path_le(cursor, (i4, i3, i2, 0)) && !spec_l4_index_path_le(next, (i4, i3, i2, 0)) ==> c.spec_held_2m_l2(i4, i3, i2) is None
            &&& forall|i4: L4Index, i3: L3Index| #![trigger c.spec_held_1g_l3(i4, i3)]
                pei_valid(i4) && pei_valid(i3) && spec_l4_index_path_le(cursor, (i4, i3, 0, 0)) && !spec_l4_index_path_le(next, (i4, i3, 0, 0)) ==> c.spec_held_1g_l3(i4, i3) is None
        }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&lctx0, final(lctx)),
        final(lctx).cpu_id() == lctx0.cpu_id(),
        final(lctx).thread_id() == lctx0.thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        reclaim_held_leaves_eol_loop_framing(k0, *final(krnl), &lctx0, pagetable, thrd_ptr, *final(indirect_4k), *final(direct_4k), *final(indirect_2m), *final(direct_2m), *final(indirect_1g),
            *final(direct_1g), ret),
        kind is L1g ==> ret == (next.0, next.1, 511usize, 512usize),
        kind is L2m ==> ret == (next.0, next.1, next.2, 512usize),
        kind is L4k ==> ret == (next.0, next.1, next.2, (next.3 + 1) as usize),
{
    proof { reclaim_held_leaves_eol_iteration_pre(k0, *krnl, &lctx0, lctx, pagetable, thrd_ptr, *indirect_4k, *direct_4k, *indirect_2m, *direct_2m, *indirect_1g, *direct_1g, cursor); }
    let ghost c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let ghost (krnl_i, lctx_i) = (*krnl, *lctx);
    proof {
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); c.higher.wf_l4_at(next.0);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); page_index_valid_imply_page_ptr_valid();
        assert(krnl.pt_lower.view() =~= krnl.pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
    }
    match kind {
        HeldLeaf::L1g => {
            let va = index2va((next.0, next.1, 0, 0));
            let ghost (indirect_i, direct_i) = (*indirect_1g, *direct_1g);
            proof {
                if c.spec_held_l4(next.0) is Some { c.l3_links_l2_wf_at(c.spec_held_l4(next.0)->0.addr, next.1); }
                spec_index2va_2m_valid(next.0, next.1, 0);
                mapped_1g_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1);
                mapped_1g_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va);
                assert(c.spec_held_l3(next.0, next.1) is None);
            }
            reclaim_held_1g_page(krnl, pagetable, va, pg_ptr, thrd_ptr, indirect_1g, direct_1g, Tracked(&mut *lctx), pagetable_perm, thread_perm);
            let ghost (krnl_c, lctx_c) = (*krnl, *lctx);
            proof {
                kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable));
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
                reclaim_held_leaves_eol_step_1g(k0, krnl_i, krnl_c, *krnl, &lctx0, &lctx_i, &lctx_c, pagetable, thrd_ptr, va, *indirect_4k, *direct_4k, *indirect_2m, *direct_2m, indirect_i,
                    direct_i, *indirect_1g, *direct_1g, cursor, next);
            }
            (next.0, next.1, 511, 512)
        },
        HeldLeaf::L2m => {
            let va = index2va(next);
            let ghost (indirect_i, direct_i) = (*indirect_2m, *direct_2m);
            proof {
                c.l3_links_l2_wf_at(c.spec_held_l4(next.0)->0.addr, next.1); c.wf_l2_at(c.spec_held_l3(next.0, next.1)->0.addr, next.2);
                spec_index2va_2m_valid(next.0, next.1, next.2); spec_va_2m_valid_index_roundtrip(va);
                mapped_2m_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1, next.2);
                mapped_2m_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va);
                assert(c.spec_held_1g_l3(next.0, next.1) is None);
            }
            reclaim_held_2m_page(krnl, pagetable, va, pg_ptr, thrd_ptr, cpu_id, indirect_2m, direct_2m, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
            let ghost (krnl_c, lctx_c) = (*krnl, *lctx);
            proof {
                kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable));
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
                reclaim_held_leaves_eol_step_2m(k0, krnl_i, krnl_c, *krnl, &lctx0, &lctx_i, &lctx_c, pagetable, thrd_ptr, va, *indirect_4k, *direct_4k, indirect_i, direct_i, *indirect_2m,
                    *direct_2m, *indirect_1g, *direct_1g, cursor, next);
            }
            (next.0, next.1, next.2, 512)
        },
        HeldLeaf::L4k => {
            let va = index2va(next);
            let ghost (indirect_i, direct_i) = (*indirect_4k, *direct_4k);
            proof {
                c.l3_links_l2_wf_at(c.spec_held_l4(next.0)->0.addr, next.1); c.wf_l2_at(c.spec_held_l3(next.0, next.1)->0.addr, next.2);
                assert(va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
                mapped_4k_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1, next.2, next.3);
                mapped_4k_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va);
                assert(c.spec_held_1g_l3(next.0, next.1) is None);
            }
            reclaim_held_4k_page(krnl, pagetable, va, pg_ptr, thrd_ptr, cpu_id, indirect_4k, direct_4k, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
            let ghost (krnl_c, lctx_c) = (*krnl, *lctx);
            proof {
                kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable));
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
                reclaim_held_leaves_eol_step_4k(k0, krnl_i, krnl_c, *krnl, &lctx0, &lctx_i, &lctx_c, pagetable, thrd_ptr, va, indirect_i, direct_i, *indirect_4k, *direct_4k, *indirect_2m,
                    *direct_2m, *indirect_1g, *direct_1g, cursor, next);
            }
            (next.0, next.1, next.2, next.3 + 1)
        },
    }
}
}

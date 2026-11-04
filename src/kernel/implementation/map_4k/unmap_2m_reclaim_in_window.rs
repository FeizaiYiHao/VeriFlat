use vstd::prelude::*;
use crate::*;
use super::reclaim_held_2m_page::reclaim_last_lock_2m_cache_with_room;
#[cfg(verus_keep_ghost)]
use super::unmap_2m_reclaim_in_window_eof::*;

verus! {
/// Reads the page that the 2M leaf `va` of the read-held `pagetable` maps and the L2 page holding that leaf.
fn reclaim_unmapped_2m_page_and_l2_ptr(
    krnl: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>,
) -> (ret: (PagePtr, PageMapPtr))
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        indices == (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= indices.0,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures
        ret.0 == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == ret.1,
{
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_2m_at(indices.0, indices.1, indices.2);
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = pt.get_entry_2m_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
    (l2.addr, l3.addr)
}

/// Remove the non-present 2M leaf `va` of the read-held `pagetable` and its record from the page `pg_ptr`, which keeps other
/// references; the caller holds the leaf's window and page, and no CPU is listed stale for the window. Only the window half
/// of the table changes.
fn remove_2m_mapping_without_free_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>,
    page_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr == pg_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().remove(va),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(p, i),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().remove((pagetable, va)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    let indices = va2index(va);
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va));
        assert(window_of(va).va == va);
        page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
    }
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    page_array_remove_2m_mapping_without_free(&mut krnl.pg_arr, pg_idx, pagetable, va, Tracked(&*lctx), page_perm);
    pagetable_map_unmap_2m_kernel_rlocked(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, Tracked(window_perm), Tracked(&mut *lctx),
        pagetable_perm);
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(remove_2m_mapping_without_free_in_window_eof_transition_framing(*old(krnl), *krnl, pagetable, va, pg_ptr, l2_ptr)) by {
            reveal(remove_2m_mapping_without_free_in_window_eof_transition_framing);
        };
        remove_2m_mapping_without_free_in_window_eof(*old(krnl), *krnl, pagetable, va, pg_ptr, l2_ptr);
    }
}

/// Frees the page behind the last mapping, the non-present 2M leaf `va` of the read-held `pagetable`: drains a batch of the
/// owner's 2M CPU cache at its watermark under its own step boundary, then moves the page into that cache, credits the thread's
/// pending free 2M quota at the owner's depth, and removes the leaf. The page lock stays held. Without a drain the steps and
/// their snapshot stay; a drain records the user view of the entry state against the snapshot.
fn reclaim_last_2m_mapping_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, owner: RwLockContainerPtr, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId,
    indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, page_perm: Tracked<&LockPerm>,
    pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_2M_MAJOR),
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, thrd_mp: old(krnl).thrd_mp, allc_2m_mp: old(krnl).allc_2m_mp, ..old(steps).snapshot_k() }),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        old(krnl).pt_lower.view() == old(steps).snapshot_k().pt_lower.view().insert(pagetable, old(krnl).pt_lower.view().spec_index(pagetable)),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr == pg_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count == 1,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(steps).view() == old(steps).view() && final(steps).snapshot_k() == old(steps).snapshot_k()
                && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks
            || final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl)))
                && old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k())
                && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), pagetable).lower.pagetable_window_locks,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..final(steps).snapshot_k() }),
        final(krnl).pt_mp.unchanged_except(&final(steps).snapshot_k().pt_mp, pagetable),
        final(krnl).pt_lower.view() == final(steps).snapshot_k().pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == final(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).thrd_mp.unchanged_except(&final(steps).snapshot_k().thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == final(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        final(krnl).pt_mp.dom().contains(pagetable),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& w.va != va ==> post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& w.va != va && pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
            &&& pei_valid(spec_v2l2index(w.va)) && !pre.lower.l2_entry_hides_l1(pre.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                ==> !post.lower.l2_entry_hides_l1(post.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let ghost pg_idx = page_ptr2page_index(pg_ptr);
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        assert(window_of(va).va == va);
        page_ptr_valid_imply_page_index_valid(); krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); }; container_perms_wf_at(krnl.ctn_mp, owner); }
    let owner_ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
    let depth = owner_ro.depth;
    let allc_ptr = owner_ro.allocator_ptr_2m;
    proof { thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }
    let thread = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
    let thread_depth = thread.container_depth;
    proof {
        let thread_owner = thread.owning_container;
        container_process_page_pagetable_wf_at(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr, pg_idx, pagetable, va);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, thread.owning_proc);
        container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, thread_owner);
        container_subtree_set_wf_at(krnl.rt_ctn, krnl.ctn_mp, owner, thread_owner);
        assert(krnl.allc_2m_mp.dom().contains(allc_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); };
    }
    let ghost drained_pre = *krnl;
    let ghost cache_lctx = *lctx;
    let Tracked(cache_perm) = reclaim_last_lock_2m_cache_with_room(krnl, allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps));
    proof { assert(cache_lctx.pagetable_window_lock_map().dom().contains((pagetable, window_of(va)))); assert(cache_lctx.pagetable_lock_map().dom().contains(pagetable)); }
    assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
        && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
    let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
    remove_last_2m_mapping_to_allocator_in_window(krnl, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, owner, depth, allc_ptr, cpu_id, &mut counter, Tracked(&mut *lctx), page_perm, pagetable_perm, thread_perm,
        Tracked(&cache_perm), Tracked(window_perm));
    if depth == thread_depth { *direct = counter; } else { indirect[depth] = counter; }
    krnl.wunlock_allocator_cache_2m(allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    proof {
        assert(lctx.allocator_cache_2m_lock_map() =~= old(lctx).allocator_cache_2m_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(krnl.pt_lower.view() =~= steps.snapshot_k().pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
    }
}

/// Remove the non-present 2M leaf `va` of the read-held `pagetable` and its record from the page `pg_ptr`, whose last mapping
/// it was, move the page into shard `cpu_id` of the owner allocator's 2M CPU cache, and credit the thread's pending free 2M
/// quota at the owner's depth; the caller holds the leaf's window, the page, the cache and the thread, and no CPU is listed
/// stale for the window.
fn remove_last_2m_mapping_to_allocator_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, counter: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, page_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
    thread_perm: Tracked<&LockPerm>, cache_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr == pg_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count == 1,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_2m_mp.dom().contains(allc_ptr),
        old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.view().state() is WriteLock,
        cache_perm.view().thread_id() == old(lctx).thread_id(),
        cache_perm.view().lock_id() == old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr,
        depth <= old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container } else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        *old(counter) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().remove(va),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(p, i),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        *final(counter) == *old(counter) + 1,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth) == *final(counter),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() + if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { 1int } else { 0int },
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view()
            == if depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().update(depth as int, *final(counter)) }
            else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view() },
        final(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allc_ptr),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    assert(krnl.allc_2m_mp.spec_index(allc_ptr).total_free_pages.view() < usize::MAX) by { kill_container_quota_fold::lemma_container_allocator_2m_quota_bounded(krnl, owner); };
    assert(krnl.allc_2m_mp.spec_index(allc_ptr).quota.view().value as int + *counter as int <= krnl.allc_2m_mp.spec_index(allc_ptr).total_free_pages.view()) by { kernel_inv_implies_thread_pending_2m_quota_bounded(krnl, thrd_ptr, owner, depth); };
    let pg_idx = page_ptr2page_index(pg_ptr);
    let indices = va2index(va);
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va));
        assert(window_of(va).va == va);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
    }
    assert(krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr && index_valid(NUM_PAGES, pg_idx) && krnl.pg_arr.spec_index(pg_idx).view().is_init()) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, pg_idx); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    assert(krnl.thrd_mp.spec_index(thrd_ptr).is_init() && krnl.allc_2m_mp.perms_wf() && krnl.allc_2m_mp.spec_index(allc_ptr).wf() && !krnl.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)) by {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, allc_ptr);
        allocator_free_2m_pages_wf_cache_at(krnl.allc_2m_mp, krnl.pg_arr, allc_ptr, cpu_id, pg_ptr);
    };
    let (node_addr, node_perm) = page_array_remove_last_2m_mapping_to_cache(&mut krnl.pg_arr, pg_idx, pagetable, va, allc_ptr, cpu_id, Tracked(&*lctx), page_perm);
    krnl.allc_2m_mp.push_cache_page_typed(allc_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), cache_perm);
    thread_map_add_free_quota_pending_2m(&mut krnl.thrd_mp, thrd_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    pagetable_map_unmap_2m_kernel_rlocked(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, Tracked(window_perm), Tracked(&mut *lctx),
        pagetable_perm);
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(pg_idx), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
        assert(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(*old(krnl), *krnl, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, *old(counter), *counter, node_addr))
            by { reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing); };
        remove_last_2m_mapping_to_allocator_in_window_eof(*old(krnl), *krnl, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, owner, depth, allc_ptr, cpu_id, *old(counter), *counter, node_addr);
        held_threads_unchanged_except_for_unchanged_except(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx), thrd_ptr);
    }
}

/// Reclaim the non-present 2M leaf `va` of the read-held `pagetable` after its stale TLB entries are flushed: the caller holds
/// the leaf's window; lock its page, drop the mapping or free the page behind the last mapping, and unlock the page. Only the
/// held windows of the table keep their leaves across the step.
pub fn reclaim_unmapped_2m_page_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
    Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_2M_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& w.va != va ==> post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& w.va != va && pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
            &&& pei_valid(spec_v2l2index(w.va)) && !pre.lower.l2_entry_hides_l1(pre.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                ==> !post.lower.l2_entry_hides_l1(post.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let indices = va2index(va);
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va));
        assert(window_of(va).va == va);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_2m_at(indices.0, indices.1, indices.2);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq(indices.0, indices.1, indices.2);
        mapped_2m_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, indices.0, indices.1, indices.2);
    }
    let (pg_ptr, l2_ptr) = reclaim_unmapped_2m_page_and_l2_ptr(krnl, pagetable, va, (indices.0, indices.1, indices.2), Tracked(&*lctx), pagetable_perm);
    let pg_idx = page_ptr2page_index(pg_ptr);
    proof { mapped_2m_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pg_idx, pagetable, va); page_index_valid_imply_page_ptr_valid(); }
    let Tracked(page_perm) = krnl.wlock_page(pg_idx, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); }
    let page = krnl.pg_arr.borrow_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        assert(krnl.pt_lower.view() =~= steps.snapshot_k().pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
    }
    if page.ref_count > 1 {
        remove_2m_mapping_without_free_in_window(krnl, pagetable, va, pg_ptr, l2_ptr, Tracked(&mut *lctx), pagetable_perm, Tracked(&page_perm), Tracked(window_perm));
    } else {
        reclaim_last_2m_mapping_in_window(krnl, pagetable, va, pg_ptr, l2_ptr, page.owning_container, thrd_ptr, cpu_id, indirect, direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&page_perm),
            pagetable_perm, thread_perm, Tracked(window_perm));
    }
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}
}

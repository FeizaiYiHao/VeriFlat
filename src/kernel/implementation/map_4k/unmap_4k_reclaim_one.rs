use vstd::prelude::*;
use crate::*;
use super::unmap_4k_remove::{remove_4k_mapping_without_free, remove_4k_mapping_without_free_in_window};
use super::unmap_4k_reclaim_last::reclaim_last_4k_mapping;

verus! {
/// Reclaim the hidden 4K leaf `va` of the write-held `pagetable` after its stale TLB entries are flushed: lock its window
/// and page, drop the mapping or free the page behind the last mapping, and unlock both.
#[verifier::spinoff_prover]
pub fn reclaim_unmapped_4k_page(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable || old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
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
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().remove(va),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
{
    let indices = va2index(va);
    let ghost window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
    proof {
        let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
    }
    let Tracked(window_perm) = krnl.lock_pagetable_window(pagetable, indices.0, indices.1, indices.2, pagetable_perm, Tracked(&mut *lctx));
    reclaim_unmapped_4k_page_under_window(krnl, pagetable, va, thread_ptr, cpu_id, indirect, direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
    krnl.unlock_pagetable_window(pagetable, indices.0, indices.1, indices.2, pagetable_perm, Tracked(&mut *lctx), Tracked(window_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).pagetable_window_lock_map(), (pagetable, window_va), TypedHeldLock { lock_id: window_lock_id_of(pagetable, window_va), mode: TypedLockMode::Write });
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thread_ptr), None, Some(pagetable));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}

/// Under the held window of leaf `va` of the write-held `pagetable`, reclaim the hidden leaf: lock its page, drop the
/// mapping or free the page behind the last mapping, and unlock the page.
fn reclaim_unmapped_4k_page_under_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..old(steps).snapshot_k() }),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable || old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize)) }), TypedLockMode::Write),
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..final(steps).snapshot_k() }),
        final(krnl).pt_mp.unchanged_except(&final(steps).snapshot_k().pt_mp, pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == final(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).thr_mp.unchanged_except(&final(steps).snapshot_k().thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == final(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().remove(va),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_lock,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
{
    let indices = va2index(va);
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
    }
    let page_ptr;
    {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
        let l4 = pt.get_entry_l4(indices.0).unwrap();
        let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
        page_ptr = pt.get_entry_l1(Tracked(lower), indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr;
    }
    let page_index = page_ptr2page_index(page_ptr);
    proof { mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, va); }
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if page.ref_count > 1 || page.is_io_page {
        remove_4k_mapping_without_free(krnl, pagetable, va, page_ptr, Tracked(&mut *lctx), pagetable_perm, Tracked(&page_perm));
        proof {
            assert(held_threads_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), set![thread_ptr])) by { old(krnl).thr_mp.typed_lock_map_aligned_held_in_dom(old(lctx).thread_lock_map(), old(lctx).thread_id()); };
            assert(held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))) by { old(krnl).ctn_mp.typed_lock_map_aligned_held_in_dom(old(lctx).container_lock_map(), old(lctx).thread_id()); };
            assert(held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))) by { old(krnl).prc_mp.typed_lock_map_aligned_held_in_dom(old(lctx).process_lock_map(), old(lctx).thread_id()); };
            assert(held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))) by { old(krnl).it_mp.typed_lock_map_aligned_held_in_dom(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()); };
            assert(held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))) by { reveal(LockedArray::typed_lock_map_aligned); };
        }
    } else {
        reclaim_last_4k_mapping(krnl, pagetable, va, page_ptr, page.owning_container, thread_ptr, cpu_id, indirect, direct, true, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, Tracked(&page_perm),
            thread_perm);
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
}

/// Reclaim the hidden 4K leaf `va` of the read-held `pagetable` after its stale TLB entries are flushed: the caller holds
/// the leaf's window; lock its page, drop the mapping or free the page behind the last mapping, and unlock the page. Only
/// the held windows of the table keep their leaves across the step.
pub fn reclaim_unmapped_4k_page_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
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
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            let pre = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) && v != va ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let indices = va2index(va);
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        spec_va_4k_index_roundtrip_at(window_of(va).va, indices.0, indices.1, indices.2, 0usize);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
    }
    let page_ptr;
    {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
        let l4 = pt.get_entry_l4(indices.0).unwrap();
        let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
        page_ptr = pt.get_entry_l1(Tracked(lower), indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr;
    }
    let page_index = page_ptr2page_index(page_ptr);
    proof { mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, va); }
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    let ghost page_lctx = *lctx;
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if page.ref_count > 1 || page.is_io_page {
        remove_4k_mapping_without_free_in_window(krnl, pagetable, va, page_ptr, Tracked(&mut *lctx), pagetable_perm, Tracked(&page_perm));
    } else {
        reclaim_last_4k_mapping(krnl, pagetable, va, page_ptr, page.owning_container, thread_ptr, cpu_id, indirect, direct, false, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, Tracked(&page_perm),
            thread_perm);
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    let ghost unlocked = *krnl;
    let ghost unlocked_lctx = *lctx;
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thread_ptr), None, Some(pagetable));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}
}

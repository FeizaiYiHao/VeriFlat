use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn allocate_new_process_with_iommu_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    current_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (PagePtr, PagePtr, PagePtr, PagePtr, PagePtr, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 5,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        ret.0 != ret.1 && ret.0 != ret.2 && ret.0 != ret.3 && ret.0 != ret.4
            && ret.1 != ret.2 && ret.1 != ret.3 && ret.1 != ret.4
            && ret.2 != ret.3 && ret.2 != ret.4 && ret.3 != ret.4,
        page_ptr_valid(ret.0) && page_ptr_valid(ret.1) && page_ptr_valid(ret.2) && page_ptr_valid(ret.3) && page_ptr_valid(ret.4),
        final(lctx).page_lock_map().dom() == set![page_ptr2page_index(ret.0), page_ptr2page_index(ret.1), page_ptr2page_index(ret.2), page_ptr2page_index(ret.3), page_ptr2page_index(ret.4)],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![ret.0, ret.1, ret.2, ret.3, ret.4],
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.1), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.2), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.3), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.4), TypedLockMode::Write),
        ret.5.view().state() is WriteLock && ret.5.view().thread_id() == final(lctx).thread_id() && ret.5.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
        ret.6.view().state() is WriteLock && ret.6.view().thread_id() == final(lctx).thread_id() && ret.6.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().locking_thread()->Write_lock_id,
        ret.7.view().state() is WriteLock && ret.7.view().thread_id() == final(lctx).thread_id() && ret.7.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().locking_thread()->Write_lock_id,
        ret.8.view().state() is WriteLock && ret.8.view().thread_id() == final(lctx).thread_id() && ret.8.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().locking_thread()->Write_lock_id,
        ret.9.view().state() is WriteLock && ret.9.view().thread_id() == final(lctx).thread_id() && ret.9.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().locking_thread()->Write_lock_id,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
{
    let (pages, Tracked(mut page_lock_perms)) = allocate_free_4k_pages::<5>(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm));
    let process_page_ptr = *pages.get(0);
    let pagetable_page_ptr = *pages.get(1);
    let l4_page_ptr = *pages.get(2);
    let iommu_table_page_ptr = *pages.get(3);
    let iommu_l4_page_ptr = *pages.get(4);
    proof {
        assert(page_lock_perms.dom().contains(process_page_ptr)
            && page_lock_perms.dom().contains(pagetable_page_ptr)
            && page_lock_perms.dom().contains(l4_page_ptr)
            && page_lock_perms.dom().contains(iommu_table_page_ptr)
            && page_lock_perms.dom().contains(iommu_l4_page_ptr)) by {
            pages.view().to_set_ensures();
        };
        assert(
            process_page_ptr != pagetable_page_ptr && process_page_ptr != l4_page_ptr
                && process_page_ptr != iommu_table_page_ptr && process_page_ptr != iommu_l4_page_ptr
                && pagetable_page_ptr != l4_page_ptr && pagetable_page_ptr != iommu_table_page_ptr
                && pagetable_page_ptr != iommu_l4_page_ptr && l4_page_ptr != iommu_table_page_ptr
                && l4_page_ptr != iommu_l4_page_ptr && iommu_table_page_ptr != iommu_l4_page_ptr
        ) by { seq_index_lemma::<PagePtr>(); };
        assert(page_ptrs_to_indices(pages.view()) =~= set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)]) by {
            pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set_ensures();
            assert_sets_equal!(page_ptrs_to_indices(pages.view()) == set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)]);
        };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr]) by { pages.view().to_set_ensures(); assert_sets_equal!(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr]); };
    }
    let tracked process_page_lock_perm = page_lock_perms.tracked_remove(process_page_ptr);
    let tracked pagetable_page_lock_perm = page_lock_perms.tracked_remove(pagetable_page_ptr);
    let tracked l4_page_lock_perm = page_lock_perms.tracked_remove(l4_page_ptr);
    let tracked iommu_table_page_lock_perm = page_lock_perms.tracked_remove(iommu_table_page_ptr);
    let tracked iommu_l4_page_lock_perm = page_lock_perms.tracked_remove(iommu_l4_page_ptr);
    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    (process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm))
}
}

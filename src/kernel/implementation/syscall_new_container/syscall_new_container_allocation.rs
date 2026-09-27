use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn allocate_new_container_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    current_thread_ptr: RwLockThreadPtr, parent_container_ptr: RwLockContainerPtr, caller_cpu_id: CpuId,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>
) -> (ret: (ArrayVec<PagePtr, 9>, PagePtr, PagePtr, Tracked<Map<PagePtr, LockPerm>>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, caller_cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k >= 9,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_2m >= 2,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page) ==> final(krnl).pg_arr.lock_id_by_index(held_page).major < ALLOCATOR_CACHE_MAJOR,
        ret.0.wf(),
        ret.0.len() == 9,
        ret.0.view().no_duplicates(),
        page_ptrs_to_indices(ret.0.view()) == set![
            page_ptr2page_index(ret.0.view().spec_index(0)), page_ptr2page_index(ret.0.view().spec_index(1)), page_ptr2page_index(ret.0.view().spec_index(2)),
            page_ptr2page_index(ret.0.view().spec_index(3)), page_ptr2page_index(ret.0.view().spec_index(4)), page_ptr2page_index(ret.0.view().spec_index(5)),
            page_ptr2page_index(ret.0.view().spec_index(6)), page_ptr2page_index(ret.0.view().spec_index(7)), page_ptr2page_index(ret.0.view().spec_index(8)),
        ],
        !final(krnl).thr_mp.dom().contains(ret.0.view().spec_index(7)),
        ret.3.view().dom() == ret.0.view().to_set(),
        allocated_4k_page_lock_perms_wf(ret.3.view(), final(krnl), final(lctx), current_thread_ptr, parent_container_ptr),
        ret.0.view().to_set().subset_of(
            final(krnl).ctn_mp.spec_index(parent_container_ptr)
                .view().owned_pages.view(),
        ),
        ret.1 != ret.2,
        page_ptr_valid(ret.2),
        page_ptr_2m_valid(ret.1),
        page_ptr_2m_valid(ret.2),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1))
            .view().view().owning_container == parent_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2))
            .view().view().owning_container == parent_container_ptr,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.1), TypedLockMode::Write),
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.2), TypedLockMode::Write),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view() == ret.0.view().to_set(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_2m.view() == set![ret.1, ret.2],
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_proc
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().owning_proc,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().proc_pagetable_ptr
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state
            == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_2m
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_2m,
        thread_effective_quota_4k(final(krnl).thr_mp.spec_index(current_thread_ptr)) == thread_effective_quota_4k(
            old(krnl).thr_mp.spec_index(current_thread_ptr)
        ) - 9,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.lock_id()
            == final(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        final(lctx).page_lock_map().dom()
            == page_ptrs_to_indices(ret.0.view()).union(seq![page_ptr2page_index(ret.1), page_ptr2page_index(ret.2)].to_set()),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map()
            == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map()
            == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map()
            == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map()
            == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map()
            == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps()
            == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps()
            == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps()
            == old(lctx).allocator_1g_lock_maps(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![current_thread_ptr]),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };


    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    let (pages_4k, Tracked(page_4k_lock_perms)) = allocate_free_4k_pages::<9>(
        krnl, current_thread_ptr, parent_container_ptr, caller_cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(current_thread_lock_perm)
    );
    let ghost staged_4k_cache = krnl.thr_mp
        .spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view();
    let ghost effective_2m_before_container = thread_effective_quota_2m(krnl.thr_mp.spec_index(current_thread_ptr));
    proof {
        assert(staged_4k_cache == pages_4k.view().to_set()) by {
            vstd::set::axiom_set_ext_equal(staged_4k_cache, pages_4k.view().to_set());
        };
    }
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
    let (container_page, Tracked(container_page_lock_perm)) = allocate_free_2m_page(
        krnl, current_thread_ptr, parent_container_ptr, caller_cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(current_thread_lock_perm)
    );
    let ghost effective_2m_before_pcid_allocator = thread_effective_quota_2m(krnl.thr_mp.spec_index(current_thread_ptr));

    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); }; }
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
    let (pcid_allocator_page, Tracked(pcid_allocator_page_lock_perm)) = allocate_free_2m_page(
        krnl, current_thread_ptr, parent_container_ptr, caller_cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(current_thread_lock_perm)
    );
    proof {
        assert(page_ptrs_to_indices(pages_4k.view()) == set![
            page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(8)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)), page_ptr2page_index(pages_4k.view().spec_index(7)),
        ]) by {
            let mapped = pages_4k.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr));
            assert(mapped.to_set().contains(mapped.spec_index(0)) && mapped.to_set().contains(mapped.spec_index(1))
                && mapped.to_set().contains(mapped.spec_index(2)) && mapped.to_set().contains(mapped.spec_index(3))
                && mapped.to_set().contains(mapped.spec_index(4)) && mapped.to_set().contains(mapped.spec_index(5))
                && mapped.to_set().contains(mapped.spec_index(6)) && mapped.to_set().contains(mapped.spec_index(7))
                && mapped.to_set().contains(mapped.spec_index(8))) by { mapped.to_set_ensures(); };
            assert_sets_equal!(page_ptrs_to_indices(pages_4k.view()) == set![
                page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
                page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(8)), page_ptr2page_index(pages_4k.view().spec_index(4)),
                page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)), page_ptr2page_index(pages_4k.view().spec_index(7)),
            ], page_index => { mapped.to_set_ensures(); });
        };
        assert(page_index_2m_valid(page_ptr2page_index(container_page)))
            by {
                reveal(hugepage_2m_wf);
            };
        assert(page_index_2m_valid(page_ptr2page_index(pcid_allocator_page))) by { reveal(hugepage_2m_wf); };
        page_ptr_roundtrip();
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr)
                .view().temp_alloc_cache_2m.view()
                == set![container_page, pcid_allocator_page]
        ) by {
            assert_sets_equal!(
                krnl.thr_mp.spec_index(current_thread_ptr)
                    .view().temp_alloc_cache_2m.view()
                    == set![container_page, pcid_allocator_page]
            );
        };
        assert(
            lctx.page_lock_map().dom()
                == page_ptrs_to_indices(pages_4k.view()).union(seq![
                    page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)
                ].to_set())
        ) by {
            seq![page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)].to_set_ensures();
        };
        assert(pages_4k.view().to_set().subset_of(
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_pages.view(),
        )) by {
            pages_4k.view().to_set_ensures();
            page_ptr_roundtrip();
            reveal(container_page_owner_wf);
        };
        assert(!krnl.thr_mp.dom().contains(pages_4k.view().spec_index(7))) by {
            assert(page_4k_lock_perms.dom().contains(pages_4k.view().spec_index(7))) by { pages_4k.view().to_set_ensures(); };
            reveal(thread_pages_wf);
            page_ptr_roundtrip();
        };
    }
    (
        pages_4k, container_page, pcid_allocator_page, Tracked(page_4k_lock_perms), Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm)
    )
}
}

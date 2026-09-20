use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn allocate_staged_4k_page_chain(
    krnl: &mut KernelK, count: usize, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (PagePtr, Ghost<Seq<PagePtr>>, Tracked<Map<PagePtr, LockPerm>>))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr)
            .view().owning_container == container_ptr,
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id()
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        thread_effective_quota_4k(
            old(krnl).thr_mp.spec_index(thread_ptr),
        ) >= count,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        ret.1@.len() == count,
        ret.1@.no_duplicates(),
        ret.0 == staged_4k_page_chain_head(ret.1@),
        staged_4k_page_chain(final(krnl).pg_arr, ret.1@),
        ret.2@.dom() == ret.1@.to_set(),
        allocated_4k_page_lock_perms_wf(
            ret.2@,
            final(krnl),
            final(lctx),
            thread_ptr,
            container_ptr,
        ),
        ret.1@.to_set().subset_of(
            final(krnl).ctn_mp.spec_index(container_ptr)
                .view().owned_pages.view(),
        ),
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().temp_alloc_cache_4k.view()
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_4k.view()
                .union(ret.1@.to_set()),
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().quota_4k
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().temp_alloc_cache_2m
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().temp_alloc_cache_1g
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().quota_2m
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().quota_2m,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().quota_1g
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().quota_1g,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().free_quota_pending_fields_equal(
                &old(krnl).thr_mp.spec_index(thread_ptr).view(),
            ),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().owning_container
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().owning_container,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().owning_proc
            == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(thread_ptr)
            .view().proc_pagetable_ptr
            == old(krnl).thr_mp.spec_index(thread_ptr)
                .view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state
            == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        thread_effective_quota_4k(
            final(krnl).thr_mp.spec_index(thread_ptr),
        ) == thread_effective_quota_4k(
            old(krnl).thr_mp.spec_index(thread_ptr),
        ) - count,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.lock_id()
            == final(krnl).thr_mp.spec_index(thread_ptr)
                .locking_thread()->Write_lock_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(ret.1.view())) == old(lctx).page_lock_map(),
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom().union(
                page_ptrs_to_indices(ret.1@),
            ),
        page_ptrs_to_indices(ret.1@).disjoint(
            old(lctx).page_lock_map().dom(),
        ),
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
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        held_pages_unchanged(
            old(krnl).pg_arr,
            final(krnl).pg_arr,
            old(lctx),
        ),
        held_threads_unchanged_except(
            old(krnl).thr_mp,
            final(krnl).thr_mp,
            old(lctx),
            set![thread_ptr],
        ),
        held_containers_unchanged(
            old(krnl).ctn_mp,
            final(krnl).ctn_mp,
            old(lctx),
        ),
        held_processes_unchanged(
            old(krnl).prc_mp,
            final(krnl).prc_mp,
            old(lctx),
        ),
        held_endpoints_unchanged(
            old(krnl).ep_mp,
            final(krnl).ep_mp,
            old(lctx),
        ),
        held_schedulers_unchanged(
            old(krnl).sched_mp,
            final(krnl).sched_mp,
            old(lctx),
        ),
        held_pcid_allocators_unchanged(
            old(krnl).pcid_allc_mp,
            final(krnl).pcid_allc_mp,
            old(lctx),
        ),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_pagetables_unchanged(
            old(krnl).pt_mp,
            final(krnl).pt_mp,
            old(lctx),
        ),
        held_iommu_tables_unchanged(
            old(krnl).it_mp,
            final(krnl).it_mp,
            old(lctx),
        ),
        held_cpus_unchanged(
            old(krnl).cpu_arr,
            final(krnl).cpu_arr,
            old(lctx),
        ),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot
            == kernel_k_to_kernel_u(*final(krnl)),
{
    let mut head = STAGED_4K_PAGE_CHAIN_END;
    let ghost mut page_ptrs = Seq::<PagePtr>::empty();
    let tracked mut page_lock_perms:
        Map<PagePtr, LockPerm> = Map::tracked_empty();
    let mut i = 0usize;
    proof {
        broadcast use group_held_objects_unchanged_transitive;
        assert(krnl.ctn_mp.dom().contains(container_ptr)) by {
            reveal(container_thread_wf);
        };
        assert(
            krnl.thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_4k.view()
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_4k.view()
                    .union(page_ptrs.to_set())
        ) by {
            vstd::set::axiom_set_ext_equal(
                krnl.thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_4k.view(),
                old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_4k.view()
                    .union(page_ptrs.to_set()),
            );
        };
    }
    while i < count
        invariant
            forall|pt: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                    ==> old(krnl).pt_mp.dom().contains(pt),
            forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            krnl.ctn_mp.dom().contains(container_ptr),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            !krnl.thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.thr_mp.spec_index(thread_ptr)
                .view().owning_container == container_ptr,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().owning_proc
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().owning_proc,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().proc_pagetable_ptr
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().state
                == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == lctx.thread_id(),
            thread_lock_perm.lock_id()
                == krnl.thr_mp.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            lctx.kernel_view_locking_state() is Acquire,
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            page_ptrs.len() == i,
            page_ptrs.no_duplicates(),
            head == staged_4k_page_chain_head(page_ptrs),
            staged_4k_page_chain(krnl.pg_arr, page_ptrs),
            page_lock_perms.dom() == page_ptrs.to_set(),
            allocated_4k_page_lock_perms_wf(
                page_lock_perms,
                krnl,
                lctx,
                thread_ptr,
                container_ptr,
            ),
            krnl.thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_4k.view()
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_4k.view()
                    .union(page_ptrs.to_set()),
            krnl.thr_mp.spec_index(thread_ptr)
                .view().quota_4k
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().quota_4k,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_2m
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_2m,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_1g
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_1g,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().quota_2m
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().quota_2m,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().quota_1g
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().quota_1g,
            krnl.thr_mp.spec_index(thread_ptr)
                .view().free_quota_pending_fields_equal(
                    &old(krnl).thr_mp.spec_index(thread_ptr).view(),
                ),
            thread_effective_quota_4k(
                krnl.thr_mp.spec_index(thread_ptr),
            ) == thread_effective_quota_4k(
                old(krnl).thr_mp.spec_index(thread_ptr),
            ) - i,
            thread_effective_quota_4k(
                krnl.thr_mp.spec_index(thread_ptr),
            ) >= count - i,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            lctx.page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)) == old(lctx).page_lock_map(),
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom().union(
                    page_ptrs_to_indices(page_ptrs),
                ),
            page_ptrs_to_indices(page_ptrs).disjoint(
                old(lctx).page_lock_map().dom(),
            ),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map()
                == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map()
                == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps()
                == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps()
                == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps()
                == old(lctx).allocator_1g_lock_maps(),
            typed_lock_maps_aligned(krnl, lctx),
            lock_id_set_aligned(lctx),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            held_pages_unchanged(
                old(krnl).pg_arr,
                krnl.pg_arr,
                old(lctx),
            ),
            held_threads_unchanged_except(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(lctx),
                set![thread_ptr],
            ),
            held_containers_unchanged(
                old(krnl).ctn_mp,
                krnl.ctn_mp,
                old(lctx),
            ),
            held_processes_unchanged(
                old(krnl).prc_mp,
                krnl.prc_mp,
                old(lctx),
            ),
            held_endpoints_unchanged(
                old(krnl).ep_mp,
                krnl.ep_mp,
                old(lctx),
            ),
            held_schedulers_unchanged(
                old(krnl).sched_mp,
                krnl.sched_mp,
                old(lctx),
            ),
            held_pcid_allocators_unchanged(
                old(krnl).pcid_allc_mp,
                krnl.pcid_allc_mp,
                old(lctx),
            ),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(
                old(krnl).pt_mp,
                krnl.pt_mp,
                old(lctx),
            ),
            held_iommu_tables_unchanged(
                old(krnl).it_mp,
                krnl.it_mp,
                old(lctx),
            ),
            held_cpus_unchanged(
                old(krnl).cpu_arr,
                krnl.cpu_arr,
                old(lctx),
            ),
            steps.steps == old(steps).steps,
            0 <= i <= count,
        decreases count - i,
    {
        let ghost pages_before_allocate = krnl.pg_arr;
        let ghost lctx_before_allocate = *lctx;
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(
                krnl,
                thread_ptr,
                container_ptr,
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(thread_lock_perm),
            );
        proof {
            assert(!page_ptrs.contains(page_ptr)
                && !page_ptrs.to_set().contains(page_ptr)) by {
                page_ptrs.to_set_ensures();
            };
            assert(held_pages_unchanged(
                pages_before_allocate,
                krnl.pg_arr,
                &lctx_before_allocate,
            )) by {
                reveal(held_pages_unchanged);
                reveal(held_pages_unchanged_except);
            };
            assert(staged_4k_page_chain(krnl.pg_arr, page_ptrs)) by {
                broadcast use page_ptr_sequence_index_in_equal_set;
                reveal(allocated_4k_page_lock_perms_wf);
                reveal(typed_lock_map_contains_mode);
                reveal(held_pages_unchanged);
                reveal(staged_4k_page_chain);
            };
            assert(
                lctx.page_lock_map().dom()
                    == old(lctx).page_lock_map().dom().union(
                        page_ptrs_to_indices(page_ptrs.push(page_ptr)),
                    )
            ) by {
                seq_push_lemma::<PagePtr>();
                assert_sets_equal!(
                    lctx.page_lock_map().dom()
                        == old(lctx).page_lock_map().dom().union(
                            page_ptrs_to_indices(
                                page_ptrs.push(page_ptr),
                            ),
                        ),
                    page_index => {
                        broadcast use Seq::lemma_push_map_commute;
                        page_ptrs.map_values(
                            |p: PagePtr| page_ptr2page_index(p),
                        ).to_set_ensures();
                        page_ptrs.map_values(
                            |p: PagePtr| page_ptr2page_index(p),
                        ).push(page_ptr2page_index(page_ptr))
                            .to_set_ensures();
                        broadcast use vstd::set::lemma_set_insert_same;
                        broadcast use vstd::set::lemma_set_insert_different;
                        broadcast use vstd::set::lemma_set_union;
                    }
                );
            };
            assert(
                !old(lctx).page_lock_map().dom().contains(
                    page_ptr2page_index(page_ptr),
                )
            ) by {
                if old(lctx).page_lock_map().dom().contains(
                    page_ptr2page_index(page_ptr),
                ) {
                    assert(
                        lctx_before_allocate.page_lock_map().dom()
                            .contains(page_ptr2page_index(page_ptr))
                    ) by {
                        reveal(Set::contains);
                    };
                }
            };
            assert(
                page_ptrs_to_indices(page_ptrs.push(page_ptr))
                    .disjoint(old(lctx).page_lock_map().dom())
            ) by {
                reveal(page_ptrs_to_indices);
                seq_push_lemma::<PagePtr>();
                assert_sets_equal!(
                    page_ptrs.push(page_ptr).map_values(
                        |p: PagePtr| page_ptr2page_index(p),
                    ).to_set()
                        == page_ptrs.map_values(
                            |p: PagePtr| page_ptr2page_index(p),
                        ).to_set().insert(page_ptr2page_index(page_ptr)),
                    page_index => {
                        broadcast use Seq::lemma_push_map_commute;
                        page_ptrs.map_values(
                            |p: PagePtr| page_ptr2page_index(p),
                        ).to_set_ensures();
                        page_ptrs.map_values(
                            |p: PagePtr| page_ptr2page_index(p),
                        ).push(page_ptr2page_index(page_ptr))
                            .to_set_ensures();
                        broadcast use vstd::set::lemma_set_insert_same;
                        broadcast use vstd::set::lemma_set_insert_different;
                    }
                );
                reveal(Set::disjoint);
            };
        }
        let ghost pages_before_staging_next = krnl.pg_arr;
        set_4k_page_staging_next(
            krnl,
            Tracked(&*lctx),
            page_ptr,
            head,
            Tracked(&page_lock_perm),
        );
        proof {
            assert(staged_4k_page_chain(
                krnl.pg_arr,
                page_ptrs,
            )) by {
                assert(staged_4k_page_chain(
                    pages_before_staging_next,
                    page_ptrs,
                ));
                broadcast use page_ptr_sequence_index_in_equal_set;
                page_ptr2page_index_injective();
                reveal(LockedArray::entries_unchanged_except);
                reveal(staged_4k_page_chain);
            };
            assert(staged_4k_page_chain(
                krnl.pg_arr,
                page_ptrs.push(page_ptr),
            )) by {
                assert(
                    krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                        .view().view().free_list == head
                );
                assert(head == if page_ptrs.len() == 0 {
                    STAGED_4K_PAGE_CHAIN_END
                } else {
                    page_ptrs.last()
                }) by {
                    reveal(staged_4k_page_chain_head);
                };
                vstd::seq::lemma_seq_push_len(page_ptrs, page_ptr);
                vstd::seq::lemma_seq_push_index_same(
                    page_ptrs,
                    page_ptr,
                    page_ptrs.len() as int,
                );
                if page_ptrs.len() > 0 {
                    assert(head == page_ptrs.spec_index(
                        page_ptrs.len() - 1,
                    ));
                    vstd::seq::lemma_seq_push_index_different(
                        page_ptrs,
                        page_ptr,
                        page_ptrs.len() - 1,
                    );
                    assert(page_ptrs.push(page_ptr).spec_index(
                        page_ptrs.len() - 1,
                    ) == head);
                }
                reveal(staged_4k_page_chain);
                reveal(staged_4k_page_chain_head);
                seq_push_lemma::<PagePtr>();
                page_ptrs.to_set_ensures();
                page_ptr2page_index_injective();
                broadcast use vstd::seq::lemma_seq_push_len;
                broadcast use vstd::seq::lemma_seq_push_index_same;
                broadcast use vstd::seq::lemma_seq_push_index_different;
            };
            assert(
                krnl.thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_4k.view()
                    == old(krnl).thr_mp.spec_index(thread_ptr)
                        .view().temp_alloc_cache_4k.view()
                        .union(page_ptrs.push(page_ptr).to_set())
            ) by {
                assert_sets_equal!(
                    old(krnl).thr_mp.spec_index(thread_ptr)
                        .view().temp_alloc_cache_4k.view()
                        .union(page_ptrs.to_set()).insert(page_ptr)
                        == old(krnl).thr_mp.spec_index(thread_ptr)
                            .view().temp_alloc_cache_4k.view()
                            .union(page_ptrs.push(page_ptr).to_set()),
                    x => {
                        seq_push_lemma::<PagePtr>();
                        page_ptrs.to_set_ensures();
                        page_ptrs.push(page_ptr).to_set_ensures();
                        broadcast use vstd::set::lemma_set_insert_same;
                        broadcast use vstd::set::lemma_set_insert_different;
                        broadcast use vstd::set::lemma_set_union;
                    }
                );
            };
            assert(
                page_lock_perms.insert(page_ptr, page_lock_perm).dom()
                    == page_ptrs.push(page_ptr).to_set()
            ) by {
                broadcast use vstd::map::lemma_map_insert_domain;
                assert_sets_equal!(
                    page_lock_perms.insert(page_ptr, page_lock_perm).dom()
                        == page_ptrs.push(page_ptr).to_set(),
                    x => {
                        seq_push_lemma::<PagePtr>();
                        page_ptrs.to_set_ensures();
                        page_ptrs.push(page_ptr).to_set_ensures();
                        broadcast use vstd::set::lemma_set_insert_same;
                        broadcast use vstd::set::lemma_set_insert_different;
                    }
                );
            };
            assert(allocated_4k_page_lock_perms_wf(
                page_lock_perms.insert(page_ptr, page_lock_perm),
                krnl,
                lctx,
                thread_ptr,
                container_ptr,
            )) by {
                page_ptr2page_index_injective();
                broadcast use vstd::map::lemma_map_insert_same;
                broadcast use vstd::map::axiom_map_insert_different;
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
            };
            page_lock_perms.tracked_insert(page_ptr, page_lock_perm);
            page_ptrs = page_ptrs.push(page_ptr);
        }
        head = page_ptr;
        i = i + 1;
    }
    proof {
        assert(page_ptrs.to_set().subset_of(
            krnl.ctn_mp.spec_index(container_ptr)
                .view().owned_pages.view(),
        )) by {
            page_ptrs.to_set_ensures();
            page_ptr_roundtrip();
            reveal(Set::subset_of);
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(container_page_owner_wf);
        };
    }
    (
        head,
        Ghost(page_ptrs),
        Tracked(page_lock_perms),
    )
}


}

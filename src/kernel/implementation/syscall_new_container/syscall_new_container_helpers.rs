use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
#[cfg(not(feature = "split-crates"))]
use crate::implementation::create_thread_from_staged_page::
    create_thread_from_staged_page_merged;
use super::staged_4k_page_chain::{
    allocate_staged_4k_page_chain,
    cleanup_published_4k_page_chain,
    page_ptr_sets_disjoint_from_index_disjoint,
    set_disjoint_from_right_subset,
    set_union_subset_of,
};

verus! {
#[verifier::spinoff_prover]
pub(super) fn allocate_new_container_pages(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    current_thread_ptr: RwLockThreadPtr,
    parent_container_ptr: RwLockContainerPtr,
    caller_cpu_id: CpuId,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (
    ArrayVec<PagePtr, 8>,
    PagePtr,
    PagePtr,
    Tracked<Map<PagePtr, LockPerm>>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, caller_cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k >= 8,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_2m >= 2,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ret.0.wf(),
        ret.0.len() == 8,
        ret.0.view().no_duplicates(),
        ret.3.view().dom() == ret.0.view().to_set(),
        allocated_4k_page_lock_perms_wf(
            ret.3.view(),
            final(krnl),
            final(lctx),
            current_thread_ptr,
            parent_container_ptr,
        ),
        ret.0.view().to_set().subset_of(
            final(krnl).ctn_mp.spec_index(parent_container_ptr)
                .view().owned_pages.view(),
        ),
        ret.1 != ret.2,
        page_ptr_valid(ret.1),
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
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1))
            .view().write_lock_perm_match(&ret.4.view()),
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2))
                .view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2))
            .view().write_lock_perm_match(&ret.5.view()),
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
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_2m
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_2m,
        thread_effective_quota_4k(
            final(krnl).thr_mp.spec_index(current_thread_ptr),
        ) == thread_effective_quota_4k(
            old(krnl).thr_mp.spec_index(current_thread_ptr),
        ) - 8,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .wlocked_by(final(lctx)),
        current_thread_lock_perm.lock_id()
            == final(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        final(lctx).page_lock_map().dom()
            == page_ptrs_to_indices(ret.0.view())
                .insert(page_ptr2page_index(ret.1))
                .insert(page_ptr2page_index(ret.2)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map()
            == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map()
            == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map()
            == old(lctx).pcid_allocator_lock_map(),
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
        held_threads_unchanged_except(
            old(krnl).thr_mp,
            final(krnl).thr_mp,
            old(lctx),
            set![current_thread_ptr],
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
{
    let ghost initial_thread = krnl.thr_mp
        .spec_index(current_thread_ptr).view();
    proof {
        broadcast use group_held_objects_unchanged_transitive;
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr)
                .view().temp_alloc_cache_2m.view().len() == 0
        ) by {
            reveal(Thread::temp_alloc_clean);
        };
        assert(
            thread_effective_quota_2m(
                krnl.thr_mp.spec_index(current_thread_ptr),
            ) >= 2
        ) by {
            reveal(thread_effective_quota_2m);
        };
    }
    let (pages_4k, Tracked(page_4k_lock_perms)) = allocate_free_4k_pages::<8>(
            krnl,
            current_thread_ptr,
            parent_container_ptr,
            caller_cpu_id,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(current_thread_lock_perm),
        );
    let ghost staged_4k_cache = krnl.thr_mp
        .spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view();
    let ghost effective_2m_before_container = thread_effective_quota_2m(
        krnl.thr_mp.spec_index(current_thread_ptr),
    );
    proof {
        assert(staged_4k_cache == pages_4k.view().to_set()) by {
            reveal(Thread::temp_alloc_clean);
            vstd::set::axiom_set_ext_equal(
                staged_4k_cache,
                pages_4k.view().to_set(),
            );
        };
        assert(
            lctx.holds_no_allocator_locks(PageSize::SZ2m)
                && lctx.holds_no_allocator_locks(PageSize::SZ1g)
        ) by {
            reveal(LocalContext::holds_no_allocator_locks);
        };
        assert(effective_2m_before_container >= 2) by {
            reveal(thread_effective_quota_2m);
            reveal(Thread::temp_alloc_clean);
        };
    }
    let (container_page, Tracked(container_page_lock_perm)) = allocate_free_2m_page(
            krnl,
            current_thread_ptr,
            parent_container_ptr,
            caller_cpu_id,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(current_thread_lock_perm),
        );
    let ghost effective_2m_before_pcid_allocator = thread_effective_quota_2m(
            krnl.thr_mp.spec_index(current_thread_ptr),
        );
    proof {
        assert(effective_2m_before_container >= 2) by {
            reveal(thread_effective_quota_2m);
            reveal(Thread::temp_alloc_clean);
        };
        assert(
            effective_2m_before_pcid_allocator >= 1
        ) by {
            assert(effective_2m_before_container >= 2) by {
                reveal(thread_effective_quota_2m);
                reveal(Thread::temp_alloc_clean);
            };
            assert(
                effective_2m_before_pcid_allocator
                    == effective_2m_before_container - 1
            ) by {
                reveal(thread_effective_quota_2m);
            };
            assert(
                effective_2m_before_container >= 2
                    && effective_2m_before_pcid_allocator
                        == effective_2m_before_container - 1
                    ==> effective_2m_before_pcid_allocator >= 1
            ) by (nonlinear_arith);
        };
    }
    let (pcid_allocator_page, Tracked(pcid_allocator_page_lock_perm)) = allocate_free_2m_page(
            krnl,
            current_thread_ptr,
            parent_container_ptr,
            caller_cpu_id,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(current_thread_lock_perm),
        );
    proof {
        assert(page_index_2m_valid(page_ptr2page_index(container_page)))
            by {
                reveal(hugepage_2m_wf);
            };
        assert(page_index_2m_valid(
            page_ptr2page_index(pcid_allocator_page),
        )) by {
            reveal(hugepage_2m_wf);
        };
        page_ptr_roundtrip();
        assert(page_ptr_2m_valid(container_page)) by {
            reveal(page_ptr_2m_valid);
            reveal(page_index_2m_valid);
            reveal(spec_page_index2page_ptr);
            assert(
                container_page % 0x200000usize == 0
            ) by (nonlinear_arith)
                requires
                    container_page
                        == page_ptr2page_index(container_page) * 4096usize,
                    page_ptr2page_index(container_page) % 512usize == 0;
        };
        assert(page_ptr_2m_valid(pcid_allocator_page)) by {
            reveal(page_ptr_2m_valid);
            reveal(page_index_2m_valid);
            reveal(spec_page_index2page_ptr);
            assert(
                pcid_allocator_page % 0x200000usize == 0
            ) by (nonlinear_arith)
                requires
                    pcid_allocator_page
                        == page_ptr2page_index(pcid_allocator_page)
                            * 4096usize,
                    page_ptr2page_index(pcid_allocator_page)
                        % 512usize == 0;
        };
        assert(container_page != pcid_allocator_page) by {
            reveal(Set::contains);
        };
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr)
                .view().temp_alloc_cache_2m.view()
                == set![container_page, pcid_allocator_page]
        ) by {
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
            assert_sets_equal!(
                krnl.thr_mp.spec_index(current_thread_ptr)
                    .view().temp_alloc_cache_2m.view()
                    == set![container_page, pcid_allocator_page]
            );
        };
        assert(
            lctx.page_lock_map().dom()
                == page_ptrs_to_indices(pages_4k.view())
                    .insert(page_ptr2page_index(container_page))
                    .insert(page_ptr2page_index(pcid_allocator_page))
        ) by {
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(
            lctx.holds_no_allocator_locks(PageSize::SZ4k)
                && lctx.holds_no_allocator_locks(PageSize::SZ2m)
                && lctx.holds_no_allocator_locks(PageSize::SZ1g)
        ) by {
            reveal(LocalContext::holds_no_allocator_locks);
        };
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr).view().state
                == old(krnl).thr_mp.spec_index(current_thread_ptr)
                    .view().state
        ) by {
            reveal(Thread::stable_allocation_root_equal);
        };
        assert(pages_4k.view().to_set().subset_of(
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_pages.view(),
        )) by {
            pages_4k.view().to_set_ensures();
            page_ptr_roundtrip();
            reveal(Set::subset_of);
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(container_page_owner_wf);
        };
    }
    (
        pages_4k,
        container_page,
        pcid_allocator_page,
        Tracked(page_4k_lock_perms),
        Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm),
    )
}

#[verifier::rlimit(120)]
#[verifier::spinoff_prover]
pub(super) fn transfer_staged_thread_page_to_child(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        page_ptr_valid(page_ptr),
        parent_container_ptr != child_container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(page_ptr),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(old(lctx)),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent_container_ptr,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        *final(lctx) == *old(lctx),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(final(lctx)),
        !final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().remove(page_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view().insert(page_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_processes,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler,
        final(krnl).ctn_mp.spec_index(parent_container_ptr).wlocked_by(final(lctx)),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.spec_index(child_container_ptr).wlocked_by(final(lctx)),
        !final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        child_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp == old(krnl).thr_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        final(krnl).irt == old(krnl).irt,
        final(krnl).rt_ctn == old(krnl).rt_ctn,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
{
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(page_index).view().is_init()) by { reveal(page_array_wf); };
        assert(krnl.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).is_init() && krnl.ctn_mp.spec_index(child_container_ptr).is_init()) by { reveal(container_perms_wf); };
        assert(old(krnl).pg_arr.spec_index(page_index).view().view().inv()) by { reveal(page_array_wf); };
        assert(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().inv() && old(krnl).ctn_mp.spec_index(child_container_ptr).view().inv()) by {
            reveal(container_perms_wf);
            reveal(containers_inv);
        };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm));
        page.owning_container = child_container_ptr;
        proof {
            assert(page.inv()) by {
                assert(old(krnl).pg_arr.spec_index(page_index).view().view().inv()) by { reveal(page_array_wf); };
                reveal(Page::mappings_va_valid);
                reveal(Page::mappings_finite);
                reveal(Page::ref_count_inv);
                reveal(Page::mapped_state_inv);
                reveal(Page::node_storage_inv);
                reveal(Page::free_state_inv);
                reveal(Page::perm_inv);
            };
        }
    }
    {
        let parent = krnl.ctn_mp.borrow_mut_typed(parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(parent_container_lock_perm));
        parent.owned_pages = Ghost(parent.owned_pages.view().remove(page_ptr));
        proof {
            assert(parent.inv()) by {
                assert(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().inv()) by {
                    reveal(container_perms_wf);
                    reveal(containers_inv);
                };
                reveal(Container::wf);
            };
        }
    }
    {
        proof {
            assert(krnl.ctn_mp.spec_index(child_container_ptr).is_init()) by { reveal(container_perms_wf); };
        }
        let child = krnl.ctn_mp.borrow_mut_typed(child_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(child_container_lock_perm));
        child.owned_pages = Ghost(child.owned_pages.view().insert(page_ptr));
        proof {
            assert(child.inv()) by {
                assert(old(krnl).ctn_mp.spec_index(child_container_ptr).view().inv()) by {
                    reveal(container_perms_wf);
                    reveal(containers_inv);
                };
                reveal(Container::wf);
            };
        }
    }
    proof {
        assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
        assert(krnl.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };

        assert(container_tree_fields_wf(krnl.ctn_mp)) by {
            reveal(container_tree_fields_wf);
            reveal(container_perms_wf);
        };
        assert(container_perms_wf(krnl.ctn_mp)) by { reveal(container_perms_wf); };
        assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
        assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
            reveal(allocator_4k_pages_wf);
            reveal(allocator_2m_pages_wf);
            reveal(allocator_1g_pages_wf);
        };
        assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(hugepage_2m_wf); };
        assert(hugepage_1g_wf(krnl.pg_arr)) by { reveal(hugepage_1g_wf); };
        assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by {
            reveal(mapped_4k_page_pagetable_wf);
            reveal(mapped_2m_page_pagetable_wf);
            reveal(mapped_1g_page_pagetable_wf);
            reveal(pagetable_perms_wf);
        };
        assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by {
            reveal(container_process_page_pagetable_wf);
            reveal(container_process_wf);
            reveal(container_page_owner_wf);
            reveal(mapped_4k_page_pagetable_wf);
            reveal(mapped_2m_page_pagetable_wf);
            reveal(mapped_1g_page_pagetable_wf);
            reveal(process_pagetable_match);
        };
        assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { reveal(container_pages_wf); };
        assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { reveal(process_pages_wf); };
        assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_pages_wf); };
        assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
        assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
        assert(thread_staged_pages_1g_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
        assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { reveal(endpoint_pages_wf); };

        assert(container_process_allocator_quota_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
        };
        assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
        assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by {
            reveal(container_allocator_free_2m_page_wf);
            reveal(container_allocator_global_free_2m_page_wf);
            reveal(container_allocator_cpu_cache_free_2m_page_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by {
            reveal(container_allocator_free_1g_page_wf);
            reveal(container_allocator_global_free_1g_page_wf);
            reveal(container_allocator_cpu_cache_free_1g_page_wf);
            reveal(allocator_free_page_ptrs_wf);
        };

        assert(container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)) by {
            reveal(container_tree_wf);
            reveal(container_root_wf);
            reveal(container_children_parent_wf);
            reveal(containers_linkedlist_wf);
            reveal(container_children_depth_wf);
            reveal(container_subtree_set_wf);
            reveal(container_uppertree_seq_wf);
            reveal(container_subtree_set_exclusive);
        };
        assert(krnl.ctn_mp.spec_index(krnl.rt_ctn).view().root_process_in_processes()) by { reveal(container_root_wf); };
        assert(container_process_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(container_process_wf); };
        assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(per_container_process_tree_wf); };
        assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
        assert(container_cpu_wf(krnl.ctn_mp, krnl.cpu_arr)) by { reveal(container_cpu_wf); };

        assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by {
            reveal(container_endpoint_wf);
            reveal(thread_endpoint_ref_counter_wf);
            reveal(thread_endpoint_queue_wf);
            reveal(container_thread_endpoint_wf);
        };
        assert(container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_pcid_allocator_wf(krnl.ctn_mp, krnl.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_pcid_allocator_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp)) by {
            reveal(container_process_wf);
            reveal(process_pcid_allocator_wf);
        };
        assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by {
            reveal(container_thread_wf);
            reveal(container_scheduler_wf);
            reveal(container_thread_scheduler_wf);
        };
        assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(container_thread_wf); };

        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)) by {
            reveal(cpu_dirty_map_contains_container_processes);
            reveal(cpu_dirty_map_proc_pcid_match);
            reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
            reveal(container_cpu_wf);
        };

        assert(iommu_root_table_process_wf(&krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
        assert(process_pci_function_ownership_wf(&krnl.irt, krnl.prc_mp)) by { reveal(process_pci_function_ownership_wf); };

    }
}

#[verifier::rlimit(80)]
#[verifier::spinoff_prover]
fn finish_staged_container_publish(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    pages_4k: &ArrayVec<PagePtr, 8>,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    Tracked(container_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(container_page_lock_perm): Tracked<LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_4k_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_1g_page_lock_perm): Tracked<LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<LockPerm>,
    Tracked(process_page_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<LockPerm>,
    Tracked(thread_page_lock_perm): Tracked<LockPerm>,
    Tracked(child_container_lock_perm): Tracked<LockPerm>,
    Tracked(child_process_lock_perm): Tracked<LockPerm>,
    Tracked(child_pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(child_scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(child_pcid_allocator_lock_perm): Tracked<LockPerm>,
) -> (ret: (
    Tracked<LockPerm>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        pages_4k.wf(),
        pages_4k.len() == 8,
        pages_4k.view().no_duplicates(),
        page_ptr_valid(pages_4k.view().spec_index(0)),
        page_ptr_valid(pages_4k.view().spec_index(1)),
        page_ptr_valid(pages_4k.view().spec_index(2)),
        page_ptr_valid(pages_4k.view().spec_index(3)),
        page_ptr_valid(pages_4k.view().spec_index(4)),
        page_ptr_valid(pages_4k.view().spec_index(5)),
        page_ptr_valid(pages_4k.view().spec_index(6)),
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(container_page)),
        ),
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(
            set![
                page_ptr2page_index(container_page),
                page_ptr2page_index(pcid_allocator_page),
                page_ptr2page_index(pages_4k.view().spec_index(0)),
                page_ptr2page_index(pages_4k.view().spec_index(1)),
                page_ptr2page_index(pages_4k.view().spec_index(2)),
                page_ptr2page_index(pages_4k.view().spec_index(3)),
                page_ptr2page_index(pages_4k.view().spec_index(4)),
                page_ptr2page_index(pages_4k.view().spec_index(5)),
                page_ptr2page_index(pages_4k.view().spec_index(6)),
                page_ptr2page_index(pages_4k.view().spec_index(7)),
            ],
        ),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))
            .disjoint(
                set![
                    page_ptr2page_index(container_page),
                    page_ptr2page_index(pcid_allocator_page),
                    page_ptr2page_index(pages_4k.view().spec_index(0)),
                    page_ptr2page_index(pages_4k.view().spec_index(1)),
                    page_ptr2page_index(pages_4k.view().spec_index(2)),
                    page_ptr2page_index(pages_4k.view().spec_index(3)),
                    page_ptr2page_index(pages_4k.view().spec_index(4)),
                    page_ptr2page_index(pages_4k.view().spec_index(5)),
                    page_ptr2page_index(pages_4k.view().spec_index(6)),
                    page_ptr2page_index(pages_4k.view().spec_index(7)),
                ],
            ),
        owned_2m_tail_lock_perms_wf(
            container_tail_lock_perms,
            old(krnl),
            old(lctx),
            page_ptr2page_index(container_page),
        ),
        owned_2m_tail_lock_perms_wf(
            pcid_allocator_tail_lock_perms,
            old(krnl),
            old(lctx),
            page_ptr2page_index(pcid_allocator_page),
        ),
        old(krnl).ctn_mp.dom().contains(container_page),
        old(krnl).ctn_mp.spec_index(container_page).wlocked_by(old(lctx)),
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id()
            == old(krnl).ctn_mp.spec_index(container_page)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        old(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4))
            .wlocked_by(old(lctx)),
        child_process_lock_perm.state() is WriteLock,
        child_process_lock_perm.thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.lock_id()
            == old(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4))
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        old(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5))
            .wlocked_by(old(lctx)),
        child_pagetable_lock_perm.state() is WriteLock,
        child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id()
            == old(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5))
                .locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        old(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3))
            .wlocked_by(old(lctx)),
        child_scheduler_lock_perm.state() is WriteLock,
        child_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        child_scheduler_lock_perm.lock_id()
            == old(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3))
                .locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_page)
            .wlocked_by(old(lctx)),
        child_pcid_allocator_lock_perm.state() is WriteLock,
        child_pcid_allocator_lock_perm.thread_id()
            == old(lctx).thread_id(),
        child_pcid_allocator_lock_perm.lock_id()
            == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_page)
                .locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page))
            .view().wlocked_by(old(lctx)),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                container_page,
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pcid_allocator_page,
        )).view().wlocked_by(old(lctx)),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id()
            == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pcid_allocator_page,
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(0),
        )).view().wlocked_by(old(lctx)),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(0),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(1),
        )).view().wlocked_by(old(lctx)),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(1),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(2),
        )).view().wlocked_by(old(lctx)),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(2),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(3),
        )).view().wlocked_by(old(lctx)),
        scheduler_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(3),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(4),
        )).view().wlocked_by(old(lctx)),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(4),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(5),
        )).view().wlocked_by(old(lctx)),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(5),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(6),
        )).view().wlocked_by(old(lctx)),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(6),
            )).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(7),
        )).view().wlocked_by(old(lctx)),
        thread_page_lock_perm.state() is WriteLock,
        thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(7),
            )).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().difference(page_2m_tail_indices(page_ptr2page_index(container_page))).difference(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))).remove(page_ptr2page_index(pages_4k.view().spec_index(0))).remove(page_ptr2page_index(pages_4k.view().spec_index(1))).remove(page_ptr2page_index(pages_4k.view().spec_index(2))).remove(page_ptr2page_index(pages_4k.view().spec_index(3))).remove(page_ptr2page_index(pages_4k.view().spec_index(4))).remove(page_ptr2page_index(pages_4k.view().spec_index(5))).remove(page_ptr2page_index(pages_4k.view().spec_index(6))).remove(page_ptr2page_index(container_page)).remove(page_ptr2page_index(pcid_allocator_page)),
        final(lctx).cpu_lock_map().dom() == old(lctx).cpu_lock_map().dom(),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom(),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom(),
        final(lctx).thread_lock_map().dom() == old(lctx).thread_lock_map().dom(),
        final(lctx).endpoint_lock_map().dom() == old(lctx).endpoint_lock_map().dom(),
        final(lctx).scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().remove(pcid_allocator_page),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom(),
        final(lctx).iommu_table_lock_map().dom() == old(lctx).iommu_table_lock_map().dom(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).ctn_mp == old(krnl).ctn_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).thr_mp == old(krnl).thr_mp,
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).ctn_mp.spec_index(container_page)
            .wlocked_by(final(lctx)),
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4))
            .wlocked_by(final(lctx)),
        final(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5))
            .wlocked_by(final(lctx)),
        final(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3))
            .wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(7),
        )).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(7),
        )) == old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(7),
        )),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id()
            == final(krnl).ctn_mp.spec_index(container_page)
                .locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id()
            == final(krnl).prc_mp.spec_index(
                pages_4k.view().spec_index(4),
            ).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id()
            == final(krnl).pt_mp.spec_index(
                pages_4k.view().spec_index(5),
            ).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id()
            == final(krnl).sched_mp.spec_index(
                pages_4k.view().spec_index(3),
            ).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(7),
            )).view().locking_thread()->Write_lock_id,
{
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let scheduler_page = *pages_4k.get(3);
    let process_page = *pages_4k.get(4);
    let pagetable_page = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page = *pages_4k.get(7);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    proof {
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        assert({
            &&& page_ptr_valid(container_page)
            &&& page_ptr_valid(pcid_allocator_page)
        }) by {
            reveal(page_ptr_2m_valid);
            reveal(page_ptr_valid);
            assert(container_page % 4096usize == 0) by (nonlinear_arith)
                requires container_page % 0x200000usize == 0;
            assert(pcid_allocator_page % 4096usize == 0)
                by (nonlinear_arith)
                requires pcid_allocator_page % 0x200000usize == 0;
        };
        assert({
            &&& index_valid(NUM_PAGES, page_ptr2page_index(allocator_4k_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(allocator_2m_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(allocator_1g_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(scheduler_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(process_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(pagetable_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(l4_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(thread_page))
        }) by {
            page_ptr_valid_imply_page_index_valid();
        };
        assert({
            &&& container_head
                != page_ptr2page_index(allocator_4k_page)
            &&& container_head
                != page_ptr2page_index(allocator_2m_page)
            &&& container_head
                != page_ptr2page_index(allocator_1g_page)
            &&& container_head != page_ptr2page_index(scheduler_page)
            &&& container_head != page_ptr2page_index(process_page)
            &&& container_head != page_ptr2page_index(pagetable_page)
            &&& container_head != page_ptr2page_index(l4_page)
            &&& container_head != page_ptr2page_index(thread_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(allocator_4k_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(allocator_2m_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(allocator_1g_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(scheduler_page)
            &&& pcid_allocator_head != page_ptr2page_index(process_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(pagetable_page)
            &&& pcid_allocator_head != page_ptr2page_index(l4_page)
            &&& pcid_allocator_head != page_ptr2page_index(thread_page)
        }) by {
            pages_4k.view().to_set_ensures();
            page_ptr_roundtrip();
            page_ptr2page_index_injective();
            page_2m_all_ptrs_contains_head(container_head);
            page_2m_all_ptrs_contains_head(pcid_allocator_head);
        };
    }
    wunlock_owned_2m_page_tails(
        krnl,
        container_head,
        Tracked(&mut *lctx),
        Tracked(container_tail_lock_perms),
    );
    proof {
        assert(owned_2m_tail_lock_perms_wf(
            pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
        )) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices);
        };
    }
    wunlock_owned_2m_page_tails(
        krnl,
        pcid_allocator_head,
        Tracked(&mut *lctx),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        assert({
            &&& krnl.pg_arr.spec_index(container_head)
                .view().wlocked_by(lctx)
            &&& container_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(container_head)
                    .view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(pcid_allocator_head)
                .view().wlocked_by(lctx)
            &&& pcid_allocator_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(pcid_allocator_head)
                    .view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                allocator_4k_page,
            )).view().wlocked_by(lctx)
            &&& allocator_4k_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    allocator_4k_page,
                )).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                allocator_2m_page,
            )).view().wlocked_by(lctx)
            &&& allocator_2m_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    allocator_2m_page,
                )).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                allocator_1g_page,
            )).view().wlocked_by(lctx)
            &&& allocator_1g_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    allocator_1g_page,
                )).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                scheduler_page,
            )).view().wlocked_by(lctx)
            &&& scheduler_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    scheduler_page,
                )).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                process_page,
            )).view().wlocked_by(lctx)
            &&& process_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    process_page,
                )).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                pagetable_page,
            )).view().wlocked_by(lctx)
            &&& pagetable_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    pagetable_page,
                )).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(l4_page))
                .view().wlocked_by(lctx)
            &&& l4_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(l4_page))
                    .view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(thread_page))
                .view().wlocked_by(lctx)
            &&& thread_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(thread_page))
                    .view().locking_thread()->Write_lock_id
        }) by {
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(page_2m_tail_indices);
            reveal(Set::disjoint);
        };
    }
    krnl.wunlock_page(
        page_ptr2page_index(allocator_4k_page),
        Tracked(&mut *lctx),
        Tracked(allocator_4k_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(allocator_2m_page),
        Tracked(&mut *lctx),
        Tracked(allocator_2m_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(allocator_1g_page),
        Tracked(&mut *lctx),
        Tracked(allocator_1g_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(scheduler_page),
        Tracked(&mut *lctx),
        Tracked(scheduler_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(process_page),
        Tracked(&mut *lctx),
        Tracked(process_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(pagetable_page),
        Tracked(&mut *lctx),
        Tracked(pagetable_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(l4_page),
        Tracked(&mut *lctx),
        Tracked(l4_page_lock_perm),
    );
    proof {
        assert(
            krnl.pg_arr.spec_index(container_head)
                .view().wlocked_by(lctx)
                && container_page_lock_perm.lock_id()
                    == krnl.pg_arr.spec_index(container_head)
                        .view().locking_thread()->Write_lock_id
        ) by {
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(typed_lock_maps_removed);
        };
    }
    krnl.wunlock_page(
        container_head,
        Tracked(&mut *lctx),
        Tracked(container_page_lock_perm),
    );
    proof {
        assert(
            krnl.pg_arr.spec_index(pcid_allocator_head)
                .view().wlocked_by(lctx)
                && pcid_allocator_page_lock_perm.lock_id()
                    == krnl.pg_arr.spec_index(pcid_allocator_head)
                        .view().locking_thread()->Write_lock_id
        ) by {
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(typed_lock_maps_removed);
        };
    }
    krnl.wunlock_page(
        pcid_allocator_head,
        Tracked(&mut *lctx),
        Tracked(pcid_allocator_page_lock_perm),
    );
    krnl.wunlock_pcid_allocator(
        pcid_allocator_page,
        Tracked(&mut *lctx),
        Tracked(child_pcid_allocator_lock_perm),
    );
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_page)
            &&& krnl.ctn_mp.spec_index(container_page).wlocked_by(lctx)
            &&& child_container_lock_perm.lock_id()
                == krnl.ctn_mp.spec_index(container_page)
                    .locking_thread()->Write_lock_id
            &&& krnl.prc_mp.dom().contains(process_page)
            &&& krnl.prc_mp.spec_index(process_page).wlocked_by(lctx)
            &&& child_process_lock_perm.lock_id()
                == krnl.prc_mp.spec_index(process_page)
                    .locking_thread()->Write_lock_id
            &&& krnl.pt_mp.dom().contains(pagetable_page)
            &&& krnl.pt_mp.spec_index(pagetable_page).wlocked_by(lctx)
            &&& child_pagetable_lock_perm.lock_id()
                == krnl.pt_mp.spec_index(pagetable_page)
                    .locking_thread()->Write_lock_id
            &&& krnl.sched_mp.dom().contains(scheduler_page)
            &&& krnl.sched_mp.spec_index(scheduler_page).wlocked_by(lctx)
            &&& child_scheduler_lock_perm.lock_id()
                == krnl.sched_mp.spec_index(scheduler_page)
                    .locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(thread_page))
                .view().wlocked_by(lctx)
            &&& thread_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(thread_page))
                    .view().locking_thread()->Write_lock_id
        }) by {
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(LockedMap::typed_lock_map_aligned);
        };
    }

    (
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    )
}

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
pub(super) fn publish_new_container_base(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, caller_cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot, pages_4k: &ArrayVec<PagePtr, 8>, container_page: PagePtr, pcid_allocator_page: PagePtr, funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, allocator_quota_4k: usize, process_quota_4k: usize, Tracked(page_4k_lock_perms): Tracked<Map<PagePtr, LockPerm>>, Tracked(funding_page_lock_perms): Tracked<Map<PagePtr, LockPerm>>, Tracked(container_page_lock_perm): Tracked<LockPerm>, Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>,))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, caller_cpu_id),
        pages_4k.wf(),
        pages_4k.len() == 8,
        pages_4k.view().no_duplicates(),
        page_4k_lock_perms.dom() == pages_4k.view().to_set(),
        allocated_4k_page_lock_perms_wf(page_4k_lock_perms, old(krnl), old(lctx), current_thread_ptr, parent_container_ptr),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        allocated_4k_page_lock_perms_wf(funding_page_lock_perms, old(krnl), old(lctx), current_thread_ptr, parent_container_ptr),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1), pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6))),
        new_container_moved_pages(container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1), pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6)).union(funding_pages.to_set()).subset_of(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view()),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(pages_4k.view().spec_index(0)),
        !old(krnl).allc_2m_mp.dom().contains(pages_4k.view().spec_index(1)),
        !old(krnl).allc_1g_mp.dom().contains(pages_4k.view().spec_index(2)),
        !old(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        !old(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        !old(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().owning_container == parent_container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == parent_container_ptr,
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().write_lock_perm_match(&container_page_lock_perm),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().write_lock_perm_match(&pcid_allocator_page_lock_perm),
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < usize::MAX,
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        old(krnl).prc_mp.spec_index(parent_process_ptr).wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 7,
        funding_page_count
            <= old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 7,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() =~= pages_4k.view().to_set().union(funding_pages.to_set()),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view() =~= set![container_page, pcid_allocator_page],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(old(lctx)),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().wlocked_by(old(lctx)),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().owning_container == parent_container_ptr,
        old(lctx).object_lock_scope(old(lctx).page_lock_map().dom(), set![caller_cpu_id], set![parent_container_ptr], set![parent_process_ptr], set![current_thread_ptr], Set::empty(), Set::empty(), Set::empty(), set![source_pagetable_ptr], Set::empty()),
        old(lctx).page_lock_map().dom() == page_ptrs_to_indices(pages_4k.view()).union(page_ptrs_to_indices(funding_pages)).insert(page_ptr2page_index(container_page)).insert(page_ptr2page_index(pcid_allocator_page)),
        old(lctx).page_lock_map().dom().disjoint(page_2m_tail_indices(page_ptr2page_index(container_page)).union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)))),
        old(lctx).lock_id_acyclic(merged_page_lock_id((page_ptr2page_index(container_page) + 1) as usize)),
        old(lctx).lock_id_acyclic(merged_page_lock_id((page_ptr2page_index(pcid_allocator_page) + 1) as usize)),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).object_lock_scope(set![page_ptr2page_index(pages_4k.view().spec_index(7))], set![caller_cpu_id], set![parent_container_ptr, container_page], set![parent_process_ptr, pages_4k.view().spec_index(4)], set![current_thread_ptr], Set::empty(), set![pages_4k.view().spec_index(3)], Set::empty(), set![ source_pagetable_ptr, pages_4k.view().spec_index(5), ], Set::empty()),
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).prc_mp.dom().contains(parent_process_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view().wlocked_by(final(lctx)),
        !final(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).wlocked_by(final(lctx)),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes.view().contains(parent_process_ptr),
        final(krnl).prc_mp.spec_index(parent_process_ptr).wlocked_by(final(lctx)),
        !final(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(final(lctx)),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(final(lctx)),
        final(krnl).ctn_mp.dom().contains(container_page),
        final(krnl).ctn_mp.spec_index(container_page).wlocked_by(final(lctx)),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().scheduler == pages_4k.view().spec_index(3),
        final(krnl).ctn_mp.spec_index(container_page).view().owned_processes.view().contains(pages_4k.view().spec_index(4)),
        !final(krnl).ctn_mp.spec_index(container_page).being_killed(),
        final(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).wlocked_by(final(lctx)),
        !final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).being_killed(),
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).view_rodata().view().owning_container == container_page,
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).view_rodata().view().pagetable == pages_4k.view().spec_index(5),
        final(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        final(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5)).wlocked_by(final(lctx)),
        final(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        final(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3)).wlocked_by(final(lctx)),
        !final(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3)).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![pages_4k.view().spec_index(7)],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 7 - funding_page_count,
        page_ptr_valid(pages_4k.view().spec_index(7)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().view().owning_container == parent_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().wlocked_by(final(lctx)),
        !final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(pages_4k.view().spec_index(7)),
        !final(krnl).ctn_mp.spec_index(container_page).view().owned_pages.view().contains(pages_4k.view().spec_index(7)),
        source_pagetable_ptr != pages_4k.view().spec_index(5),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread(),
        final(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread(),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5)).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3)).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().locking_thread()->Write_lock_id,
{
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let scheduler_page = *pages_4k.get(3);
    let process_page = *pages_4k.get(4);
    let pagetable_page = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page = *pages_4k.get(7);
    proof {
        assert({
            &&& page_4k_lock_perms.dom().contains(allocator_4k_page)
            &&& page_4k_lock_perms.dom().contains(allocator_2m_page)
            &&& page_4k_lock_perms.dom().contains(allocator_1g_page)
            &&& page_4k_lock_perms.dom().contains(scheduler_page)
            &&& page_4k_lock_perms.dom().contains(process_page)
            &&& page_4k_lock_perms.dom().contains(pagetable_page)
            &&& page_4k_lock_perms.dom().contains(l4_page)
            &&& page_4k_lock_perms.dom().contains(thread_page)
        }) by { pages_4k.view().to_set_ensures(); };
        assert({
            &&& page_ptr_valid(allocator_4k_page)
            &&& page_ptr_valid(allocator_2m_page)
            &&& page_ptr_valid(allocator_1g_page)
            &&& page_ptr_valid(scheduler_page)
            &&& page_ptr_valid(process_page)
            &&& page_ptr_valid(pagetable_page)
            &&& page_ptr_valid(l4_page)
            &&& page_ptr_valid(thread_page)
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(process_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
        }) by { reveal(allocated_4k_page_lock_perms_wf); };
    }
    let tracked mut page_4k_lock_perms = page_4k_lock_perms;
    let tracked allocator_4k_page_lock_perm = page_4k_lock_perms.tracked_remove(allocator_4k_page);
    let tracked allocator_2m_page_lock_perm = page_4k_lock_perms.tracked_remove(allocator_2m_page);
    let tracked allocator_1g_page_lock_perm = page_4k_lock_perms.tracked_remove(allocator_1g_page);
    let tracked scheduler_page_lock_perm = page_4k_lock_perms.tracked_remove(scheduler_page);
    let tracked process_page_lock_perm = page_4k_lock_perms.tracked_remove(process_page);
    let tracked pagetable_page_lock_perm = page_4k_lock_perms.tracked_remove(pagetable_page);
    let tracked l4_page_lock_perm = page_4k_lock_perms.tracked_remove(l4_page);
    let tracked thread_page_lock_perm = page_4k_lock_perms.tracked_remove(thread_page);
    proof {
        pages_4k.view().to_set_ensures();
        assert(pages_4k.view().to_set() == new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page).insert(thread_page)) by {
            assert_sets_equal!(
                pages_4k.view().to_set() == new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page).insert(thread_page),
                page_ptr => {
                    reveal(new_container_bootstrap_4k_pages);
                }
            );
        };
    }
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    proof {
        assert({
            &&& old(lctx).page_lock_map().dom().contains(container_head)
            &&& old(lctx).page_lock_map().dom().contains(pcid_allocator_head)
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(allocator_4k_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(allocator_2m_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(allocator_1g_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(scheduler_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(process_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(pagetable_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(l4_page))
            &&& old(lctx).page_lock_map().dom().contains(page_ptr2page_index(thread_page))
        }) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    let (Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms)) = if container_head < pcid_allocator_head {
        proof {
            let container_quotient = container_head / 512usize;
            let pcid_allocator_quotient = pcid_allocator_head / 512usize;
            assert(container_head == container_quotient * 512usize) by (nonlinear_arith)
                requires
                    container_head % 512usize == 0,
                    container_quotient == container_head / 512usize;
            assert(pcid_allocator_head == pcid_allocator_quotient * 512usize) by (nonlinear_arith)
                requires
                    pcid_allocator_head % 512usize == 0,
                    pcid_allocator_quotient == pcid_allocator_head / 512usize;
            assert(container_head + 512usize <= pcid_allocator_head)
                by (nonlinear_arith)
                requires
                    container_head == container_quotient * 512usize,
                    pcid_allocator_head == pcid_allocator_quotient * 512usize,
                    container_head < pcid_allocator_head;
        }
        let Tracked(container_tail_lock_perms) = wlock_owned_2m_page_tails(krnl, container_head, Tracked(&mut *lctx));
        proof {
            assert(lctx.lock_id_acyclic(merged_page_lock_id((pcid_allocator_head + 1) as usize))) by {
                reveal(LocalContext::lock_id_acyclic);
                reveal(owned_2m_tail_lock_perms_wf);
                reveal(page_2m_tail_indices);
                reveal(merged_page_lock_id);
            };
        }
        let Tracked(pcid_allocator_tail_lock_perms) = wlock_owned_2m_page_tails(krnl, pcid_allocator_head, Tracked(&mut *lctx));
        (Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),)
    } else {
        proof {
            let container_quotient = container_head / 512usize;
            let pcid_allocator_quotient = pcid_allocator_head / 512usize;
            assert(container_head == container_quotient * 512usize) by (nonlinear_arith)
                requires
                    container_head % 512usize == 0,
                    container_quotient == container_head / 512usize;
            assert(pcid_allocator_head == pcid_allocator_quotient * 512usize) by (nonlinear_arith)
                requires
                    pcid_allocator_head % 512usize == 0,
                    pcid_allocator_quotient == pcid_allocator_head / 512usize;
            assert(pcid_allocator_head + 512usize <= container_head)
                by (nonlinear_arith)
                requires
                    container_head == container_quotient * 512usize,
                    pcid_allocator_head == pcid_allocator_quotient * 512usize,
                    pcid_allocator_head < container_head;
        }
        let Tracked(pcid_allocator_tail_lock_perms) = wlock_owned_2m_page_tails(krnl, pcid_allocator_head, Tracked(&mut *lctx));
        proof {
            assert(lctx.lock_id_acyclic(merged_page_lock_id((container_head + 1) as usize))) by {
                reveal(LocalContext::lock_id_acyclic);
                reveal(owned_2m_tail_lock_perms_wf);
                reveal(page_2m_tail_indices);
                reveal(merged_page_lock_id);
            };
        }
        let Tracked(container_tail_lock_perms) = wlock_owned_2m_page_tails(krnl, container_head, Tracked(&mut *lctx));
        (Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),)
    };
    proof {
        assert({
            &&& krnl.pg_arr.spec_index(container_head) == old(krnl).pg_arr.spec_index(container_head)
            &&& krnl.pg_arr.spec_index(pcid_allocator_head) == old(krnl).pg_arr.spec_index(pcid_allocator_head)
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(process_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
        }) by { reveal(page_2m_tail_indices); };
        assert forall|i: int|
            #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(funding_pages.spec_index(i)))]
            0 <= i < funding_pages.len() implies {
                &&& page_ptr_valid(funding_pages.spec_index(i))
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(funding_pages.spec_index(i))) == old(krnl).pg_arr.spec_index(page_ptr2page_index(funding_pages.spec_index(i)))
            } by {
            let page_ptr = funding_pages.spec_index(i);
            assert(funding_pages.to_set().contains(page_ptr)) by {
                funding_pages.to_set_ensures();
                reveal(Seq::contains);
            };
            assert(page_ptr_valid(page_ptr)) by { reveal(staged_4k_page_chain); };
            page_ptr_valid_imply_page_index_valid();
            page_ptr_roundtrip();
            let page_index = page_ptr2page_index(page_ptr);
            assert(!page_2m_tail_indices(container_head).contains(page_index)) by {
                if page_2m_tail_indices(container_head).contains(page_index)
                {
                    assert(container_head <= page_index < container_head + 512) by { reveal(page_2m_tail_indices); };
                    page_2m_all_ptrs_contains_index(container_head, page_index);
                    assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page).contains(page_ptr)) by { reveal(new_container_moved_pages); };
                }
            };
            assert(!page_2m_tail_indices(pcid_allocator_head).contains(page_index)) by {
                if page_2m_tail_indices(pcid_allocator_head).contains(page_index)
                {
                    assert(pcid_allocator_head <= page_index < pcid_allocator_head + 512) by { reveal(page_2m_tail_indices); };
                    page_2m_all_ptrs_contains_index(pcid_allocator_head, page_index);
                    assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page).contains(page_ptr)) by { reveal(new_container_moved_pages); };
                }
            };
            reveal(page_2m_tail_indices);
        };
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by { reveal(staged_4k_page_chain); };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(krnl.pg_arr.spec_index(container_head).view().write_lock_perm_match(&container_page_lock_perm)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(krnl.pg_arr.spec_index(pcid_allocator_head).view().write_lock_perm_match(&pcid_allocator_page_lock_perm)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().write_lock_perm_match(&allocator_4k_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().write_lock_perm_match(&allocator_2m_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().write_lock_perm_match(&allocator_1g_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().write_lock_perm_match(&scheduler_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(process_page)).view().write_lock_perm_match(&process_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().write_lock_perm_match(&pagetable_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)).view().write_lock_perm_match(&l4_page_lock_perm)) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(owned_2m_tail_lock_perms_wf(container_tail_lock_perms, krnl, lctx, container_head)) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices);
        };
        assert(owned_2m_tail_lock_perms_wf(pcid_allocator_tail_lock_perms, krnl, lctx, pcid_allocator_head)) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices);
        };
    }
    let ghost lctx_before_container_publish = *lctx;
    let ghost parent_process_before_container_publish = krnl.prc_mp.spec_index(parent_process_ptr);
    proof {
        assert(krnl.prc_mp == old(krnl).prc_mp);
        assert(!parent_process_before_container_publish.being_killed());

    }
    let (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(child_pcid_allocator_lock_perm)) = publish_staged_container_root(krnl, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page, thread_page, funding_page_count, funding_page_head, Ghost(funding_pages), allocator_quota_4k, process_quota_4k, Tracked(&mut *lctx), Tracked(parent_container_lock_perm), Tracked(current_thread_lock_perm), Tracked(&container_page_lock_perm), Tracked(&pcid_allocator_page_lock_perm), Tracked(&allocator_4k_page_lock_perm), Tracked(&allocator_2m_page_lock_perm), Tracked(&allocator_1g_page_lock_perm), Tracked(&scheduler_page_lock_perm), Tracked(&process_page_lock_perm), Tracked(&pagetable_page_lock_perm), Tracked(&l4_page_lock_perm), Tracked(&funding_page_lock_perms), Tracked(&container_tail_lock_perms), Tracked(&pcid_allocator_tail_lock_perms));
    proof {
        assert(lctx_before_container_publish.process_lock_map().dom().contains(parent_process_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(!krnl.prc_mp.spec_index(parent_process_ptr).being_killed()) by {
            reveal(held_processes_unchanged);
            assert(krnl.prc_mp.spec_index(parent_process_ptr) == parent_process_before_container_publish);
        };

    }
    let ghost lctx_before_funding_cleanup = *lctx;
    proof {
        page_2m_all_ptrs_contains_head(container_head);
        page_2m_all_ptrs_contains_head(pcid_allocator_head);
        page_ptr_roundtrip();
        assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page).contains(container_page)) by { reveal(new_container_moved_pages); };
        assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, process_page, pagetable_page, l4_page).contains(pcid_allocator_page)) by { reveal(new_container_moved_pages); };
        assert(!funding_pages.to_set().contains(container_page)) by { reveal(Set::disjoint); };
        assert(!funding_pages.to_set().contains(pcid_allocator_page)) by { reveal(Set::disjoint); };
        assert(!page_ptrs_to_indices(funding_pages).contains(container_head)) by {
            reveal(page_ptrs_to_indices);
            let mapped = funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr));
            if mapped.to_set().contains(container_head) {
                mapped.to_set_ensures();
                reveal(Seq::contains);
                let i = choose|i: int|
                    0 <= i < mapped.len()
                        && mapped.spec_index(i) == container_head;
                assert(0 <= i < funding_pages.len()) by { reveal(Seq::map_values); };
                assert(funding_pages.to_set().contains(funding_pages.spec_index(i))) by {
                    funding_pages.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(page_ptr_valid(funding_pages.spec_index(i))) by { reveal(staged_4k_page_chain); };
                assert(funding_pages.spec_index(i) == container_page) by {
                    page_ptr2page_index_injective();
                    reveal(Seq::map_values);
                };
            }
        };
        assert(!page_ptrs_to_indices(funding_pages).contains(pcid_allocator_head)) by {
            reveal(page_ptrs_to_indices);
            let mapped = funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr));
            if mapped.to_set().contains(pcid_allocator_head) {
                mapped.to_set_ensures();
                reveal(Seq::contains);
                let i = choose|i: int|
                    0 <= i < mapped.len()
                        && mapped.spec_index(i) == pcid_allocator_head;
                assert(0 <= i < funding_pages.len()) by { reveal(Seq::map_values); };
                assert(funding_pages.to_set().contains(funding_pages.spec_index(i))) by {
                    funding_pages.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(page_ptr_valid(funding_pages.spec_index(i))) by { reveal(staged_4k_page_chain); };
                assert(funding_pages.spec_index(i) == pcid_allocator_page) by {
                    page_ptr2page_index_injective();
                    reveal(Seq::map_values);
                };
            }
        };
        assert(lctx_before_funding_cleanup.page_lock_map().dom().contains(container_head)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(lctx_before_funding_cleanup.page_lock_map().dom().contains(pcid_allocator_head)) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    cleanup_published_4k_page_chain(krnl, funding_page_count, funding_page_head, Ghost(funding_pages), allocator_4k_page, container_page, Tracked(&mut *lctx), Tracked(funding_page_lock_perms));
    proof {
        assert(lctx.page_lock_map().dom().contains(container_head)) by { reveal(Map::remove_keys); };
        assert(lctx.page_lock_map().dom().contains(pcid_allocator_head)) by { reveal(Map::remove_keys); };
        assert(krnl.pg_arr.spec_index(container_head).view().wlocked_by(lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(krnl.pg_arr.spec_index(pcid_allocator_head).view().wlocked_by(lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(owned_2m_tail_lock_perms_wf(container_tail_lock_perms, krnl, lctx, container_head)) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(owned_2m_tail_lock_perms_wf(pcid_allocator_tail_lock_perms, krnl, lctx, pcid_allocator_head)) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(LockedArray::typed_lock_map_aligned);
        };
    }
    let (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(thread_page_lock_perm)) = finish_staged_container_publish(krnl, Tracked(&mut *lctx), pages_4k, container_page, pcid_allocator_page, Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms), Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm), Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm), Tracked(allocator_1g_page_lock_perm), Tracked(scheduler_page_lock_perm), Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(thread_page_lock_perm), Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(child_pcid_allocator_lock_perm));
    proof {
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_processes.view().contains(parent_process_ptr)) by { reveal(container_process_wf); };
        assert({
            &&& old(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& old(lctx).holds_no_allocator_locks(PageSize::SZ2m)
            &&& old(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id]
            &&& old(lctx).container_lock_map().dom() =~= set![parent_container_ptr]
            &&& old(lctx).process_lock_map().dom() =~= set![parent_process_ptr]
            &&& old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr]
            &&& old(lctx).endpoint_lock_map().dom() =~= Set::empty()
            &&& old(lctx).scheduler_lock_map().dom() =~= Set::empty()
            &&& old(lctx).pcid_allocator_lock_map().dom() =~= Set::empty()
            &&& old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr]
            &&& old(lctx).iommu_table_lock_map().dom() =~= Set::empty()
        }) by { reveal(LocalContext::holds_no_allocator_locks); };
        assert(lctx.object_lock_scope(set![page_ptr2page_index(thread_page)], set![caller_cpu_id], set![parent_container_ptr, container_page], set![parent_process_ptr, process_page], set![current_thread_ptr], Set::empty(), set![scheduler_page], Set::empty(), set![source_pagetable_ptr, pagetable_page], Set::empty())) by {
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
        };
    }
    (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(thread_page_lock_perm),)
}

#[verifier::spinoff_prover]
pub(super) fn create_root_thread_and_finish_new_container(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId,
    parent_container_ptr: RwLockContainerPtr,
    parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    source_pagetable_ptr: RwLockPageTableRoot,
    child_container_ptr: RwLockContainerPtr,
    child_process_ptr: RwLockProcessPtr,
    child_pagetable_ptr: RwLockPageTableRoot,
    child_scheduler_ptr: RwLockSchedulerPtr,
    thread_page_ptr: PagePtr,
    caller_cpu_lock_perm: Tracked<LockPerm>,
    parent_container_lock_perm: Tracked<LockPerm>,
    parent_process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
    child_container_lock_perm: Tracked<LockPerm>,
    child_process_lock_perm: Tracked<LockPerm>,
    child_pagetable_lock_perm: Tracked<LockPerm>,
    child_scheduler_lock_perm: Tracked<LockPerm>,
    thread_page_lock_perm: Tracked<LockPerm>,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, caller_cpu_id),
        page_ptr_valid(thread_page_ptr),
        parent_container_ptr != child_container_ptr,
        parent_process_ptr != child_process_ptr,
        source_pagetable_ptr != child_pagetable_ptr,
        old(lctx).object_lock_scope(
            set![page_ptr2page_index(thread_page_ptr)],
            set![caller_cpu_id],
            set![parent_container_ptr, child_container_ptr],
            set![parent_process_ptr, child_process_ptr],
            set![current_thread_ptr],
            Set::empty(),
            set![child_scheduler_ptr],
            Set::empty(),
            set![source_pagetable_ptr, child_pagetable_ptr],
            Set::empty(),
        ),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().wlocked_by(old(lctx)),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().being_killed(),
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id()
            == old(krnl).cpu_arr.spec_index(caller_cpu_id)
                .view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        old(krnl).prc_mp.spec_index(parent_process_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr)
            .view_rodata().view().owning_container
            == parent_container_ptr,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(parent_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr)
            .wlocked_by(old(lctx)),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(source_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().parent == Some(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().scheduler == child_scheduler_ptr,
        child_container_lock_perm.view().state() is WriteLock,
        child_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(child_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().owning_container == child_container_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().pagetable == child_pagetable_ptr,
        child_process_lock_perm.view().state() is WriteLock,
        child_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr)
            .wlocked_by(old(lctx)),
        child_pagetable_lock_perm.view().state() is WriteLock,
        child_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(child_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        old(krnl).sched_mp.spec_index(child_scheduler_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).sched_mp.spec_index(child_scheduler_ptr).being_killed(),
        child_scheduler_lock_perm.view().state() is WriteLock,
        child_scheduler_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_scheduler_lock_perm.view().lock_id()
            == old(krnl).sched_mp.spec_index(child_scheduler_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().wlocked_by(old(lctx)),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().view().owning_container == parent_container_ptr,
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_pages.view().contains(thread_page_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_processes.view().contains(parent_process_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view().owned_processes.view().contains(child_process_ptr),
        thread_page_lock_perm.view().state() is WriteLock,
        thread_page_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.view().lock_id()
            == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(thread_page_ptr),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(steps).steps == record_user_view_change(
            old(steps).steps,
            old(steps).snap_shot,
            kernel_k_to_kernel_u(*final(krnl)),
        ),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        new_thread_ptr == thread_page_ptr,
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().owning_container == child_container_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().owning_proc == child_process_ptr,
        final(krnl).ctn_mp.dom().contains(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().parent
            == old(krnl).ctn_mp.spec_index(child_container_ptr)
                .view_rodata().view().parent,
        final(krnl).prc_mp.dom().contains(child_process_ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().owning_container
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .view_rodata().view().owning_container,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k - 1,
{
    let tracked caller_cpu_lock_perm = caller_cpu_lock_perm.get();
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked parent_process_lock_perm = parent_process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked child_container_lock_perm = child_container_lock_perm.get();
    let tracked child_process_lock_perm = child_process_lock_perm.get();
    let tracked child_pagetable_lock_perm = child_pagetable_lock_perm.get();
    let tracked child_scheduler_lock_perm = child_scheduler_lock_perm.get();
    let tracked thread_page_lock_perm = thread_page_lock_perm.get();
    let ghost caller_quota_4k = krnl.thr_mp
        .spec_index(current_thread_ptr).view().quota_4k;
    transfer_staged_thread_page_to_child(
        krnl,
        Tracked(&mut *lctx),
        thread_page_ptr,
        current_thread_ptr,
        parent_container_ptr,
        child_container_ptr,
        Tracked(&thread_page_lock_perm),
        Tracked(&parent_container_lock_perm),
        Tracked(&child_container_lock_perm),
    );
    let (
        new_thread_ptr,
        Tracked(new_thread_lock_perm),
    ) = create_thread_from_staged_page_merged(
        krnl,
        thread_page_ptr,
        child_process_ptr,
        current_thread_ptr,
        child_container_ptr,
        child_scheduler_ptr,
        Tracked(&mut *lctx),
        Tracked(&thread_page_lock_perm),
        Tracked(&child_process_lock_perm),
        Tracked(&current_thread_lock_perm),
        Tracked(&child_scheduler_lock_perm),
    );
    proof {
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k
                == caller_quota_4k - 1
        );
        assert(
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().contains(parent_process_ptr)
        );
        assert(
            krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().contains(child_process_ptr)
        );
    }

    krnl.wunlock_thread(
        new_thread_ptr,
        Tracked(&mut *lctx),
        Tracked(new_thread_lock_perm),
    );
    krnl.wunlock_process(
        child_process_ptr,
        Tracked(&mut *lctx),
        Tracked(child_process_lock_perm),
    );
    krnl.wunlock_pagetable(
        child_pagetable_ptr,
        Tracked(&mut *lctx),
        Tracked(child_pagetable_lock_perm),
    );
    krnl.wunlock_pagetable(
        source_pagetable_ptr,
        Tracked(&mut *lctx),
        Tracked(source_pagetable_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(thread_page_ptr),
        Tracked(&mut *lctx),
        Tracked(thread_page_lock_perm),
    );
    krnl.wunlock_scheduler(
        child_scheduler_ptr,
        Tracked(&mut *lctx),
        Tracked(child_scheduler_lock_perm),
    );
    krnl.wunlock_thread(
        current_thread_ptr,
        Tracked(&mut *lctx),
        Tracked(current_thread_lock_perm),
    );
    proof {
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k
                == caller_quota_4k - 1
        ) by {
            reveal(wunlock_ensures);
        };
        assert(
            krnl.prc_mp.spec_index(parent_process_ptr)
                .view().owned_threads.view().len() != 0
        ) by {
            reveal(process_thread_wf);
        };
    }
    krnl.wunlock_process(
        parent_process_ptr,
        Tracked(&mut *lctx),
        Tracked(parent_process_lock_perm),
    );
    proof {
        assert(
            krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().contains(child_process_ptr)
        ) by {
            reveal(container_process_wf);
        };
        assert(
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().contains(parent_process_ptr)
        );
        assert({
            &&& !krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().is_empty()
            &&& !krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().is_empty()
        }) by {
            reveal(container_process_wf);
        };
    }
    krnl.wunlock_container(
        child_container_ptr,
        Tracked(&mut *lctx),
        Tracked(child_container_lock_perm),
    );
    krnl.wunlock_container(
        parent_container_ptr,
        Tracked(&mut *lctx),
        Tracked(parent_container_lock_perm),
    );
    krnl.wunlock_cpu(
        caller_cpu_id,
        Tracked(&mut *lctx),
        Tracked(caller_cpu_lock_perm),
    );
    proof {
        assert(lctx.no_locks_held()) by {
            reveal(LocalContext::no_locks_held);
        };
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    new_thread_ptr
}

#[verifier::spinoff_prover]
pub(super) fn commit_new_container(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId,
    parent_container_ptr: RwLockContainerPtr,
    parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    source_pagetable_ptr: RwLockPageTableRoot,
    funding_page_count: usize,
    process_quota_4k: usize,
    caller_cpu_lock_perm: Tracked<LockPerm>,
    parent_container_lock_perm: Tracked<LockPerm>,
    parent_process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
) -> (ret: (
    RwLockContainerPtr,
    RwLockProcessPtr,
    RwLockThreadPtr,
))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, caller_cpu_id),
        process_quota_4k <= funding_page_count,
        funding_page_count <= usize::MAX - 8,
        old(lctx).object_lock_scope(
            Set::empty(),
            set![caller_cpu_id],
            set![parent_container_ptr],
            set![parent_process_ptr],
            set![current_thread_ptr],
            Set::empty(),
            Set::empty(),
            Set::empty(),
            set![source_pagetable_ptr],
            Set::empty(),
        ),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().wlocked_by(old(lctx)),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().view().owning_container == parent_container_ptr,
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id()
            == old(krnl).cpu_arr.spec_index(caller_cpu_id)
                .view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view_rodata().view().depth < usize::MAX,
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        old(krnl).prc_mp.spec_index(parent_process_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr)
            .view_rodata().view().owning_container
            == parent_container_ptr,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(parent_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state
            == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k
            >= 8 + funding_page_count,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m
            >= 2,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr)
            .wlocked_by(old(lctx)),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(source_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
    ensures
        final(krnl).inv(),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(steps).steps.len() <= old(steps).steps.len() + 1,
        final(steps).steps.subrange(
            0,
            old(steps).steps.len() as int,
        ) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(krnl).ctn_mp.dom().contains(ret.0),
        final(krnl).ctn_mp.spec_index(ret.0)
            .view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).prc_mp.dom().contains(ret.1),
        final(krnl).prc_mp.spec_index(ret.1)
            .view_rodata().view().owning_container == ret.0,
        final(krnl).thr_mp.dom().contains(ret.2),
        final(krnl).thr_mp.spec_index(ret.2).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(ret.2)
            .view().owning_container == ret.0,
        final(krnl).thr_mp.spec_index(ret.2).view().owning_proc == ret.1,
{
    let tracked caller_cpu_lock_perm = caller_cpu_lock_perm.get();
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked parent_process_lock_perm = parent_process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let (
        container_page,
        child_process_ptr,
        child_pagetable_ptr,
        child_scheduler_ptr,
        thread_page_ptr,
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    ) = {
    let (
        pages_4k,
        container_page,
        pcid_allocator_page,
        Tracked(page_4k_lock_perms),
        Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm),
    ) = allocate_new_container_pages(
        krnl,
        Tracked(&mut *lctx),
        Tracked(&mut *steps),
        current_thread_ptr,
        parent_container_ptr,
        caller_cpu_id,
        Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(
            thread_effective_quota_4k(
                krnl.thr_mp.spec_index(current_thread_ptr),
            ) >= funding_page_count
        ) by {
            reveal(thread_effective_quota_4k);
            reveal(Thread::temp_alloc_clean);
        };
    }
    let ghost krnl_before_funding_pages = *krnl;
    let ghost lctx_before_funding_pages = *lctx;
    let (
        funding_page_head,
        Ghost(funding_pages),
        Tracked(funding_page_lock_perms),
    ) = allocate_staged_4k_page_chain(
        krnl,
        funding_page_count,
        current_thread_ptr,
        parent_container_ptr,
        caller_cpu_id,
        Tracked(&mut *lctx),
        Tracked(&mut *steps),
        Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(allocated_4k_page_lock_perms_wf(
            page_4k_lock_perms,
            krnl,
            lctx,
            current_thread_ptr,
            parent_container_ptr,
        )) by {
            reveal(allocated_4k_page_lock_perms_wf);
            reveal(held_pages_unchanged);
            reveal(Set::contains);
        };
        assert(
            page_ptrs_to_indices(pages_4k.view()).subset_of(
                lctx_before_funding_pages.page_lock_map().dom(),
            )
        ) by {
            reveal(Set::subset_of);
        };
        set_disjoint_from_right_subset(
            page_ptrs_to_indices(funding_pages),
            lctx_before_funding_pages.page_lock_map().dom(),
            page_ptrs_to_indices(pages_4k.view()),
        );
        page_ptr_sets_disjoint_from_index_disjoint(
            funding_pages,
            pages_4k.view(),
        );
    }
    let allocator_quota_4k = funding_page_count - process_quota_4k;
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let child_scheduler_ptr = *pages_4k.get(3);
    let child_process_ptr = *pages_4k.get(4);
    let child_pagetable_ptr = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page_ptr = *pages_4k.get(7);
    proof {
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(
            pcid_allocator_page,
        );
        distinct_2m_heads_have_disjoint_all_ptrs(
            page_ptr2page_index(container_page),
            page_ptr2page_index(pcid_allocator_page),
        );
        owned_2m_all_ptrs_belong_to_container(
            krnl,
            page_ptr2page_index(container_page),
            parent_container_ptr,
        );
        owned_2m_all_ptrs_belong_to_container(
            krnl,
            page_ptr2page_index(pcid_allocator_page),
            parent_container_ptr,
        );
        set_union_subset_of(
            pages_4k.view().to_set(),
            funding_pages.to_set(),
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_pages.view(),
        );
        let ghost parent_owned_pages = krnl.ctn_mp
            .spec_index(parent_container_ptr).view().owned_pages.view();
        let ghost container_all_ptrs = page_2m_all_ptrs(
            page_ptr2page_index(container_page),
        );
        let ghost pcid_allocator_all_ptrs = page_2m_all_ptrs(
            page_ptr2page_index(pcid_allocator_page),
        );
        let ghost bootstrap_pages = new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            child_scheduler_ptr,
            child_process_ptr,
            child_pagetable_ptr,
            l4_page,
        );
        assert(bootstrap_pages.subset_of(
            pages_4k.view().to_set(),
        )) by {
            reveal(Set::subset_of);
            reveal(new_container_bootstrap_4k_pages);
            pages_4k.view().to_set_ensures();
        };
        set_union_subset_of(
            container_all_ptrs,
            pcid_allocator_all_ptrs,
            parent_owned_pages,
        );
        set_union_subset_of(
            container_all_ptrs.union(pcid_allocator_all_ptrs),
            bootstrap_pages,
            parent_owned_pages,
        );
        assert(
            new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                child_scheduler_ptr,
                child_process_ptr,
                child_pagetable_ptr,
                l4_page,
            ).subset_of(parent_owned_pages)
        ) by {
            reveal(new_container_moved_pages);
        };
        set_union_subset_of(
            new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                child_scheduler_ptr,
                child_process_ptr,
                child_pagetable_ptr,
                l4_page,
            ),
            funding_pages.to_set(),
            parent_owned_pages,
        );
        assert(
            new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                child_scheduler_ptr,
                child_process_ptr,
                child_pagetable_ptr,
                l4_page,
            ).union(funding_pages.to_set()).subset_of(
                krnl.ctn_mp.spec_index(parent_container_ptr)
                    .view().owned_pages.view(),
            )
        ) by {
            reveal(Set::subset_of);
        };
        assert(!krnl.ctn_mp.dom().contains(container_page)) by {
            page_ptr_roundtrip();
            reveal(container_pages_wf);
        };
        assert(
            !krnl.pcid_allc_mp.dom().contains(pcid_allocator_page)
        ) by {
            page_ptr_roundtrip();
            reveal(pcid_allocator_pages_wf);
        };
        assert({
            &&& page_4k_lock_perms.dom().contains(allocator_4k_page)
            &&& page_4k_lock_perms.dom().contains(allocator_2m_page)
            &&& page_4k_lock_perms.dom().contains(allocator_1g_page)
            &&& page_4k_lock_perms.dom().contains(child_scheduler_ptr)
            &&& page_4k_lock_perms.dom().contains(child_process_ptr)
            &&& page_4k_lock_perms.dom().contains(child_pagetable_ptr)
        }) by {
            pages_4k.view().to_set_ensures();
        };
        assert({
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                allocator_4k_page,
            )).view().view().state
                == (PageState::Owned4k {
                    thread_ptr: current_thread_ptr,
                })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                allocator_2m_page,
            )).view().view().state
                == (PageState::Owned4k {
                    thread_ptr: current_thread_ptr,
                })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                allocator_1g_page,
            )).view().view().state
                == (PageState::Owned4k {
                    thread_ptr: current_thread_ptr,
                })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                child_scheduler_ptr,
            )).view().view().state
                == (PageState::Owned4k {
                    thread_ptr: current_thread_ptr,
                })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                child_process_ptr,
            )).view().view().state
                == (PageState::Owned4k {
                    thread_ptr: current_thread_ptr,
                })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                child_pagetable_ptr,
            )).view().view().state
                == (PageState::Owned4k {
                    thread_ptr: current_thread_ptr,
                })
        }) by {
            pages_4k.view().to_set_ensures();
            reveal(allocated_4k_page_lock_perms_wf);
        };
        assert(!krnl.allc_4k_mp.dom().contains(allocator_4k_page)) by {
            page_ptr_roundtrip();
            reveal(allocator_4k_pages_wf);
        };
        assert(!krnl.allc_2m_mp.dom().contains(allocator_2m_page)) by {
            page_ptr_roundtrip();
            reveal(allocator_2m_pages_wf);
        };
        assert(!krnl.allc_1g_mp.dom().contains(allocator_1g_page)) by {
            page_ptr_roundtrip();
            reveal(allocator_1g_pages_wf);
        };
        assert(!krnl.sched_mp.dom().contains(child_scheduler_ptr)) by {
            page_ptr_roundtrip();
            reveal(scheduler_pages_wf);
        };
        assert(!krnl.prc_mp.dom().contains(child_process_ptr)) by {
            page_ptr_roundtrip();
            reveal(process_pages_wf);
        };
        assert(!krnl.pt_mp.dom().contains(child_pagetable_ptr)) by {
            page_ptr_roundtrip();
            reveal(pagetable_pages_wf);
        };
        assert(
            lctx.page_lock_map().dom()
                == page_ptrs_to_indices(pages_4k.view())
                    .union(page_ptrs_to_indices(funding_pages))
                    .insert(page_ptr2page_index(container_page))
                    .insert(page_ptr2page_index(pcid_allocator_page))
        );
        assert forall|page_ptr: PagePtr|
            #![trigger pages_4k.view().to_set()
                .union(funding_pages.to_set()).contains(page_ptr)]
            pages_4k.view().to_set().union(funding_pages.to_set())
                .contains(page_ptr) implies {
                &&& page_ptr_valid(page_ptr)
                &&& krnl.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state is Owned4k
            }
        by {
            if pages_4k.view().to_set().contains(page_ptr) {
                assert(page_4k_lock_perms.dom().contains(page_ptr)) by {
                    pages_4k.view().to_set_ensures();
                };
                reveal(allocated_4k_page_lock_perms_wf);
            } else {
                assert(funding_pages.to_set().contains(page_ptr)) by {
                    reveal(Set::contains);
                };
                assert(
                    funding_page_lock_perms.dom().contains(page_ptr)
                ) by {
                    funding_pages.to_set_ensures();
                };
                reveal(allocated_4k_page_lock_perms_wf);
            }
        };
        assert({
            &&& pages_4k.view().to_set().disjoint(
                page_2m_all_ptrs(page_ptr2page_index(container_page)),
            )
            &&& pages_4k.view().to_set().disjoint(
                page_2m_all_ptrs(
                    page_ptr2page_index(pcid_allocator_page),
                ),
            )
        }) by {
            reveal(Set::disjoint);
            if !pages_4k.view().to_set().disjoint(
                page_2m_all_ptrs(page_ptr2page_index(container_page)),
            ) {
                let page_ptr = choose|page_ptr: PagePtr|
                    #[trigger] pages_4k.view().to_set().contains(page_ptr)
                        && page_2m_all_ptrs(
                            page_ptr2page_index(container_page),
                        ).contains(page_ptr);
                assert(
                    pages_4k.view().to_set()
                        .union(funding_pages.to_set())
                        .contains(page_ptr)
                );
                owned_4k_page_not_in_2m_region(
                    krnl,
                    page_ptr,
                    page_ptr2page_index(container_page),
                );
            }
            if !pages_4k.view().to_set().disjoint(
                page_2m_all_ptrs(
                    page_ptr2page_index(pcid_allocator_page),
                ),
            ) {
                let page_ptr = choose|page_ptr: PagePtr|
                    #[trigger] pages_4k.view().to_set().contains(page_ptr)
                        && page_2m_all_ptrs(
                            page_ptr2page_index(pcid_allocator_page),
                        ).contains(page_ptr);
                assert(
                    pages_4k.view().to_set()
                        .union(funding_pages.to_set())
                        .contains(page_ptr)
                );
                owned_4k_page_not_in_2m_region(
                    krnl,
                    page_ptr,
                    page_ptr2page_index(pcid_allocator_page),
                );
            }
        };
        assert(
            funding_pages.to_set().disjoint(new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                child_scheduler_ptr,
                child_process_ptr,
                child_pagetable_ptr,
                l4_page,
            ))
        ) by {
            reveal(Set::disjoint);
            if !funding_pages.to_set().disjoint(
                new_container_moved_pages(
                    container_page,
                    pcid_allocator_page,
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    child_scheduler_ptr,
                    child_process_ptr,
                    child_pagetable_ptr,
                    l4_page,
                ),
            ) {
                let page_ptr = choose|page_ptr: PagePtr|
                    #[trigger] funding_pages.to_set().contains(page_ptr)
                        && new_container_moved_pages(
                        container_page,
                        pcid_allocator_page,
                        allocator_4k_page,
                        allocator_2m_page,
                        allocator_1g_page,
                        child_scheduler_ptr,
                        child_process_ptr,
                        child_pagetable_ptr,
                        l4_page,
                    ).contains(page_ptr);
                assert(
                    pages_4k.view().to_set()
                        .union(funding_pages.to_set())
                        .contains(page_ptr)
                );
                owned_4k_page_not_in_2m_region(
                    krnl,
                    page_ptr,
                    page_ptr2page_index(container_page),
                );
                owned_4k_page_not_in_2m_region(
                    krnl,
                    page_ptr,
                    page_ptr2page_index(pcid_allocator_page),
                );
                if new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    child_scheduler_ptr,
                    child_process_ptr,
                    child_pagetable_ptr,
                    l4_page,
                ).contains(page_ptr) {
                    assert(pages_4k.view().to_set().contains(page_ptr))
                        by {
                            reveal(new_container_bootstrap_4k_pages);
                            pages_4k.view().to_set_ensures();
                        };
                    assert(false) by {
                        reveal(Set::disjoint);
                    };
                }
                reveal(new_container_moved_pages);
            }
        };
        let container_head = page_ptr2page_index(container_page);
        let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
        let page_tails = page_2m_tail_indices(container_head).union(
            page_2m_tail_indices(pcid_allocator_head),
        );
        assert(
            page_ptrs_to_indices(pages_4k.view())
                .union(page_ptrs_to_indices(funding_pages))
                .disjoint(page_tails)
        ) by {
            reveal(Set::disjoint);
            if !page_ptrs_to_indices(pages_4k.view())
                .union(page_ptrs_to_indices(funding_pages))
                .disjoint(page_tails)
            {
                let page_index = choose|page_index: PageIndex|
                    #[trigger] page_ptrs_to_indices(pages_4k.view())
                        .union(page_ptrs_to_indices(funding_pages))
                        .contains(page_index)
                        && page_tails.contains(page_index);
                reveal(page_ptrs_to_indices);
                let pages_indices = pages_4k.view().map_values(
                    |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
                );
                let funding_indices = funding_pages.map_values(
                    |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
                );
                let page_ptr = if pages_indices.to_set()
                    .contains(page_index)
                {
                    pages_indices.to_set_ensures();
                    reveal(Seq::contains);
                    let i = choose|i: int|
                        0 <= i < pages_indices.len()
                            && pages_indices.spec_index(i) == page_index;
                    assert(0 <= i < pages_4k.view().len()) by {
                        reveal(Seq::map_values);
                    };
                    assert(
                        pages_4k.view().to_set().contains(
                            pages_4k.view().spec_index(i),
                        )
                    ) by {
                        pages_4k.view().to_set_ensures();
                        reveal(Seq::contains);
                    };
                    assert(
                        page_ptr2page_index(
                            pages_4k.view().spec_index(i),
                        ) == page_index
                    ) by {
                        reveal(Seq::map_values);
                    };
                    pages_4k.view().spec_index(i)
                } else {
                    assert(
                        funding_indices.to_set().contains(page_index)
                    ) by {
                        reveal(Set::contains);
                    };
                    funding_indices.to_set_ensures();
                    reveal(Seq::contains);
                    let i = choose|i: int|
                        0 <= i < funding_indices.len()
                            && funding_indices.spec_index(i) == page_index;
                    assert(0 <= i < funding_pages.len()) by {
                        reveal(Seq::map_values);
                    };
                    assert(
                        funding_pages.to_set().contains(
                            funding_pages.spec_index(i),
                        )
                    ) by {
                        funding_pages.to_set_ensures();
                        reveal(Seq::contains);
                    };
                    assert(
                        page_ptr2page_index(funding_pages.spec_index(i))
                            == page_index
                    ) by {
                        reveal(Seq::map_values);
                    };
                    funding_pages.spec_index(i)
                };
                assert(
                    pages_4k.view().to_set().union(funding_pages.to_set())
                        .contains(page_ptr)
                );
                owned_4k_page_not_in_2m_tail(
                    krnl,
                    page_ptr,
                    container_head,
                );
                owned_4k_page_not_in_2m_tail(
                    krnl,
                    page_ptr,
                    pcid_allocator_head,
                );
            }
        };
        let container_quotient = container_head / 512usize;
        let pcid_allocator_quotient = pcid_allocator_head / 512usize;
        assert(
            container_head == container_quotient * 512usize
        ) by (nonlinear_arith)
            requires
                container_head % 512usize == 0,
                container_quotient == container_head / 512usize;
        assert(
            pcid_allocator_head == pcid_allocator_quotient * 512usize
        ) by (nonlinear_arith)
            requires
                pcid_allocator_head % 512usize == 0,
                pcid_allocator_quotient
                    == pcid_allocator_head / 512usize;
        assert(
            container_head + 512usize <= pcid_allocator_head
                || pcid_allocator_head + 512usize <= container_head
        ) by (nonlinear_arith)
            requires
                container_head == container_quotient * 512usize,
                pcid_allocator_head
                    == pcid_allocator_quotient * 512usize,
                container_head != pcid_allocator_head;
        assert({
            &&& !page_tails.contains(container_head)
            &&& !page_tails.contains(pcid_allocator_head)
        }) by {
            reveal(page_2m_tail_indices);
            reveal(Set::contains);
        };
        assert(
            lctx.page_lock_map().dom().disjoint(page_tails)
        ) by {
            reveal(Set::disjoint);
        };
    }
    let (
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    ) = publish_new_container_base(
        krnl,
        Tracked(&mut *lctx),
        caller_cpu_id,
        parent_container_ptr,
        parent_process_ptr,
        current_thread_ptr,
        source_pagetable_ptr,
        &pages_4k,
        container_page,
        pcid_allocator_page,
        funding_page_count,
        funding_page_head,
        Ghost(funding_pages),
        allocator_quota_4k,
        process_quota_4k,
        Tracked(page_4k_lock_perms),
        Tracked(funding_page_lock_perms),
        Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm),
        Tracked(&parent_container_lock_perm),
        Tracked(&current_thread_lock_perm),
    );
    (
        container_page,
        child_process_ptr,
        child_pagetable_ptr,
        child_scheduler_ptr,
        thread_page_ptr,
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    )
    };
    let new_thread_ptr = create_root_thread_and_finish_new_container(
        krnl,
        Tracked(&mut *lctx),
        Tracked(&mut *steps),
        caller_cpu_id,
        parent_container_ptr,
        parent_process_ptr,
        current_thread_ptr,
        source_pagetable_ptr,
        container_page,
        child_process_ptr,
        child_pagetable_ptr,
        child_scheduler_ptr,
        thread_page_ptr,
        Tracked(caller_cpu_lock_perm),
        Tracked(parent_container_lock_perm),
        Tracked(parent_process_lock_perm),
        Tracked(current_thread_lock_perm),
        Tracked(source_pagetable_lock_perm),
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    );
    (container_page, child_process_ptr, new_thread_ptr)
}

}

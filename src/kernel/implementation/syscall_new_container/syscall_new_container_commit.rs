use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::staged_4k_page_chain::{
    allocate_staged_4k_page_chain,
    page_ptr_sets_disjoint_from_index_disjoint,
    set_disjoint_from_right_subset,
    set_union_subset_of,
};
use super::*;

verus! {
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
pub(super) fn commit_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    funding_page_count: usize, process_quota_4k: usize, caller_cpu_lock_perm: Tracked<LockPerm>,
    parent_container_lock_perm: Tracked<LockPerm>, parent_process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, source_pagetable_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
) -> (ret: (RwLockContainerPtr, RwLockProcessPtr, RwLockThreadPtr))
    requires
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, caller_cpu_id),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        process_quota_4k <= funding_page_count,
        funding_page_count <= usize::MAX - 9,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().view().view().owning_container == parent_container_ptr,
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id()
            == old(krnl).cpu_arr.spec_index(caller_cpu_id)
                .view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
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
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
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
            >= 9 + funding_page_count,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m
            >= 2,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
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
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(steps).steps.len() <= old(steps).steps.len() + 1,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(krnl).ctn_mp.dom().contains(ret.0),
        final(krnl).ctn_mp.spec_index(ret.0)
            .view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).prc_mp.dom().contains(ret.1),
        final(krnl).prc_mp.spec_index(ret.1)
            .view_rodata().view().owning_container == ret.0,
        final(krnl).prc_mp.spec_index(ret.1)
            .view().quota_4k == process_quota_4k,
        final(krnl).allc_4k_mp.dom().contains(
            final(krnl).ctn_mp.spec_index(ret.0)
                .view_rodata().view().allocator_ptr_4k,
        ),
        final(krnl).allc_4k_mp.spec_index(
            final(krnl).ctn_mp.spec_index(ret.0)
                .view_rodata().view().allocator_ptr_4k,
        ).total_free_pages.view() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(
            final(krnl).ctn_mp.spec_index(ret.0)
                .view_rodata().view().allocator_ptr_4k,
        ).quota.view().view() == funding_page_count - process_quota_4k,
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
        allocator_4k_page,
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
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, parent_container_ptr, caller_cpu_id,
        Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(
            thread_effective_quota_4k(
                krnl.thr_mp.spec_index(current_thread_ptr),
            ) >= funding_page_count
        );
    }
    let ghost lctx_before_funding_pages = *lctx;
    let (
        funding_page_head,
        Ghost(funding_pages),
        Tracked(funding_page_lock_perms),
    ) = allocate_staged_4k_page_chain(
        krnl, funding_page_count, current_thread_ptr, parent_container_ptr, caller_cpu_id,
        Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(allocated_4k_page_lock_perms_wf(
            page_4k_lock_perms,
            krnl,
            lctx,
            current_thread_ptr,
            parent_container_ptr,
        ));
        assert(
            page_ptrs_to_indices(pages_4k.view()).subset_of(
                lctx_before_funding_pages.page_lock_map().dom(),
            )
        );
        set_disjoint_from_right_subset(
            page_ptrs_to_indices(funding_pages), lctx_before_funding_pages.page_lock_map().dom(), page_ptrs_to_indices(pages_4k.view()),
        );
        page_ptr_sets_disjoint_from_index_disjoint(funding_pages, pages_4k.view());
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
        distinct_2m_heads_have_disjoint_all_ptrs(page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page));
        owned_2m_all_ptrs_belong_to_container(krnl, page_ptr2page_index(container_page), parent_container_ptr);
        owned_2m_all_ptrs_belong_to_container(krnl, page_ptr2page_index(pcid_allocator_page), parent_container_ptr);
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
            child_scheduler_ptr, pages_4k.view().spec_index(8),
            child_process_ptr,
            child_pagetable_ptr,
            l4_page);
        assert(bootstrap_pages.subset_of(
            pages_4k.view().to_set(),
        )) by {
            reveal(new_container_bootstrap_4k_pages);
            pages_4k.view().to_set_ensures();
        };
        assert(page_ptrs_to_indices(pages_4k.view()) == set![
            page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page),
            page_ptr2page_index(allocator_1g_page),
            page_ptr2page_index(child_scheduler_ptr),
            page_ptr2page_index(pages_4k.view().spec_index(8)),
            page_ptr2page_index(child_process_ptr),
            page_ptr2page_index(child_pagetable_ptr),
            page_ptr2page_index(l4_page),
            page_ptr2page_index(thread_page_ptr),
        ]) by {
            let mapped = pages_4k.view().map_values(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
            );
            assert(
                mapped.to_set().contains(mapped.spec_index(0))
                    && mapped.to_set().contains(mapped.spec_index(1))
                    && mapped.to_set().contains(mapped.spec_index(2))
                    && mapped.to_set().contains(mapped.spec_index(3))
                    && mapped.to_set().contains(mapped.spec_index(4))
                    && mapped.to_set().contains(mapped.spec_index(5))
                    && mapped.to_set().contains(mapped.spec_index(6))
                    && mapped.to_set().contains(mapped.spec_index(7))
                    && mapped.to_set().contains(mapped.spec_index(8))
            ) by {
                mapped.to_set_ensures();
            };
            assert_sets_equal!(
                page_ptrs_to_indices(pages_4k.view()) == set![
                    page_ptr2page_index(allocator_4k_page),
                    page_ptr2page_index(allocator_2m_page),
                    page_ptr2page_index(allocator_1g_page),
                    page_ptr2page_index(child_scheduler_ptr),
                    page_ptr2page_index(pages_4k.view().spec_index(8)),
                    page_ptr2page_index(child_process_ptr),
                    page_ptr2page_index(child_pagetable_ptr),
                    page_ptr2page_index(l4_page),
                    page_ptr2page_index(thread_page_ptr),
                ],
                page_index => {
                    mapped.to_set_ensures();
                }
            );
        };
        set_union_subset_of(container_all_ptrs, pcid_allocator_all_ptrs, parent_owned_pages);
        set_union_subset_of(container_all_ptrs.union(pcid_allocator_all_ptrs), bootstrap_pages, parent_owned_pages);
        assert(
            new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                child_scheduler_ptr, pages_4k.view().spec_index(8),
                child_process_ptr,
                child_pagetable_ptr,
                l4_page).subset_of(parent_owned_pages)
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
                child_scheduler_ptr, pages_4k.view().spec_index(8),
                child_process_ptr,
                child_pagetable_ptr,
                l4_page),
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
                child_scheduler_ptr, pages_4k.view().spec_index(8),
                child_process_ptr,
                child_pagetable_ptr,
                l4_page).union(funding_pages.to_set()).subset_of(
                krnl.ctn_mp.spec_index(parent_container_ptr)
                    .view().owned_pages.view(),
            )
        );
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
        assert(!krnl.cpu_set_mp.dom().contains(pages_4k.view().spec_index(8))) by { reveal(cpu_set_pages_wf); assert(page_4k_lock_perms.dom().contains(pages_4k.view().spec_index(8))) by { pages_4k.view().to_set_ensures(); }; };
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
                    .union(seq![
                        page_ptr2page_index(container_page),
                        page_ptr2page_index(pcid_allocator_page),
                    ].to_set())
        ) by {
            seq![
                page_ptr2page_index(container_page),
                page_ptr2page_index(pcid_allocator_page),
            ].to_set_ensures();
        };
        new_container_staged_pages_disjoint(
            krnl, lctx, &pages_4k, funding_pages, page_4k_lock_perms, funding_page_lock_perms, current_thread_ptr, parent_container_ptr,
            container_page, pcid_allocator_page,
        );
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    let (
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    ) = publish_new_container_base(
        krnl, Tracked(&mut *lctx), caller_cpu_id, parent_container_ptr, parent_process_ptr,
        current_thread_ptr, source_pagetable_ptr, &pages_4k, container_page, pcid_allocator_page,
        funding_page_count, funding_page_head, Ghost(funding_pages), allocator_quota_4k, process_quota_4k,
        Tracked(page_4k_lock_perms), Tracked(funding_page_lock_perms),
        Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
        Tracked(&parent_container_lock_perm), Tracked(&current_thread_lock_perm),
    );
    (
        container_page,
        allocator_4k_page,
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
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, parent_container_ptr,
        parent_process_ptr, current_thread_ptr, source_pagetable_ptr, container_page, child_process_ptr,
        child_pagetable_ptr, child_scheduler_ptr, allocator_4k_page, thread_page_ptr,
        Tracked(caller_cpu_lock_perm), Tracked(parent_container_lock_perm), Tracked(parent_process_lock_perm),
        Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm), initial_regs,
    );
    (container_page, child_process_ptr, new_thread_ptr)
}
}

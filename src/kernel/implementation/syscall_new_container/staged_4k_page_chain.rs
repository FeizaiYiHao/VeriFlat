use vstd::{assert_maps_equal, assert_seqs_equal, assert_sets_equal};
use vstd::prelude::*;
use crate::*;

verus! {
pub(super) proof fn page_ptr_sets_disjoint_from_index_disjoint(
    left: Seq<PagePtr>,
    right: Seq<PagePtr>,
)
    requires
        page_ptrs_to_indices(left).disjoint(
            page_ptrs_to_indices(right),
        ),
    ensures
        left.to_set().disjoint(right.to_set()),
{
    if !left.to_set().disjoint(right.to_set()) {
        reveal(page_ptrs_to_indices);
        reveal(Set::disjoint);
        broadcast use Seq::lemma_to_set_map_commutes;
        broadcast use Set::lemma_map_contains;
        let page_ptr = choose|page_ptr: PagePtr|
            left.to_set().contains(page_ptr)
                && right.to_set().contains(page_ptr);
        assert(left.to_set().map(
            |p: PagePtr| page_ptr2page_index(p),
        ).contains(page_ptr2page_index(page_ptr)));
        assert(right.to_set().map(
            |p: PagePtr| page_ptr2page_index(p),
        ).contains(page_ptr2page_index(page_ptr)));
    }
}

pub(super) proof fn set_disjoint_from_right_subset<A>(
    left: Set<A>,
    right: Set<A>,
    subset: Set<A>,
)
    requires
        left.disjoint(right),
        subset.subset_of(right),
    ensures
        left.disjoint(subset),
{
    assert(left.disjoint(subset)) by {
        reveal(Set::disjoint);
        reveal(Set::subset_of);
    };
}

pub(super) proof fn set_union_subset_of<A>(
    left: Set<A>,
    right: Set<A>,
    superset: Set<A>,
)
    requires
        left.subset_of(superset),
        right.subset_of(superset),
    ensures
        left.union(right).subset_of(superset),
{
    assert(left.union(right).subset_of(superset)) by {
        reveal(Set::subset_of);
    };
}

#[verifier::spinoff_prover]
pub(super) fn set_4k_page_staging_next(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&LocalContext>,
    page_ptr: PagePtr,
    next: PagePtr,
    Tracked(page_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lock_id_set_aligned(lctx),
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().wlocked_by(lctx),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().state is Owned4k
            || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state is Free4k,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
        final(krnl).pg_arr.entries_unchanged_except(
            &old(krnl).pg_arr,
            page_ptr2page_index(page_ptr),
        ),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().free_list == next,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().state
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().owning_container
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().owning_container,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().wlocked_by(lctx),
        page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().locking_thread()->Write_lock_id,
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).irt == old(krnl).irt,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).ctn_mp == old(krnl).ctn_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).thr_mp == old(krnl).thr_mp,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        final(krnl).rt_ctn == old(krnl).rt_ctn,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
{
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert({
            &&& krnl.pg_arr.inv()
            &&& krnl.pg_arr.spec_index(page_index).view().is_init()
            &&& krnl.pg_arr.spec_index(page_index).view().view().inv()
        }) by {
            reveal(page_array_wf);
        };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(
            page_index,
            Ghost(lctx.page_lock_map()),
            Tracked(lctx),
            Tracked(page_lock_perm),
        );
        set_4k_staging_next(page, next);
    }
    proof {
        assert(krnl.subsystems_inv()) by {
            reveal(KernelK::default_pagetable_wf);
            reveal(page_array_wf);
        };
        assert(allocator_pages_wf(
            krnl.pg_arr,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(allocator_4k_pages_wf);
            reveal(allocator_2m_pages_wf);
            reveal(allocator_1g_pages_wf);
        };
        assert(container_page_owner_wf(
            krnl.ctn_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_page_owner_wf);
        };
        assert(hugepage_2m_wf(krnl.pg_arr)) by {
            reveal(hugepage_2m_wf);
        };
        assert(hugepage_1g_wf(krnl.pg_arr)) by {
            reveal(hugepage_1g_wf);
        };
        assert(page_pagetable_wf(
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            page_pagetable_wf_preserved_for_nonmapped_page_change(
                old(krnl).pt_mp,
                krnl.pt_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
                page_index,
            );
        };
        assert(container_process_page_pagetable_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_process_page_pagetable_wf);
        };
        assert(container_pages_wf(
            krnl.pg_arr,
            krnl.ctn_mp,
        )) by {
            reveal(container_pages_wf);
        };
        assert(process_pages_wf(
            krnl.pg_arr,
            krnl.prc_mp,
        )) by {
            reveal(process_pages_wf);
        };
        assert(pagetable_pages_wf(
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            reveal(pagetable_pages_wf);
        };
        assert(iommu_table_pages_wf(
            krnl.it_mp,
            krnl.pg_arr,
        )) by {
            reveal(iommu_table_pages_wf);
        };
        assert(thread_pages_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            reveal(thread_pages_wf);
        };
        assert(scheduler_pages_wf(
            krnl.sched_mp,
            krnl.pg_arr,
        )) by {
            reveal(scheduler_pages_wf);
        };
        assert(pcid_allocator_pages_wf(
            krnl.pg_arr,
            krnl.pcid_allc_mp,
        )) by {
            reveal(pcid_allocator_pages_wf);
        };
        assert(thread_staged_pages_4k_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            thread_staged_pages_4k_wf_preserved_for_eq(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
            );
        };
        assert(thread_staged_pages_2m_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            thread_staged_pages_2m_wf_preserved_for_eq(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
            );
        };
        assert(thread_staged_pages_1g_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            thread_staged_pages_1g_wf_preserved_for_eq(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
            );
        };
        assert(endpoint_pages_wf(
            krnl.ep_mp,
            krnl.pg_arr,
        )) by {
            reveal(endpoint_pages_wf);
        };
        assert(krnl.allocator_free_pages_wf()) by {
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_process_allocator_quota_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
            krnl.thr_mp,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
        };
        assert(container_allocator_wf(
            krnl.ctn_mp,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(container_allocator_wf);
        };
        assert(container_allocator_free_4k_page_wf(
            krnl.allc_4k_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_allocator_free_2m_page_wf(
            krnl.allc_2m_mp,
            krnl.pg_arr,
        )) by {
            container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_2m_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
                page_index,
            );
        };
        assert(container_allocator_free_1g_page_wf(
            krnl.allc_1g_mp,
            krnl.pg_arr,
        )) by {
            container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_1g_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
                page_index,
            );
        };
        assert(
            kernel_k_to_kernel_u(*krnl)
                == kernel_k_to_kernel_u(*old(krnl))
        ) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                old(krnl),
                krnl,
            );
        };
    }
}

#[verifier::spinoff_prover]
pub(super) fn cleanup_published_4k_page_chain(
    krnl: &mut KernelK,
    count: usize,
    head: PagePtr,
    Ghost(page_ptrs): Ghost<Seq<PagePtr>>,
    child_allocator_ptr: RwLockPageAllocatorPtr,
    child_container_ptr: RwLockContainerPtr,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        page_ptrs.len() == count,
        page_ptrs.no_duplicates(),
        head == staged_4k_page_chain_head(page_ptrs),
        page_lock_perms.dom() == page_ptrs.to_set(),
        staged_4k_page_chain(old(krnl).pg_arr, page_ptrs),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_ptr),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == child_container_ptr
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().wlocked_by(old(lctx))
                &&& page_lock_perms.spec_index(page_ptr).state()
                    is WriteLock
                &&& page_lock_perms.spec_index(page_ptr).thread_id()
                    == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(page_ptr).lock_id()
                    == old(krnl).pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().locking_thread()->Write_lock_id
            },
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().submap_of(
            old(lctx).page_lock_map(),
        ),
        final(lctx).page_lock_map()
            .remove_keys(page_ptrs_to_indices(page_ptrs))
            == old(lctx).page_lock_map()
                .remove_keys(page_ptrs_to_indices(page_ptrs)),
        final(lctx).page_lock_map().dom().disjoint(
            page_ptrs_to_indices(page_ptrs),
        ),
        final(lctx).page_lock_map()
            == old(lctx).page_lock_map()
                .remove_keys(page_ptrs_to_indices(page_ptrs)),
        held_pages_unchanged_except(
            old(krnl).pg_arr,
            final(krnl).pg_arr,
            old(lctx),
            page_ptrs_to_indices(page_ptrs),
        ),
        forall|page_index: PageIndex|
            #![trigger old(lctx).page_lock_map().dom().contains(page_index)]
            #![trigger old(krnl).pg_arr.spec_index(page_index)]
            old(lctx).page_lock_map().dom().contains(page_index)
                && old(krnl).pg_arr.spec_index(page_index)
                    .view().view().state is Merged2m
            ==> {
                &&& final(lctx).page_lock_map().dom()
                    .contains(page_index)
                &&& final(lctx).page_lock_map()
                    .spec_index(page_index)
                    == old(lctx).page_lock_map().spec_index(page_index)
                &&& final(krnl).pg_arr.spec_index(page_index).view()
                    == old(krnl).pg_arr.spec_index(page_index).view()
            },
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
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).irt == old(krnl).irt,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).ctn_mp == old(krnl).ctn_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).thr_mp == old(krnl).thr_mp,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        final(krnl).rt_ctn == old(krnl).rt_ctn,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
        forall|page_index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(page_index)]
            #![trigger old(krnl).pg_arr.spec_index(page_index)]
            index_valid(NUM_PAGES, page_index)
                && !page_ptrs_to_indices(page_ptrs).contains(page_index)
            ==> final(krnl).pg_arr.spec_index(page_index)
                == old(krnl).pg_arr.spec_index(page_index),
        forall|page_ptr: PagePtr|
            #![trigger page_ptrs.to_set().contains(page_ptr)]
            page_ptrs.to_set().contains(page_ptr) ==> {
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().free_list == 0
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_ptr),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == child_container_ptr
                &&& !final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().locked_by_thread(final(lctx).thread_id())
            },
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
{
    let tracked mut page_lock_perms = page_lock_perms;
    let mut current = head;
    let mut remaining = count;
    proof {
        assert(
            page_ptrs.subrange(0, count as int) == page_ptrs
        ) by {
            assert_seqs_equal!(
                page_ptrs.subrange(0, count as int),
                page_ptrs,
                i => {}
            );
        };
        assert(
            lctx.page_lock_map().submap_of(
                old(lctx).page_lock_map(),
            )
        ) by {
            reveal(Map::submap_of);
        };
        assert(
            page_lock_perms.dom()
                == page_ptrs.subrange(0, remaining as int).to_set()
        ) by {
            assert_sets_equal!(
                page_lock_perms.dom()
                    == page_ptrs.subrange(0, remaining as int).to_set(),
                page_ptr => {
                    page_ptrs.to_set_ensures();
                    page_ptrs.subrange(0, remaining as int).to_set_ensures();
                }
            );
        };
    }
    while remaining > 0
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_aligned(krnl, lctx),
            lock_id_set_aligned(lctx),
            page_ptrs.len() == count,
            page_ptrs.no_duplicates(),
            forall|page_ptr: PagePtr|
                #![trigger page_ptrs.to_set().contains(page_ptr)]
                page_ptrs.to_set().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& old(krnl).pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().view().state is Free4k
                },
            0 <= remaining <= count,
            current == if remaining == 0 {
                STAGED_4K_PAGE_CHAIN_END
            } else {
                page_ptrs.spec_index(remaining - 1)
            },
            page_lock_perms.dom()
                == page_ptrs.subrange(0, remaining as int).to_set(),
            lctx.page_lock_map().submap_of(
                old(lctx).page_lock_map(),
            ),
            lctx.page_lock_map()
                .remove_keys(page_ptrs_to_indices(page_ptrs))
                == old(lctx).page_lock_map()
                    .remove_keys(page_ptrs_to_indices(page_ptrs)),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map()
                == old(lctx).pcid_allocator_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map()
                == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps()
                == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps()
                == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps()
                == old(lctx).allocator_1g_lock_maps(),
            krnl.pt_mp == old(krnl).pt_mp,
            krnl.it_mp == old(krnl).it_mp,
            krnl.irt == old(krnl).irt,
            krnl.cpu_arr == old(krnl).cpu_arr,
            krnl.ctn_mp == old(krnl).ctn_mp,
            krnl.sched_mp == old(krnl).sched_mp,
            krnl.pcid_allc_mp == old(krnl).pcid_allc_mp,
            krnl.prc_mp == old(krnl).prc_mp,
            krnl.thr_mp == old(krnl).thr_mp,
            krnl.ep_mp == old(krnl).ep_mp,
            krnl.allc_4k_mp == old(krnl).allc_4k_mp,
            krnl.allc_2m_mp == old(krnl).allc_2m_mp,
            krnl.allc_1g_mp == old(krnl).allc_1g_mp,
            krnl.cpu_tlb == old(krnl).cpu_tlb,
            krnl.iommu_tlb == old(krnl).iommu_tlb,
            krnl.rt_ctn == old(krnl).rt_ctn,
            krnl.dflt_pt == old(krnl).dflt_pt,
            forall|page_index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(page_index)]
                #![trigger old(krnl).pg_arr.spec_index(page_index)]
                index_valid(NUM_PAGES, page_index)
                    && !page_ptrs_to_indices(page_ptrs)
                        .contains(page_index)
                ==> krnl.pg_arr.spec_index(page_index)
                    == old(krnl).pg_arr.spec_index(page_index),
            forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list]
                0 <= i < remaining ==> {
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list
                        == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                },
            forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list]
                remaining <= i < count ==> {
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list == 0
                    &&& !lctx.page_lock_map().dom().contains(
                        page_ptr2page_index(page_ptrs.spec_index(i)),
                    )
                },
            forall|page_ptr: PagePtr|
                #![trigger page_ptrs.to_set().contains(page_ptr)]
                page_ptrs.to_set().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& krnl.pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
                    &&& krnl.pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().view().owning_container
                        == child_container_ptr
                },
            forall|page_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(page_ptr)]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& krnl.pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().wlocked_by(lctx)
                    &&& page_lock_perms.spec_index(page_ptr).state()
                        is WriteLock
                    &&& page_lock_perms.spec_index(page_ptr).thread_id()
                        == lctx.thread_id()
                    &&& page_lock_perms.spec_index(page_ptr).lock_id()
                        == krnl.pg_arr.spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().locking_thread()->Write_lock_id
                },
        decreases remaining,
    {
        let page_ptr = current;
        let old_remaining = remaining;
        let ghost krnl_before = *krnl;
        let ghost lctx_before = *lctx;
        proof {
            assert({
                &&& 0 <= remaining - 1 < page_ptrs.len()
                &&& page_ptr == page_ptrs.spec_index(remaining - 1)
            }) by {
                reveal(Seq::contains);
            };
            assert(page_ptrs.to_set().contains(page_ptr)) by {
                page_ptrs.to_set_ensures();
                reveal(Seq::contains);
            };
            assert(
                page_ptrs.subrange(0, remaining as int)
                    .spec_index(remaining - 1) == page_ptr
            ) by {
                vstd::seq::lemma_seq_subrange_index(
                    page_ptrs,
                    0,
                    remaining as int,
                    remaining - 1,
                );
            };
            assert(
                page_ptrs.subrange(0, remaining as int)
                    .to_set().contains(page_ptr)
            ) by {
                page_ptrs.subrange(0, remaining as int).to_set_ensures();
                reveal(Seq::contains);
            };
            assert(page_lock_perms.dom().contains(page_ptr)) by {
                page_ptrs.subrange(0, remaining as int).to_set_ensures();
            };
            assert(page_ptr_valid(page_ptr)) by {
                page_ptrs.to_set_ensures();
            };
            page_ptr_valid_imply_page_index_valid();
            assert(krnl.pg_arr.inv()) by {
                reveal(page_array_wf);
            };
        }
        let page_index = page_ptr2page_index(page_ptr);
        let next = {
            let page = krnl.pg_arr.borrow(
                page_index,
                Tracked(page_lock_perms.tracked_borrow(page_ptr)),
            );
            page.free_list
        };
        set_4k_page_staging_next(
            krnl,
            Tracked(&*lctx),
            page_ptr,
            0,
            Tracked(page_lock_perms.tracked_borrow(page_ptr)),
        );
        let ghost krnl_after_clear = *krnl;
        let tracked page_lock_perm = page_lock_perms.tracked_remove(page_ptr);
        krnl.wunlock_page(
            page_index,
            Tracked(&mut *lctx),
            Tracked(page_lock_perm),
        );
        current = next;
        remaining = remaining - 1;
        proof {
            broadcast use vstd::map::lemma_map_remove_domain;
            assert(page_ptrs_to_indices(page_ptrs).contains(
                page_index,
            )) by {
                reveal(page_ptrs_to_indices);
                let mapped = page_ptrs.map_values(
                    |p: PagePtr| page_ptr2page_index(p),
                );
                mapped.to_set_ensures();
                assert(mapped.spec_index(old_remaining - 1)
                    == page_index);
            };
            assert(
                lctx.page_lock_map()
                    .remove_keys(page_ptrs_to_indices(page_ptrs))
                    == old(lctx).page_lock_map()
                        .remove_keys(page_ptrs_to_indices(page_ptrs))
            ) by {
                reveal(typed_lock_maps_removed);
                reveal(Map::remove_keys);
            };
            assert(
                page_lock_perms.dom()
                    == page_ptrs.subrange(0, remaining as int).to_set()
            ) by {
                assert_sets_equal!(
                    page_lock_perms.dom()
                        == page_ptrs.subrange(0, remaining as int)
                            .to_set(),
                    candidate => {
                        seq_subrange_split_lemma::<PagePtr>();
                        page_ptrs.subrange(0, remaining as int)
                            .to_set_ensures();
                        page_ptrs.subrange(
                            0,
                            (remaining + 1) as int,
                        ).to_set_ensures();
                    }
                );
            };
            assert(
                lctx.page_lock_map().submap_of(
                    old(lctx).page_lock_map(),
                )
            ) by {
                reveal(typed_lock_maps_removed);
            };
            assert forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list]
                0 <= i < remaining implies {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list
                        == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                } by {
                let other_ptr = page_ptrs.spec_index(i);
                assert(page_ptrs.to_set().contains(other_ptr)) by {
                    page_ptrs.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(
                    page_ptr2page_index(other_ptr) != page_index
                ) by {
                    page_ptr2page_index_injective();
                };
                assert(
                    krnl_after_clear.pg_arr.spec_index(
                        page_ptr2page_index(other_ptr),
                    ) == krnl_before.pg_arr.spec_index(
                        page_ptr2page_index(other_ptr),
                    )
                ) by {
                    reveal(LockedArray::entries_unchanged_except);
                };
                assert(
                    krnl.pg_arr.spec_index(
                        page_ptr2page_index(other_ptr),
                    ).view().view()
                        == krnl_after_clear.pg_arr.spec_index(
                            page_ptr2page_index(other_ptr),
                        ).view().view()
                ) by {
                    reveal(LockedArray::unchanged_except);
                };
            };
            assert forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list]
                remaining <= i < count implies {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list == 0
                    &&& !lctx.page_lock_map().dom().contains(
                        page_ptr2page_index(page_ptrs.spec_index(i)),
                    )
                } by {
                let other_ptr = page_ptrs.spec_index(i);
                assert(page_ptrs.to_set().contains(other_ptr)) by {
                    page_ptrs.to_set_ensures();
                    reveal(Seq::contains);
                };
                if i == remaining {
                    assert(
                        krnl.pg_arr.spec_index(page_index)
                            .view().view()
                            == krnl_after_clear.pg_arr.spec_index(
                                page_index,
                            ).view().view()
                    ) by {
                        reveal(LockedArray::unchanged_except);
                    };
                    assert(
                        !lctx.page_lock_map().dom().contains(page_index)
                    ) by {
                        reveal(typed_lock_maps_removed);
                    };
                } else {
                    assert(
                        page_ptr2page_index(other_ptr) != page_index
                    ) by {
                        page_ptr2page_index_injective();
                    };
                    assert(
                        krnl_after_clear.pg_arr.spec_index(
                            page_ptr2page_index(other_ptr),
                        ) == krnl_before.pg_arr.spec_index(
                            page_ptr2page_index(other_ptr),
                        )
                    ) by {
                        reveal(LockedArray::entries_unchanged_except);
                    };
                    assert(
                        krnl.pg_arr.spec_index(
                            page_ptr2page_index(other_ptr),
                        ).view().view()
                            == krnl_after_clear.pg_arr.spec_index(
                                page_ptr2page_index(other_ptr),
                            ).view().view()
                    ) by {
                        reveal(LockedArray::unchanged_except);
                    };
                    assert(
                        !lctx.page_lock_map().dom().contains(
                            page_ptr2page_index(other_ptr),
                        )
                    ) by {
                        assert(
                            krnl_before.pg_arr.spec_index(
                                page_ptr2page_index(other_ptr),
                            ).view().view().free_list == 0
                        );
                        assert(
                            !lctx_before.page_lock_map().dom().contains(
                                page_ptr2page_index(other_ptr),
                            )
                        );
                        assert(
                            lctx.page_lock_map()
                                == lctx_before.page_lock_map().remove(
                                    page_index,
                                )
                        ) by {
                            reveal(typed_lock_maps_removed);
                        };
                        reveal(typed_lock_maps_removed);
                    };
                }
            };
        }
    }
    proof {
        held_pages_unchanged_except_for_changed_set(
            old(krnl).pg_arr,
            krnl.pg_arr,
            old(lctx),
            page_ptrs_to_indices(page_ptrs),
        );
        let mapped = page_ptrs.map_values(
            |p: PagePtr| page_ptr2page_index(p),
        );
        assert(
            lctx.page_lock_map().dom().disjoint(
                page_ptrs_to_indices(page_ptrs),
            )
        ) by {
            reveal(page_ptrs_to_indices);
            reveal(Set::disjoint);
            if !lctx.page_lock_map().dom().disjoint(mapped.to_set()) {
                let page_index = choose|page_index: PageIndex|
                    lctx.page_lock_map().dom().contains(page_index)
                        && #[trigger] mapped.to_set().contains(page_index);
                mapped.to_set_ensures();
                reveal(Seq::contains);
                let i = choose|i: int|
                    0 <= i < mapped.len()
                        && mapped.spec_index(i) == page_index;
                assert(page_ptrs.to_set().contains(
                    page_ptrs.spec_index(i),
                )) by {
                    page_ptrs.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(
                    page_index == page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )
                );
                assert(
                    krnl.pg_arr.spec_index(page_index)
                        .view().view().free_list == 0
                );
                assert(
                    !lctx.page_lock_map().dom().contains(page_index)
                );
            }
        };
        assert(
            lctx.page_lock_map()
                == old(lctx).page_lock_map()
                    .remove_keys(page_ptrs_to_indices(page_ptrs))
        ) by {
            reveal(Map::remove_keys);
            reveal(Map::submap_of);
            reveal(Set::disjoint);
            assert_maps_equal!(
                lctx.page_lock_map(),
                old(lctx).page_lock_map()
                    .remove_keys(page_ptrs_to_indices(page_ptrs)),
                page_index => {}
            );
        };
        assert forall|page_index: PageIndex|
            #![trigger old(lctx).page_lock_map().dom()
                .contains(page_index)]
            #![trigger old(krnl).pg_arr.spec_index(page_index)]
            old(lctx).page_lock_map().dom().contains(page_index)
                && old(krnl).pg_arr.spec_index(page_index)
                    .view().view().state is Merged2m
            implies {
                &&& lctx.page_lock_map().dom().contains(page_index)
                &&& lctx.page_lock_map().spec_index(page_index)
                    == old(lctx).page_lock_map().spec_index(page_index)
                &&& krnl.pg_arr.spec_index(page_index).view()
                    == old(krnl).pg_arr.spec_index(page_index).view()
            } by {
            assert(
                !page_ptrs_to_indices(page_ptrs).contains(page_index)
            ) by {
                if page_ptrs_to_indices(page_ptrs).contains(page_index) {
                    reveal(page_ptrs_to_indices);
                    let mapped = page_ptrs.map_values(
                        |page_ptr: PagePtr| {
                            page_ptr2page_index(page_ptr)
                        },
                    );
                    mapped.to_set_ensures();
                    reveal(Seq::contains);
                    let i = choose|i: int|
                        0 <= i < mapped.len()
                            && mapped.spec_index(i) == page_index;
                    assert(0 <= i < page_ptrs.len()) by {
                        reveal(Seq::map_values);
                    };
                    assert(page_ptrs.to_set().contains(
                        page_ptrs.spec_index(i),
                    )) by {
                        page_ptrs.to_set_ensures();
                        reveal(Seq::contains);
                    };
                    assert(
                        old(krnl).pg_arr.spec_index(page_index)
                            .view().view().state is Free4k
                    ) by {
                        reveal(Seq::map_values);
                    };
                }
            };
            assert(
                lctx.page_lock_map().dom().contains(page_index)
            ) by {
                reveal(Map::remove_keys);
            };
            assert(
                lctx.page_lock_map().spec_index(page_index)
                    == old(lctx).page_lock_map().spec_index(page_index)
            ) by {
                reveal(Map::remove_keys);
            };
            assert(
                krnl.pg_arr.spec_index(page_index).view()
                    == old(krnl).pg_arr.spec_index(page_index).view()
            ) by {
                reveal(held_pages_unchanged_except);
            };
        };
        assert forall|page_ptr: PagePtr|
            #![trigger page_ptrs.to_set().contains(page_ptr)]
            page_ptrs.to_set().contains(page_ptr) implies {
                &&& krnl.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().free_list == 0
                &&& krnl.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_ptr),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& krnl.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == child_container_ptr
                &&& !krnl.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().locked_by_thread(lctx.thread_id())
            } by {
            page_ptrs.to_set_ensures();
            reveal(Seq::contains);
            let i = choose|i: int|
                0 <= i < page_ptrs.len()
                    && page_ptrs.spec_index(i) == page_ptr;
            page_ptr_valid_imply_page_index_valid();
            assert(
                krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().free_list == 0
            );
            assert(
                krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
            );
            assert(
                krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().owning_container == child_container_ptr
            );
            assert(
                !lctx.page_lock_map().dom().contains(
                    page_ptr2page_index(page_ptr),
                )
            );
            assert(
                !krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().locked_by_thread(lctx.thread_id())
            ) by {
                reveal(LockedArray::typed_lock_map_aligned);
            };
        };
        assert(
            kernel_k_to_kernel_u(*krnl)
                == kernel_k_to_kernel_u(*old(krnl))
        ) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                old(krnl),
                krnl,
            );
        };
    }
}

#[verifier::spinoff_prover]
pub(super) fn allocate_staged_4k_page_chain(
    krnl: &mut KernelK,
    count: usize,
    thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (
    PagePtr,
    Ghost<Seq<PagePtr>>,
    Tracked<Map<PagePtr, LockPerm>>,
))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr)
            .view().owning_container == container_ptr,
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr)
            .wlocked_by(old(lctx)),
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
        final(krnl).inv(),
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
        final(krnl).thr_mp.spec_index(thread_ptr)
            .wlocked_by(final(lctx)),
        thread_lock_perm.lock_id()
            == final(krnl).thr_mp.spec_index(thread_ptr)
                .locking_thread()->Write_lock_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom().union(
                page_ptrs_to_indices(ret.1@),
            ),
        page_ptrs_to_indices(ret.1@).disjoint(
            old(lctx).page_lock_map().dom(),
        ),
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
        assert(
            krnl.thr_mp.spec_index(thread_ptr)
                .view().temp_alloc_cache_4k.view()
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .view().temp_alloc_cache_4k.view()
        );
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
            krnl.inv(),
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
            krnl.thr_mp.spec_index(thread_ptr)
                .wlocked_by(lctx),
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
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom().union(
                    page_ptrs_to_indices(page_ptrs),
                ),
            page_ptrs_to_indices(page_ptrs).disjoint(
                old(lctx).page_lock_map().dom(),
            ),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map()
                == old(lctx).pcid_allocator_lock_map(),
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
        proof {
            assert(staged_4k_page_chain(
                pages_before_allocate,
                page_ptrs,
            ));
            assert forall|j: int|
                #![trigger page_ptr_valid(page_ptrs.spec_index(j))]
                0 <= j < page_ptrs.len() implies {
                    &&& page_ptr_valid(page_ptrs.spec_index(j))
                    &&& lctx_before_allocate.page_lock_map().dom()
                        .contains(page_ptr2page_index(
                            page_ptrs.spec_index(j),
                        ))
                } by {
                assert(page_ptrs.to_set().contains(
                    page_ptrs.spec_index(j),
                )) by {
                    page_ptrs.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(page_lock_perms.dom().contains(
                    page_ptrs.spec_index(j),
                ));
                reveal(allocated_4k_page_lock_perms_wf);
            };
        }
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
            assert(!page_ptrs.contains(page_ptr)) by {
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
                reveal(staged_4k_page_chain);
                reveal(held_pages_unchanged);
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
        let ghost pages_before_link = krnl.pg_arr;
        proof {
            assert(staged_4k_page_chain(
                pages_before_link,
                page_ptrs,
            ));
        }
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
                page_ptrs.push(page_ptr),
            )) by {
                assert forall|j: int|
                    #![trigger krnl.pg_arr.spec_index(
                        page_ptr2page_index(
                            page_ptrs.push(page_ptr).spec_index(j),
                        ),
                    ).view().view().free_list]
                    0 <= j < page_ptrs.push(page_ptr).len()
                    implies {
                        &&& page_ptr_valid(
                            page_ptrs.push(page_ptr).spec_index(j),
                        )
                        &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                            page_ptrs.push(page_ptr).spec_index(j),
                        )).view().view().free_list
                            == if j == 0 {
                                STAGED_4K_PAGE_CHAIN_END
                            } else {
                                page_ptrs.push(page_ptr)
                                    .spec_index(j - 1)
                            }
                } by {
                    seq_push_lemma::<PagePtr>();
                    if j == page_ptrs.len() {
                        assert(
                            page_ptrs.push(page_ptr).spec_index(j)
                                == page_ptr
                        );
                        if page_ptrs.len() == 0 {
                        } else {
                            assert(
                                page_ptrs.push(page_ptr)
                                    .spec_index(j - 1)
                                    == page_ptrs.last()
                            );
                        }
                    } else {
                        assert(
                            page_ptrs.push(page_ptr).spec_index(j)
                                == page_ptrs.spec_index(j)
                        );
                        assert(page_ptr_valid(page_ptrs.spec_index(j)))
                            by {
                            reveal(staged_4k_page_chain);
                        };
                        assert(page_ptrs.spec_index(j) != page_ptr) by {
                            if page_ptrs.spec_index(j) == page_ptr {
                                assert(page_ptrs.contains(page_ptr)) by {
                                    reveal(Seq::contains);
                                };
                            }
                        };
                        assert(
                            page_ptr2page_index(
                                page_ptrs.spec_index(j),
                            ) != page_ptr2page_index(page_ptr)
                        ) by {
                            page_ptr2page_index_injective();
                        };
                        assert(
                            krnl.pg_arr.spec_index(page_ptr2page_index(
                                page_ptrs.spec_index(j),
                            )).view()
                                == pages_before_link.spec_index(
                                    page_ptr2page_index(
                                        page_ptrs.spec_index(j),
                                    ),
                                ).view()
                        ) by {
                            reveal(LockedArray::entries_unchanged_except);
                        };
                        reveal(staged_4k_page_chain);
                    }
                };
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

use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn prove_new_container_bootstrap_pages_disjoint_from_2m_regions(
    krnl: &KernelK,
    lctx: &LocalContext,
    pages_4k: &ArrayVec<PagePtr, 9>,
    page_4k_lock_perms: Map<PagePtr, LockPerm>,
    current_thread_ptr: RwLockThreadPtr,
    parent_container_ptr: RwLockContainerPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
)
    requires
        krnl.inv(),
        pages_4k.wf(),
        page_4k_lock_perms.dom() == pages_4k.view().to_set(),
        allocated_4k_page_lock_perms_wf(
            page_4k_lock_perms,
            krnl,
            lctx,
            current_thread_ptr,
            parent_container_ptr,
        ),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        krnl.pg_arr.spec_index(page_ptr2page_index(container_page))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
    ensures
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(container_page)),
        ),
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
{
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(container_page)),
        )
    ) by {
        let page_ptrs = pages_4k.view().to_set();
        let region = page_2m_all_ptrs(page_ptr2page_index(container_page));
        assert(page_ptrs.intersect(region) =~= Set::<PagePtr>::empty()) by {
            assert_sets_equal!(page_ptrs.intersect(region) == Set::<PagePtr>::empty(), page_ptr => {
                if page_ptrs.contains(page_ptr) && region.contains(page_ptr) {
                    assert(page_4k_lock_perms.dom().contains(page_ptr)) by {
                        pages_4k.view().to_set_ensures();
                    };
                    assert({
                        &&& page_ptr_valid(page_ptr)
                        &&& krnl.pg_arr.spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().state is Owned4k
                    }) by {
                        reveal(allocated_4k_page_lock_perms_wf);
                    };
                    owned_4k_page_not_in_2m_region(
                        krnl,
                        page_ptr,
                        page_ptr2page_index(container_page),
                    );
                }
            });
        };
        vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(
            page_ptrs,
            region,
        );
    };
    assert(
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        )
    ) by {
        let page_ptrs = pages_4k.view().to_set();
        let region = page_2m_all_ptrs(
            page_ptr2page_index(pcid_allocator_page),
        );
        assert(page_ptrs.intersect(region) =~= Set::<PagePtr>::empty()) by {
            assert_sets_equal!(page_ptrs.intersect(region) == Set::<PagePtr>::empty(), page_ptr => {
                if page_ptrs.contains(page_ptr) && region.contains(page_ptr) {
                    assert(page_4k_lock_perms.dom().contains(page_ptr)) by {
                        pages_4k.view().to_set_ensures();
                    };
                    assert({
                        &&& page_ptr_valid(page_ptr)
                        &&& krnl.pg_arr.spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().state is Owned4k
                    }) by {
                        reveal(allocated_4k_page_lock_perms_wf);
                    };
                    owned_4k_page_not_in_2m_region(
                        krnl,
                        page_ptr,
                        page_ptr2page_index(pcid_allocator_page),
                    );
                }
            });
        };
        vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(
            page_ptrs,
            region,
        );
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn prove_new_container_funding_pages_disjoint_from_moved_pages(
    krnl: &KernelK,
    lctx: &LocalContext,
    pages_4k: &ArrayVec<PagePtr, 9>,
    funding_pages: Seq<PagePtr>,
    funding_page_lock_perms: Map<PagePtr, LockPerm>,
    current_thread_ptr: RwLockThreadPtr,
    parent_container_ptr: RwLockContainerPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
)
    requires
        krnl.inv(),
        pages_4k.wf(),
        pages_4k.len() == 9,
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        allocated_4k_page_lock_perms_wf(funding_page_lock_perms, krnl, lctx, current_thread_ptr, parent_container_ptr),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        krnl.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
    ensures
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1),
            pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(8),
            pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6),
        )),
{
    let allocator_4k_page = pages_4k.view().spec_index(0);
    let allocator_2m_page = pages_4k.view().spec_index(1);
    let allocator_1g_page = pages_4k.view().spec_index(2);
    let child_scheduler_ptr = pages_4k.view().spec_index(3);
    let cpu_set_page = pages_4k.view().spec_index(8);
    let child_process_ptr = pages_4k.view().spec_index(4);
    let child_pagetable_ptr = pages_4k.view().spec_index(5);
    let l4_page = pages_4k.view().spec_index(6);
    let funding_page_set = funding_pages.to_set();
    let moved_pages = new_container_moved_pages(
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        child_scheduler_ptr,
        cpu_set_page,
        child_process_ptr,
        child_pagetable_ptr,
        l4_page,
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(funding_page_set.intersect(moved_pages) =~= Set::<PagePtr>::empty()) by {
        assert_sets_equal!(funding_page_set.intersect(moved_pages) == Set::<PagePtr>::empty(), page_ptr => {
            if funding_page_set.contains(page_ptr) && moved_pages.contains(page_ptr) {
                assert({
                    &&& page_ptr_valid(page_ptr)
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
                }) by {
                    assert(funding_page_lock_perms.dom().contains(page_ptr)) by {
                        funding_pages.to_set_ensures();
                    };
                    reveal(allocated_4k_page_lock_perms_wf);
                };
                owned_4k_page_not_in_2m_region(krnl, page_ptr, page_ptr2page_index(container_page));
                owned_4k_page_not_in_2m_region(krnl, page_ptr, page_ptr2page_index(pcid_allocator_page));
                if new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, child_scheduler_ptr, cpu_set_page, child_process_ptr, child_pagetable_ptr, l4_page).contains(page_ptr) {
                    assert(pages_4k.view().to_set().contains(page_ptr)) by {
                        reveal(new_container_bootstrap_4k_pages);
                        pages_4k.view().to_set_ensures();
                    };
                    reveal(Set::disjoint);
                }
                reveal(new_container_moved_pages);
            }
        });
    };
    vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(funding_page_set, moved_pages);
}

#[verifier::spinoff_prover]
pub(super) proof fn prove_new_container_locked_4k_pages_disjoint_from_2m_tails(
    krnl: &KernelK,
    lctx: &LocalContext,
    pages_4k: &ArrayVec<PagePtr, 9>,
    funding_pages: Seq<PagePtr>,
    page_4k_lock_perms: Map<PagePtr, LockPerm>,
    funding_page_lock_perms: Map<PagePtr, LockPerm>,
    current_thread_ptr: RwLockThreadPtr,
    parent_container_ptr: RwLockContainerPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
)
    requires
        krnl.inv(),
        pages_4k.wf(),
        page_4k_lock_perms.dom() == pages_4k.view().to_set(),
        allocated_4k_page_lock_perms_wf(
            page_4k_lock_perms,
            krnl,
            lctx,
            current_thread_ptr,
            parent_container_ptr,
        ),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        allocated_4k_page_lock_perms_wf(
            funding_page_lock_perms,
            krnl,
            lctx,
            current_thread_ptr,
            parent_container_ptr,
        ),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        krnl.pg_arr.spec_index(page_ptr2page_index(container_page))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        lctx.page_lock_map().dom()
            == page_ptrs_to_indices(pages_4k.view())
                .union(page_ptrs_to_indices(funding_pages))
                .union(seq![
                    page_ptr2page_index(container_page),
                    page_ptr2page_index(pcid_allocator_page),
                ].to_set()),
    ensures
        lctx.page_lock_map().dom().disjoint(
            page_2m_tail_indices(page_ptr2page_index(container_page))
                .union(page_2m_tail_indices(
                    page_ptr2page_index(pcid_allocator_page),
                )),
        ),
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let page_tails = page_2m_tail_indices(container_head).union(
        page_2m_tail_indices(pcid_allocator_head),
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(
        page_ptrs_to_indices(pages_4k.view())
            .union(page_ptrs_to_indices(funding_pages))
            .disjoint(page_tails)
    ) by {
        let locked_indices = page_ptrs_to_indices(pages_4k.view())
            .union(page_ptrs_to_indices(funding_pages));
        assert(locked_indices.intersect(page_tails)
            =~= Set::<PageIndex>::empty()) by {
            assert_sets_equal!(
                locked_indices.intersect(page_tails)
                    == Set::<PageIndex>::empty(),
                page_index => {
                    if locked_indices.contains(page_index)
                        && page_tails.contains(page_index)
                    {
                        reveal(page_ptrs_to_indices);
                        let pages_indices = pages_4k.view().map_values(
                            |page_ptr: PagePtr| {
                                page_ptr2page_index(page_ptr)
                            },
                        );
                        let funding_indices = funding_pages.map_values(
                            |page_ptr: PagePtr| {
                                page_ptr2page_index(page_ptr)
                            },
                        );
                        let page_ptr = if pages_indices.to_set()
                            .contains(page_index)
                        {
                            pages_indices.to_set_ensures();
                            assert(pages_indices.contains(page_index));
                            pages_indices.index_of_first_ensures(page_index);
                            let i = pages_indices
                                .index_of_first(page_index).unwrap();
                            assert(0 <= i < pages_4k.view().len()) by {
                                reveal(Seq::map_values);
                            };
                            assert(
                                pages_4k.view().to_set().contains(
                                    pages_4k.view().spec_index(i),
                                )
                            ) by {
                                pages_4k.view().to_set_ensures();
                                assert(pages_4k.view().contains(
                                    pages_4k.view().spec_index(i),
                                ));
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
                                funding_indices.to_set()
                                    .contains(page_index)
                            ) by {
                                reveal(Set::contains);
                            };
                            funding_indices.to_set_ensures();
                            assert(funding_indices.contains(page_index));
                            funding_indices
                                .index_of_first_ensures(page_index);
                            let i = funding_indices
                                .index_of_first(page_index).unwrap();
                            assert(0 <= i < funding_pages.len()) by {
                                reveal(Seq::map_values);
                            };
                            assert(
                                funding_pages.to_set().contains(
                                    funding_pages.spec_index(i),
                                )
                            ) by {
                                funding_pages.to_set_ensures();
                                assert(funding_pages.contains(
                                    funding_pages.spec_index(i),
                                ));
                            };
                            assert(
                                page_ptr2page_index(
                                    funding_pages.spec_index(i),
                                ) == page_index
                            ) by {
                                reveal(Seq::map_values);
                            };
                            funding_pages.spec_index(i)
                        };
                        assert({
                            &&& page_ptr_valid(page_ptr)
                            &&& krnl.pg_arr.spec_index(
                                page_ptr2page_index(page_ptr),
                            ).view().view().state is Owned4k
                        }) by {
                            if pages_4k.view().to_set()
                                .contains(page_ptr)
                            {
                                assert(
                                    page_4k_lock_perms.dom()
                                        .contains(page_ptr)
                                );
                            } else {
                                assert(
                                    funding_pages.to_set()
                                        .contains(page_ptr)
                                ) by {
                                    reveal(Set::contains);
                                };
                                assert(
                                    funding_page_lock_perms.dom()
                                        .contains(page_ptr)
                                );
                            }
                            reveal(allocated_4k_page_lock_perms_wf);
                        };
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
                }
            );
        };
        vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(
            locked_indices,
            page_tails,
        );
    };
    assert({
        &&& !page_tails.contains(container_head)
        &&& !page_tails.contains(pcid_allocator_head)
    }) by {
        reveal(page_2m_tail_indices);
        reveal(Set::contains);
    };
    assert(lctx.page_lock_map().dom().disjoint(page_tails)) by {
        reveal(Set::disjoint);
    };
}


}

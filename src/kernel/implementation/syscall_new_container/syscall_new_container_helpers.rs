use vstd::{assert_maps_equal, assert_sets_equal};
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn new_container_page_positions(pages: Seq<PagePtr>)
    requires
        pages.len() == 9,
        pages.no_duplicates(),
    ensures
        pages.spec_index(1) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(0),
        pages.spec_index(3) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(0),
        pages.spec_index(8) != pages.spec_index(1),
        pages.spec_index(8) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(0),
        pages.spec_index(4) != pages.spec_index(1),
        pages.spec_index(4) != pages.spec_index(2),
        pages.spec_index(4) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(0),
        pages.spec_index(5) != pages.spec_index(1),
        pages.spec_index(5) != pages.spec_index(2),
        pages.spec_index(5) != pages.spec_index(3),
        pages.spec_index(5) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(0),
        pages.spec_index(6) != pages.spec_index(1),
        pages.spec_index(6) != pages.spec_index(2),
        pages.spec_index(6) != pages.spec_index(3),
        pages.spec_index(6) != pages.spec_index(8),
        pages.spec_index(6) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(0),
        pages.spec_index(7) != pages.spec_index(1),
        pages.spec_index(7) != pages.spec_index(2),
        pages.spec_index(7) != pages.spec_index(3),
        pages.spec_index(7) != pages.spec_index(8),
        pages.spec_index(7) != pages.spec_index(4),
        pages.spec_index(7) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(6),
        pages.to_set().contains(pages.spec_index(0)),
        pages.to_set().contains(pages.spec_index(1)),
        pages.to_set().contains(pages.spec_index(2)),
        pages.to_set().contains(pages.spec_index(3)),
        pages.to_set().contains(pages.spec_index(4)),
        pages.to_set().contains(pages.spec_index(5)),
        pages.to_set().contains(pages.spec_index(6)),
        pages.to_set().contains(pages.spec_index(7)),
        pages.to_set().contains(pages.spec_index(8)),
        pages.spec_index(1) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(0),
        pages.spec_index(2) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(0),
        pages.spec_index(3) != pages.spec_index(1),
        pages.spec_index(3) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(0),
        pages.spec_index(8) != pages.spec_index(1),
        pages.spec_index(8) != pages.spec_index(2),
        pages.spec_index(8) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(0),
        pages.spec_index(4) != pages.spec_index(1),
        pages.spec_index(4) != pages.spec_index(2),
        pages.spec_index(4) != pages.spec_index(3),
        pages.spec_index(4) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(0),
        pages.spec_index(5) != pages.spec_index(1),
        pages.spec_index(5) != pages.spec_index(2),
        pages.spec_index(5) != pages.spec_index(3),
        pages.spec_index(5) != pages.spec_index(8),
        pages.spec_index(5) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(0),
        pages.spec_index(6) != pages.spec_index(1),
        pages.spec_index(6) != pages.spec_index(2),
        pages.spec_index(6) != pages.spec_index(3),
        pages.spec_index(6) != pages.spec_index(8),
        pages.spec_index(6) != pages.spec_index(4),
        pages.spec_index(6) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(0),
        pages.spec_index(7) != pages.spec_index(1),
        pages.spec_index(7) != pages.spec_index(2),
        pages.spec_index(7) != pages.spec_index(3),
        pages.spec_index(7) != pages.spec_index(8),
        pages.spec_index(7) != pages.spec_index(4),
        pages.spec_index(7) != pages.spec_index(5),
        pages.spec_index(7) != pages.spec_index(6),
        new_container_bootstrap_4k_pages(
            pages.spec_index(0), pages.spec_index(1), pages.spec_index(2), pages.spec_index(3), pages.spec_index(8), pages.spec_index(4),
            pages.spec_index(5), pages.spec_index(6),
        ).len() == 8,
        !new_container_bootstrap_4k_pages(
            pages.spec_index(0), pages.spec_index(1), pages.spec_index(2), pages.spec_index(3), pages.spec_index(8), pages.spec_index(4),
            pages.spec_index(5), pages.spec_index(6),
        ).contains(pages.spec_index(7)),
        pages.to_set()
            == new_container_bootstrap_4k_pages(
                pages.spec_index(0), pages.spec_index(1), pages.spec_index(2), pages.spec_index(3), pages.spec_index(8),
                pages.spec_index(4), pages.spec_index(5), pages.spec_index(6),
            ).union(seq![pages.spec_index(7)].to_set()),
        pages.to_set()
            == new_container_bootstrap_4k_pages(
                pages.spec_index(0), pages.spec_index(1), pages.spec_index(2), pages.spec_index(3), pages.spec_index(8),
                pages.spec_index(4), pages.spec_index(5), pages.spec_index(6),
            ).insert(pages.spec_index(7)),
{
    pages.to_set_ensures();
    let bootstrap_pages = new_container_bootstrap_4k_pages(
        pages.spec_index(0), pages.spec_index(1), pages.spec_index(2), pages.spec_index(3), pages.spec_index(8), pages.spec_index(4),
        pages.spec_index(5), pages.spec_index(6),
    );
    let bootstrap_seq = seq![
        pages.spec_index(0),
        pages.spec_index(1),
        pages.spec_index(2),
        pages.spec_index(3),
        pages.spec_index(8),
        pages.spec_index(4),
        pages.spec_index(5),
        pages.spec_index(6),
    ];
    bootstrap_seq.unique_seq_to_set();
    assert(bootstrap_pages == bootstrap_seq.to_set()) by { reveal(new_container_bootstrap_4k_pages); };
    assert(bootstrap_pages.len() == 8) by { bootstrap_seq.unique_seq_to_set(); };
    assert(!bootstrap_pages.contains(pages.spec_index(7)));
    assert(
        pages.to_set()
            == bootstrap_pages.union(seq![pages.spec_index(7)].to_set())
    ) by {
        let thread_seq = seq![pages.spec_index(7)];
        let thread_pages = thread_seq.to_set();
        bootstrap_seq.to_set_ensures();
        thread_seq.to_set_ensures();
        assert_sets_equal!(
            pages.to_set() == bootstrap_pages.union(thread_pages),
            page_ptr => {
                if pages.to_set().contains(page_ptr) {
                    assert(pages.contains(page_ptr)) by { pages.to_set_ensures(); };
                    pages.index_of_first_ensures(page_ptr);
                    let i = pages.index_of_first(page_ptr).unwrap();
                    assert(
                        i == 0 || i == 1 || i == 2
                            || i == 3 || i == 4 || i == 5
                            || i == 6 || i == 7 || i == 8
                    ) by {
                        pages.index_of_first_ensures(page_ptr);
                    };
                    if i == 7 {
                        assert(page_ptr == pages.spec_index(7)) by { pages.index_of_first_ensures(page_ptr); };
                        thread_seq.lemma_index_contains(0);
                    } else {
                        assert(bootstrap_seq.contains(page_ptr)) by {
                            if i == 0 {
                                assert(bootstrap_seq.spec_index(0) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else if i == 1 {
                                assert(bootstrap_seq.spec_index(1) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else if i == 2 {
                                assert(bootstrap_seq.spec_index(2) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else if i == 3 {
                                assert(bootstrap_seq.spec_index(3) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else if i == 4 {
                                assert(bootstrap_seq.spec_index(5) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else if i == 5 {
                                assert(bootstrap_seq.spec_index(6) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else if i == 6 {
                                assert(bootstrap_seq.spec_index(7) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            } else {
                                assert(bootstrap_seq.spec_index(4) == page_ptr) by { pages.index_of_first_ensures(page_ptr); };
                            }
                        };
                    }
                }
                if bootstrap_pages.union(thread_pages).contains(page_ptr) {
                    if bootstrap_pages.contains(page_ptr) {
                        assert(bootstrap_seq.contains(page_ptr)) by { bootstrap_seq.to_set_ensures(); };
                        bootstrap_seq.index_of_first_ensures(page_ptr);
                        let i = bootstrap_seq
                            .index_of_first(page_ptr).unwrap();
                        assert(
                            i == 0 || i == 1 || i == 2 || i == 3
                                || i == 4 || i == 5 || i == 6 || i == 7
                        ) by {
                            bootstrap_seq.index_of_first_ensures(page_ptr);
                        };
                        if i == 0 {
                            assert(page_ptr == pages.spec_index(0)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else if i == 1 {
                            assert(page_ptr == pages.spec_index(1)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else if i == 2 {
                            assert(page_ptr == pages.spec_index(2)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else if i == 3 {
                            assert(page_ptr == pages.spec_index(3)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else if i == 4 {
                            assert(page_ptr == pages.spec_index(8)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else if i == 5 {
                            assert(page_ptr == pages.spec_index(4)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else if i == 6 {
                            assert(page_ptr == pages.spec_index(5)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        } else {
                            assert(page_ptr == pages.spec_index(6)) by { bootstrap_seq.index_of_first_ensures(page_ptr); };
                        }
                        assert(pages.to_set().contains(page_ptr)) by { pages.to_set_ensures(); };
                    } else {
                        assert(thread_seq.contains(page_ptr)) by { thread_seq.to_set_ensures(); };
                        assert(pages.to_set().contains(page_ptr)) by { pages.to_set_ensures(); };
                    }
                }
            }
        );
    };
    assert(pages.to_set() == bootstrap_pages.insert(pages.spec_index(7))) by {
        let thread_seq = seq![pages.spec_index(7)];
        thread_seq.to_set_ensures();
        assert_sets_equal!(
            pages.to_set() == bootstrap_pages.insert(pages.spec_index(7)),
            page_ptr => {
            }
        );
    };
}

pub(super) proof fn new_container_staged_pages_disjoint(
    krnl: &KernelK, lctx: &LocalContext, pages_4k: &ArrayVec<PagePtr, 9>, funding_pages: Seq<PagePtr>,
    page_4k_lock_perms: Map<PagePtr, LockPerm>, funding_page_lock_perms: Map<PagePtr, LockPerm>, current_thread_ptr: RwLockThreadPtr,
    parent_container_ptr: RwLockContainerPtr, container_page: PagePtr, pcid_allocator_page: PagePtr,
)
    requires
        krnl.inv(),
        pages_4k.wf(),
        pages_4k.len() == 9,
        page_4k_lock_perms.dom() == pages_4k.view().to_set(),
        allocated_4k_page_lock_perms_wf(page_4k_lock_perms, krnl, lctx, current_thread_ptr, parent_container_ptr),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        allocated_4k_page_lock_perms_wf(funding_page_lock_perms, krnl, lctx, current_thread_ptr, parent_container_ptr),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        krnl.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        lctx.page_lock_map().dom() == page_ptrs_to_indices(pages_4k.view()).union(page_ptrs_to_indices(funding_pages)).union(seq![page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)].to_set()),
    ensures
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(container_page)),
        ),
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1),
            pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(8),
            pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6),
        )),
        lctx.page_lock_map().dom().disjoint(
            page_2m_tail_indices(page_ptr2page_index(container_page))
                .union(page_2m_tail_indices(
                    page_ptr2page_index(pcid_allocator_page),
                )),
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
                    assert(page_4k_lock_perms.dom().contains(page_ptr)) by { pages_4k.view().to_set_ensures(); };
                    assert({
                        &&& page_ptr_valid(page_ptr)
                        &&& krnl.pg_arr.spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().state is Owned4k
                    });
                    owned_4k_page_not_in_2m_region(krnl, page_ptr, page_ptr2page_index(container_page));
                }
            });
        };
        vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(page_ptrs, region);
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
                    assert(page_4k_lock_perms.dom().contains(page_ptr)) by { pages_4k.view().to_set_ensures(); };
                    assert({
                        &&& page_ptr_valid(page_ptr)
                        &&& krnl.pg_arr.spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().state is Owned4k
                    });
                    owned_4k_page_not_in_2m_region(krnl, page_ptr, page_ptr2page_index(pcid_allocator_page));
                }
            });
        };
        vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(page_ptrs, region);
    };
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
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, child_scheduler_ptr, cpu_set_page,
        child_process_ptr, child_pagetable_ptr, l4_page,
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
                    assert(funding_page_lock_perms.dom().contains(page_ptr)) by { funding_pages.to_set_ensures(); };
                };
                owned_4k_page_not_in_2m_region(krnl, page_ptr, page_ptr2page_index(container_page));
                owned_4k_page_not_in_2m_region(krnl, page_ptr, page_ptr2page_index(pcid_allocator_page));
                if new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, child_scheduler_ptr, cpu_set_page, child_process_ptr, child_pagetable_ptr, l4_page).contains(page_ptr) {
                    assert(pages_4k.view().to_set().contains(page_ptr)) by {
                        reveal(new_container_bootstrap_4k_pages);
                        pages_4k.view().to_set_ensures();
                    };
                }
                reveal(new_container_moved_pages);
            }
        });
    };
    vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(funding_page_set, moved_pages);
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
                            pages_indices.index_of_first_ensures(page_index);
                            let i = pages_indices
                                .index_of_first(page_index).unwrap();
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
                            );
                            pages_4k.view().spec_index(i)
                        } else {
                            assert(
                                funding_indices.to_set()
                                    .contains(page_index)
                            );
                            funding_indices.to_set_ensures();
                            funding_indices
                                .index_of_first_ensures(page_index);
                            let i = funding_indices
                                .index_of_first(page_index).unwrap();
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
                            );
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
                                );
                                assert(
                                    funding_page_lock_perms.dom()
                                        .contains(page_ptr)
                                );
                            }
                        };
                        owned_4k_page_not_in_2m_tail(krnl, page_ptr, container_head);
                        owned_4k_page_not_in_2m_tail(krnl, page_ptr, pcid_allocator_head);
                    }
                }
            );
        };
        vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(locked_indices, page_tails);
    };
    assert({
        &&& !page_tails.contains(container_head)
        &&& !page_tails.contains(pcid_allocator_head)
    });
}

#[verifier::spinoff_prover]
pub(super) fn wlock_new_container_2m_page_tails(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, left: PageIndex, right: PageIndex,
) -> (ret: (Tracked<Map<PageIndex, LockPerm>>, Tracked<Map<PageIndex, LockPerm>>))
    requires
        old(krnl).inv(),
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
        old(krnl).pg_arr.spec_index(left).view().view().state is Owned2m,
        old(krnl).pg_arr.spec_index(right).view().view().state is Owned2m,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().disjoint(page_2m_tail_indices(left).union(page_2m_tail_indices(right))),
        old(lctx).lock_id_acyclic(merged_page_lock_id((left + 1) as usize)),
        old(lctx).lock_id_acyclic(merged_page_lock_id((right + 1) as usize)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().remove_keys(page_2m_tail_indices(left).union(page_2m_tail_indices(right))) == old(lctx).page_lock_map(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_2m_tail_indices(left)).union(page_2m_tail_indices(right)),
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(left).union(page_2m_tail_indices(right)).contains(index)
                ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view() == old(krnl).pg_arr.spec_index(index).view().view(),
        owned_2m_tail_lock_perms_wf(ret.0.view(), final(krnl).pg_arr, final(lctx), left),
        owned_2m_tail_lock_perms_wf(ret.1.view(), final(krnl).pg_arr, final(lctx), right),
{
    let (Tracked(left_perms), Tracked(right_perms)) = if left < right {
        let Tracked(left_perms) = wlock_owned_2m_page_tails(krnl, left, Tracked(&mut *lctx));
        let Tracked(right_perms) = wlock_owned_2m_page_tails(krnl, right, Tracked(&mut *lctx));
        (Tracked(left_perms), Tracked(right_perms))
    } else {
        let Tracked(right_perms) = wlock_owned_2m_page_tails(krnl, right, Tracked(&mut *lctx));
        let Tracked(left_perms) = wlock_owned_2m_page_tails(krnl, left, Tracked(&mut *lctx));
        (Tracked(left_perms), Tracked(right_perms))
    };
    proof {
        assert(lctx.page_lock_map().remove_keys(page_2m_tail_indices(left).union(page_2m_tail_indices(right))) == old(lctx).page_lock_map()) by {
            assert_maps_equal!(
                lctx.page_lock_map().remove_keys(page_2m_tail_indices(left).union(page_2m_tail_indices(right))),
                old(lctx).page_lock_map(),
                index => {}
            );
        };
    }
    (Tracked(left_perms), Tracked(right_perms))
}
}

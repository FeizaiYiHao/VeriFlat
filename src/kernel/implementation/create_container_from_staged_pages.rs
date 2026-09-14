use vstd::prelude::*;
use crate::*;
use crate::kernel::implementation::lock_owned_2m_page_tails::{
    distinct_2m_heads_have_disjoint_tails,
    non_merged_page_not_in_owned_2m_tails,
    set_owned_2m_page_tails_container,
};

verus! {
pub const STAGED_4K_PAGE_CHAIN_END: PagePtr = usize::MAX;

pub open spec fn staged_4k_page_chain(pages: PageLockedArray, page_ptrs: Seq<PagePtr>) -> bool {
    forall|i: int|
        #![trigger pages.spec_index(
            page_ptr2page_index(page_ptrs.spec_index(i)),
        ).view().view().free_list]
        0 <= i < page_ptrs.len() ==> {
            &&& page_ptr_valid(page_ptrs.spec_index(i))
            &&& pages.spec_index(page_ptr2page_index(
                page_ptrs.spec_index(i),
            )).view().view().free_list
                == if i == 0 {
                    STAGED_4K_PAGE_CHAIN_END
                } else {
                    page_ptrs.spec_index(i - 1)
                }
        }
}

pub open spec fn staged_4k_page_chain_head(page_ptrs: Seq<PagePtr>) -> PagePtr {
    if page_ptrs.len() == 0 {
        STAGED_4K_PAGE_CHAIN_END
    } else {
        page_ptrs.last()
    }
}

#[verifier::spinoff_prover]
fn build_staged_4k_global_pool(
    pages: &mut PageLockedArray,
    count: usize,
    head: PagePtr,
    Ghost(page_ptrs): Ghost<Seq<PagePtr>>,
    child_allocator_ptr: RwLockPageAllocatorPtr,
    child_container_ptr: RwLockContainerPtr,
    child_depth: usize,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
) -> (ret: LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>)
    requires
        old(pages).inv(),
        old(pages).typed_lock_map_aligned(
            old(lctx).page_lock_map(),
            old(lctx).thread_id(),
        ),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptrs.len() == count,
        page_ptrs.no_duplicates(),
        head == staged_4k_page_chain_head(page_ptrs),
        staged_4k_page_chain(*old(pages), page_ptrs),
        page_lock_perms.dom() == page_ptrs.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& old(pages).spec_index(page_ptr2page_index(page_ptr))
                    .view().is_init()
                &&& old(pages).spec_index(page_ptr2page_index(page_ptr))
                    .view().view().inv()
                &&& old(pages).spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).state()
                    is WriteLock
                &&& page_lock_perms.spec_index(page_ptr).thread_id()
                    == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(page_ptr).lock_id()
                    == old(pages).spec_index(page_ptr2page_index(page_ptr))
                        .view().locking_thread()->Write_lock_id
            },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(pages).inv(),
        ret.wf(),
        ret.view() == page_ptrs,
        ret.view().no_duplicates(),
        ret.container_depth == Some(child_depth),
        ret.minor == Some(child_container_ptr),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom(),
        final(lctx).page_lock_map()
            .remove_keys(
                page_ptrs
                    .map_values(|page_ptr: PagePtr| {
                        page_ptr2page_index(page_ptr)
                    })
                    .to_set(),
            )
            == old(lctx).page_lock_map()
                .remove_keys(
                    page_ptrs
                        .map_values(|page_ptr: PagePtr| {
                            page_ptr2page_index(page_ptr)
                        })
                        .to_set(),
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
        final(pages).typed_lock_map_aligned(
            final(lctx).page_lock_map(),
            final(lctx).thread_id(),
        ),
        lock_id_set_aligned(final(lctx)),
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view().free_list]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr))
                    .view().view().free_list
                    == old(pages).spec_index(page_ptr2page_index(page_ptr))
                        .view().view().free_list
            },
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(
                page_ptr2page_index(page_ptr),
            )]
            page_ptr_valid(page_ptr)
                && !page_ptrs.to_set().contains(page_ptr)
            ==> final(pages).spec_index(page_ptr2page_index(page_ptr))
                == old(pages).spec_index(page_ptr2page_index(page_ptr)),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr))
                    .view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).lock_id()
                    == final(pages).spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().locking_thread()->Write_lock_id
            },
{
    let mut global_pool = LinkedList::new(
        Some(child_depth),
        Some(child_container_ptr),
    );
    let mut current = head;
    let mut remaining = count;
    proof {
        assert forall|i: int|
            #![trigger pages.spec_index(page_ptr2page_index(
                page_ptrs.spec_index(i),
            )).view().view().state]
            0 <= i < remaining implies {
                &&& page_ptr_valid(page_ptrs.spec_index(i))
                &&& pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().state is Owned4k
                &&& pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list
                    == if i == 0 {
                        STAGED_4K_PAGE_CHAIN_END
                    } else {
                        page_ptrs.spec_index(i - 1)
                    }
            } by {
            assert(page_ptrs.to_set().contains(
                page_ptrs.spec_index(i),
            )) by {
                page_ptrs.to_set_ensures();
                reveal(Seq::contains);
            };
            assert(page_lock_perms.dom().contains(
                page_ptrs.spec_index(i),
            ));
            reveal(staged_4k_page_chain);
        };
    }
    while remaining > 0
        invariant
            pages.inv(),
            pages.typed_lock_map_aligned(
                lctx.page_lock_map(),
                lctx.thread_id(),
            ),
            lock_id_set_aligned(lctx),
            lctx.kernel_view_locking_state() is Release,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom(),
            lctx.page_lock_map()
                .remove_keys(
                    page_ptrs
                        .map_values(|page_ptr: PagePtr| {
                            page_ptr2page_index(page_ptr)
                        })
                        .to_set(),
                )
                == old(lctx).page_lock_map()
                    .remove_keys(
                        page_ptrs
                            .map_values(|page_ptr: PagePtr| {
                                page_ptr2page_index(page_ptr)
                            })
                            .to_set(),
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
            forall|page_ptr: PagePtr|
                #![trigger pages.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().free_list]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& pages.spec_index(page_ptr2page_index(page_ptr))
                        .view().view().free_list
                        == old(pages).spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().free_list
                },
            forall|page_ptr: PagePtr|
                #![trigger pages.spec_index(
                    page_ptr2page_index(page_ptr),
                )]
                page_ptr_valid(page_ptr)
                    && !page_ptrs.to_set().contains(page_ptr)
                ==> pages.spec_index(page_ptr2page_index(page_ptr))
                    == old(pages).spec_index(
                        page_ptr2page_index(page_ptr),
                    ),
            page_ptrs.len() == count,
            page_ptrs.no_duplicates(),
            page_lock_perms.dom() == page_ptrs.to_set(),
            0 <= remaining <= count,
            current == if remaining == 0 {
                STAGED_4K_PAGE_CHAIN_END
            } else {
                page_ptrs.spec_index(remaining - 1)
            },
            global_pool.wf(),
            global_pool.view()
                == page_ptrs.subrange(remaining as int, count as int),
            global_pool.length == count - remaining,
            global_pool.container_depth == Some(child_depth),
            global_pool.minor == Some(child_container_ptr),
            forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().state]
                0 <= i < remaining ==> {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().state is Owned4k
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list
                        == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                },
            forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().state]
                remaining <= i < count ==> {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().owning_container
                        == child_container_ptr
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list
                        == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                },
            forall|page_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(page_ptr)]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& pages.spec_index(page_ptr2page_index(page_ptr))
                        .view().is_init()
                    &&& pages.spec_index(page_ptr2page_index(page_ptr))
                        .view().view().inv()
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                    &&& page_lock_perms.spec_index(page_ptr).state()
                        is WriteLock
                    &&& page_lock_perms.spec_index(page_ptr).thread_id()
                        == lctx.thread_id()
                    &&& page_lock_perms.spec_index(page_ptr).lock_id()
                        == pages.spec_index(page_ptr2page_index(page_ptr))
                            .view().locking_thread()->Write_lock_id
                },
        decreases remaining,
    {
        let page_ptr = current;
        proof {
            assert(page_ptrs.to_set().contains(page_ptr)) by {
                page_ptrs.to_set_ensures();
                reveal(Seq::contains);
            };
            page_ptr_valid_imply_page_index_valid();
        }
        let page_index = page_ptr2page_index(page_ptr);
        let ghost pages_before = *pages;
        let old_remaining = remaining;
        proof {
            assert(
                pages_before.spec_index(page_index)
                    .view().view().free_list
                    == old(pages).spec_index(page_index)
                        .view().view().free_list
            );
        }
        let ghost old_page_lock_id = pages.lock_id_by_index(page_index);
        let (next, node_addr, Tracked(node_perm)) = {
            let page = pages.borrow_mut_typed(
                page_index,
                Ghost(lctx.page_lock_map()),
                Tracked(&*lctx),
                Tracked(page_lock_perms.tracked_borrow(page_ptr)),
            );
            let next = page.free_list;
            let (addr, Tracked(perm)) = convert_owned_4k_to_free_global(
                page,
                child_allocator_ptr,
                child_container_ptr,
            );
            (next, addr, Tracked(perm))
        };
        proof {
            assert(pages.entries_unchanged_except(
                &pages_before,
                page_index,
            ));
            assert forall|stable_ptr: PagePtr|
                #![trigger pages.spec_index(
                    page_ptr2page_index(stable_ptr),
                )]
                page_ptr_valid(stable_ptr)
                    && !page_ptrs.to_set().contains(stable_ptr)
                implies pages.spec_index(page_ptr2page_index(stable_ptr))
                    == old(pages).spec_index(
                        page_ptr2page_index(stable_ptr),
                    ) by {
                assert(
                    page_ptr2page_index(stable_ptr) != page_index
                ) by {
                    page_ptr2page_index_injective();
                };
                assert(
                    pages.spec_index(page_ptr2page_index(stable_ptr))
                        == pages_before.spec_index(
                            page_ptr2page_index(stable_ptr),
                        )
                ) by {
                    reveal(LockedArray::entries_unchanged_except);
                };
            };
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                pages.lock_id_by_index(page_index),
            );
            let mapped_page_indices = page_ptrs.map_values(
                |mapped_page_ptr: PagePtr| {
                    page_ptr2page_index(mapped_page_ptr)
                },
            );
            assert(
                mapped_page_indices.spec_index(remaining - 1)
                    == page_index
            );
            assert(mapped_page_indices.to_set().contains(page_index)) by {
                mapped_page_indices.to_set_ensures();
            };
            assert(
                lctx.page_lock_map()
                    .remove_keys(mapped_page_indices.to_set())
                    == old(lctx).page_lock_map()
                        .remove_keys(mapped_page_indices.to_set())
            ) by {
                reveal(typed_lock_maps_inserted);
                reveal(Map::remove_keys);
            };
            assert forall|other_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(other_ptr)]
                page_lock_perms.dom().contains(other_ptr) implies {
                    &&& page_ptr_valid(other_ptr)
                    &&& pages.spec_index(page_ptr2page_index(other_ptr))
                        .view().is_init()
                    &&& pages.spec_index(page_ptr2page_index(other_ptr))
                        .view().view().inv()
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(other_ptr), TypedLockMode::Write)
                    &&& page_lock_perms.spec_index(other_ptr).state()
                        is WriteLock
                    &&& page_lock_perms.spec_index(other_ptr).thread_id()
                        == lctx.thread_id()
                    &&& page_lock_perms.spec_index(other_ptr).lock_id()
                        == pages.spec_index(page_ptr2page_index(other_ptr))
                            .view().locking_thread()->Write_lock_id
                } by {
                if other_ptr != page_ptr {
                    assert(
                        page_ptr2page_index(other_ptr) != page_index
                    ) by {
                        page_ptr2page_index_injective();
                    };
                    assert(
                        pages.spec_index(page_ptr2page_index(other_ptr))
                            == pages_before.spec_index(
                                page_ptr2page_index(other_ptr),
                            )
                    ) by {
                        reveal(LockedArray::entries_unchanged_except);
                    };
                    reveal(typed_lock_maps_inserted);
                }
            };
        }
        let mut node_perm = Tracked(node_perm);
        node_update_value(node_addr, &mut node_perm, page_ptr);
        global_pool.push_head(node_addr, node_perm);
        current = next;
        remaining = remaining - 1;
        proof {
            assert(
                global_pool.view()
                    == page_ptrs.subrange(
                        remaining as int,
                        count as int,
                    )
            ) by {
                seq_subrange_split_lemma::<PagePtr>();
            };
            assert forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().state]
                0 <= i < remaining implies {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().state is Owned4k
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list
                        == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                } by {
                assert(page_ptrs.to_set().contains(
                    page_ptrs.spec_index(i),
                )) by {
                    page_ptrs.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(page_lock_perms.dom().contains(
                    page_ptrs.spec_index(i),
                ));
                page_ptr_valid_imply_page_index_valid();
                assert(
                    page_ptr2page_index(page_ptrs.spec_index(i))
                        != page_index
                ) by {
                    page_ptr2page_index_injective();
                };
                assert(
                    pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )) == pages_before.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    ))
                ) by {
                    reveal(LockedArray::entries_unchanged_except);
                };
            };
            assert forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().state]
                remaining <= i < count implies {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().owning_container
                        == child_container_ptr
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list
                        == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                } by {
                assert(page_ptrs.to_set().contains(
                    page_ptrs.spec_index(i),
                )) by {
                    page_ptrs.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(page_lock_perms.dom().contains(
                    page_ptrs.spec_index(i),
                ));
                page_ptr_valid_imply_page_index_valid();
                if i != old_remaining - 1 {
                    assert(
                        page_ptr2page_index(page_ptrs.spec_index(i))
                            != page_index
                    ) by {
                        page_ptr2page_index_injective();
                    };
                    assert(
                        pages.spec_index(page_ptr2page_index(
                            page_ptrs.spec_index(i),
                        )) == pages_before.spec_index(
                            page_ptr2page_index(page_ptrs.spec_index(i)),
                        )
                    ) by {
                        reveal(LockedArray::entries_unchanged_except);
                    };
                }
            };
        }
    }
    proof {
        assert forall|i: int|
            #![trigger pages.spec_index(page_ptr2page_index(
                page_ptrs.spec_index(i),
            )).view().view().free_list]
            0 <= i < page_ptrs.len() implies {
                &&& page_ptr_valid(page_ptrs.spec_index(i))
                &&& pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list
                    == if i == 0 {
                        STAGED_4K_PAGE_CHAIN_END
                    } else {
                        page_ptrs.spec_index(i - 1)
                    }
            } by {
            assert(
                pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_ptr),
                    state: FreePageAllocatorState::GlobalList,
                })
            );
            assert(
                pages.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list
                    == if i == 0 {
                        STAGED_4K_PAGE_CHAIN_END
                    } else {
                        page_ptrs.spec_index(i - 1)
                    }
            );
        };
    }
    global_pool
}

pub open spec fn new_container_bootstrap_4k_pages(
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
) -> Set<PagePtr> {
    set![
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page, cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ]
}

pub open spec fn new_container_moved_pages(
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
) -> Set<PagePtr> {
    page_2m_all_ptrs(page_ptr2page_index(container_page))
        .union(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)))
        .union(new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ))
}

pub fn publish_staged_container_root(
    krnl: &mut KernelK,
    parent_container_ptr: RwLockContainerPtr,
    current_thread_ptr: RwLockThreadPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
    thread_page: PagePtr,
    funding_page_count: usize,
    funding_page_head: PagePtr,
    Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    allocator_quota_4k: usize,
    process_quota_4k: usize,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>,
    Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>,
    Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
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
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id()
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count
            <= old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k - 8,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page, cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).union(funding_pages.to_set()).insert(thread_page),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_2m.view()
            =~= set![container_page, pcid_allocator_page],
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).len() == 8,
        !new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).contains(thread_page),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page,
            pcid_allocator_page,
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        )),
        new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page))
            .disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page, cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).union(funding_pages.to_set()).subset_of(
                old(krnl).ctn_mp.spec_index(parent_container_ptr)
                    .view().owned_pages.view(),
            ),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        !old(krnl).sched_mp.dom().contains(scheduler_page),
        !old(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        !old(krnl).prc_mp.dom().contains(process_page),
        !old(krnl).pt_mp.dom().contains(pagetable_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page))
            .view().view().state
            == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        forall|page_ptr: PagePtr|
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page, cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page, cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)
            ==> old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state
                == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
            .view().view().owning_container == parent_container_ptr,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& funding_page_lock_perms.spec_index(page_ptr).state()
                    is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id()
                    == old(lctx).thread_id()
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == parent_container_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id()
                    == old(krnl).pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(
            *container_tail_lock_perms,
            old(krnl),
            old(lctx),
            page_ptr2page_index(container_page),
        ),
        owned_2m_tail_lock_perms_wf(
            *pcid_allocator_tail_lock_perms,
            old(krnl),
            old(lctx),
            page_ptr2page_index(pcid_allocator_page),
        ),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page))
                .view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).pcid_needflush == old(krnl).pcid_needflush,
        final(krnl).cpu_published == old(krnl).cpu_published,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        held_cpus_unchanged(
            old(krnl).cpu_arr,
            final(krnl).cpu_arr,
            old(lctx),
        ),
        held_processes_unchanged(
            old(krnl).prc_mp,
            final(krnl).prc_mp,
            old(lctx),
        ),
        held_pagetables_unchanged(
            old(krnl).pt_mp,
            final(krnl).pt_mp,
            old(lctx),
        ),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
            .view().view().owning_container == parent_container_ptr,
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr)
            .being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_pages.view().contains(thread_page),
        final(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_processes
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes,
        !final(krnl).ctn_mp.spec_index(container_page)
            .view().owned_pages.view().contains(thread_page),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).allocator_4k_lock_maps()
            == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps()
            == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps()
            == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom(),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(
            set![
                page_ptr2page_index(container_page),
                page_ptr2page_index(pcid_allocator_page),
                page_ptr2page_index(allocator_4k_page),
                page_ptr2page_index(allocator_2m_page),
                page_ptr2page_index(allocator_1g_page),
                page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page),
                page_ptr2page_index(process_page),
                page_ptr2page_index(pagetable_page),
                page_ptr2page_index(l4_page),
                page_ptr2page_index(thread_page),
            ],
        ),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))
            .disjoint(
                set![
                    page_ptr2page_index(container_page),
                    page_ptr2page_index(pcid_allocator_page),
                    page_ptr2page_index(allocator_4k_page),
                    page_ptr2page_index(allocator_2m_page),
                    page_ptr2page_index(allocator_1g_page),
                    page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page),
                    page_ptr2page_index(process_page),
                    page_ptr2page_index(pagetable_page),
                    page_ptr2page_index(l4_page),
                    page_ptr2page_index(thread_page),
                ],
            ),
        final(lctx).page_lock_map()
            .remove_keys(
                funding_pages
                    .map_values(|page_ptr: PagePtr| {
                        page_ptr2page_index(page_ptr)
                    })
                    .to_set(),
            )
            .remove(page_ptr2page_index(container_page))
            .remove(page_ptr2page_index(pcid_allocator_page))
            .remove(page_ptr2page_index(allocator_4k_page))
            .remove(page_ptr2page_index(allocator_2m_page))
            .remove(page_ptr2page_index(allocator_1g_page))
            .remove(page_ptr2page_index(scheduler_page))
            .remove(page_ptr2page_index(process_page))
            .remove(page_ptr2page_index(pagetable_page))
            .remove(page_ptr2page_index(l4_page))
            == old(lctx).page_lock_map()
                .remove_keys(
                    funding_pages
                        .map_values(|page_ptr: PagePtr| {
                            page_ptr2page_index(page_ptr)
                        })
                        .to_set(),
                )
                .remove(page_ptr2page_index(container_page))
                .remove(page_ptr2page_index(pcid_allocator_page))
                .remove(page_ptr2page_index(allocator_4k_page))
                .remove(page_ptr2page_index(allocator_2m_page))
                .remove(page_ptr2page_index(allocator_1g_page))
                .remove(page_ptr2page_index(scheduler_page))
                .remove(page_ptr2page_index(process_page))
                .remove(page_ptr2page_index(pagetable_page))
                .remove(page_ptr2page_index(l4_page)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map()
            == old(lctx).container_lock_map().insert(
                container_page,
                TypedHeldLock {
                    lock_id: final(krnl).ctn_mp.lock_id_by_key(
                        container_page,
                    ),
                    mode: TypedLockMode::Write,
                },
            ),
        final(lctx).process_lock_map()
            == old(lctx).process_lock_map().insert(
                process_page,
                TypedHeldLock {
                    lock_id: final(krnl).prc_mp.lock_id_by_key(process_page),
                    mode: TypedLockMode::Write,
                },
            ),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map()
            == old(lctx).scheduler_lock_map().insert(
                scheduler_page,
                TypedHeldLock {
                    lock_id: final(krnl).sched_mp.lock_id_by_key(
                        scheduler_page,
                    ),
                    mode: TypedLockMode::Write,
                },
            ),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(krnl).cpu_set_mp.dom() == old(krnl).cpu_set_mp.dom().insert(cpu_set_page),
        forall|ptr: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(ptr)] old(krnl).cpu_set_mp.dom().contains(ptr) ==> final(krnl).cpu_set_mp.spec_index(ptr) == old(krnl).cpu_set_mp.spec_index(ptr),
        final(krnl).cpu_set_mp.spec_index(cpu_set_page).locking_thread() is None,
        final(lctx).pcid_allocator_lock_map()
            == old(lctx).pcid_allocator_lock_map().insert(
                pcid_allocator_page,
                TypedHeldLock {
                    lock_id: final(krnl).pcid_allc_mp.lock_id_by_key(
                        pcid_allocator_page,
                    ),
                    mode: TypedLockMode::Write,
                },
            ),
        final(lctx).pagetable_lock_map()
            == old(lctx).pagetable_lock_map().insert(
                pagetable_page,
                TypedHeldLock {
                    lock_id: final(krnl).pt_mp.lock_id_by_key(
                        pagetable_page,
                    ),
                    mode: TypedLockMode::Write,
                },
            ),
        final(lctx).iommu_table_lock_map()
            == old(lctx).iommu_table_lock_map(),
        final(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(container_page).being_killed(),
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().scheduler == scheduler_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().cpu_set == cpu_set_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().pcid_allocator == pcid_allocator_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().allocator_ptr_4k == allocator_4k_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().allocator_ptr_2m == allocator_2m_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view_rodata().view().allocator_ptr_1g == allocator_1g_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view().owned_processes.view() == set![process_page],
        final(krnl).cpu_set_mp.spec_index(cpu_set_page)
            .view().owned_cpus.view().is_empty(),
        final(krnl).cpu_set_mp.spec_index(cpu_set_page)
            .view().owned_cpus.closed_view().is_empty(),
        final(krnl).ctn_mp.spec_index(container_page)
            .view().root_process == process_page,
        final(krnl).ctn_mp.spec_index(container_page)
            .view().owned_pages.view()
            == new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page, cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).union(funding_pages.to_set()),
        final(krnl).prc_mp.dom().contains(process_page),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(process_page).being_killed(),
        !final(krnl).prc_mp.spec_index(process_page).view().zombie,
        final(krnl).prc_mp.spec_index(process_page)
            .view_rodata().view().owning_container == container_page,
        final(krnl).prc_mp.spec_index(process_page)
            .view_rodata().view().pagetable == pagetable_page,
        final(krnl).prc_mp.spec_index(process_page)
            .view_rodata().view().parent is None,
        final(krnl).prc_mp.spec_index(process_page)
            .view_rodata().view().depth == 0,
        final(krnl).prc_mp.spec_index(process_page)
            .view().quota_4k == process_quota_4k,
        final(krnl).prc_mp.spec_index(process_page)
            .view().owned_threads.view().len() == 0,
        final(krnl).pt_mp.dom().contains(pagetable_page),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(pagetable_page).view().is_empty(),
        final(krnl).pt_mp.spec_index(pagetable_page).view().proc_ptr == process_page,
        final(krnl).pt_mp.spec_index(pagetable_page)
            .view().page_closure() == set![l4_page],
        final(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        final(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        final(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page)
            .global_pool.view().view() == funding_pages,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page)
            .global_pool.view().len() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page)
            .total_free_pages.view() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page)
            .quota.view().view() == allocator_quota_4k,
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        final(krnl).allc_2m_mp.spec_index(allocator_2m_page)
            .total_free_pages.view() == 0,
        final(krnl).allc_1g_mp.spec_index(allocator_1g_page)
            .total_free_pages.view() == 0,
        final(krnl).sched_mp.dom().contains(scheduler_page),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_page, TypedLockMode::Write),
        !final(krnl).sched_mp.spec_index(scheduler_page).being_killed(),
        final(krnl).sched_mp.spec_index(scheduler_page)
            .view().queue.view().len() == 0,
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            == set![thread_page],
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_1g
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_fields_equal(
                &old(krnl).thr_mp.spec_index(current_thread_ptr).view(),
            ),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().owning_container,
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
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed()
            == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k - 8 - funding_page_count,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m
            == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m - 2,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(container_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        scheduler_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page))
                .view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        process_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        pagetable_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page))
                .view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        l4_page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page))
                .view().locking_thread()->Write_lock_id,
        forall|i: int|
            #![trigger final(krnl).pg_arr.spec_index(page_ptr2page_index(
                funding_pages.spec_index(i),
            )).view().view().free_list]
            0 <= i < funding_pages.len() ==> {
                &&& page_ptr_valid(funding_pages.spec_index(i))
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(
                    funding_pages.spec_index(i),
                )).view().view().free_list
                    == if i == 0 {
                        STAGED_4K_PAGE_CHAIN_END
                    } else {
                        funding_pages.spec_index(i - 1)
                    }
            },
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(allocator_4k_page),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id()
                    == final(krnl).pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(
            *container_tail_lock_perms,
            final(krnl),
            final(lctx),
            page_ptr2page_index(container_page),
        ),
        owned_2m_tail_lock_perms_wf(
            *pcid_allocator_tail_lock_perms,
            final(krnl),
            final(lctx),
            page_ptr2page_index(pcid_allocator_page),
        ),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id()
            == final(krnl).ctn_mp.spec_index(container_page)
                .locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id()
            == final(krnl).prc_mp.spec_index(process_page)
                .locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id()
            == final(krnl).pt_mp.spec_index(pagetable_page)
                .locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id()
            == final(krnl).sched_mp.spec_index(scheduler_page)
                .locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id()
            == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page)
                .locking_thread()->Write_lock_id,
{
    let child_container_ptr = container_page;
    let child_pcid_allocator_ptr = pcid_allocator_page;
    let child_allocator_4k_ptr = allocator_4k_page;
    let child_allocator_2m_ptr = allocator_2m_page;
    let child_allocator_1g_ptr = allocator_1g_page;
    let child_scheduler_ptr = scheduler_page;
    let child_cpu_set_ptr = cpu_set_page;
    let child_process_ptr = process_page;
    let child_pagetable_ptr = pagetable_page;
    let root_pcid: Pcid = KERNEL_DEFAULT_PCID + 1usize;
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let scheduler_index = page_ptr2page_index(scheduler_page);
    let cpu_set_index = page_ptr2page_index(cpu_set_page);
    let process_index = page_ptr2page_index(process_page);
    let pagetable_index = page_ptr2page_index(pagetable_page);
    let l4_index = page_ptr2page_index(l4_page);
    let ghost bootstrap_pages = new_container_bootstrap_4k_pages(
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page, cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    );
    proof {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        assert(page_ptr_valid(container_page)) by {
            reveal(page_ptr_valid);
            reveal(page_ptr_2m_valid);
            assert(container_page % 4096usize == 0) by (nonlinear_arith)
                requires container_page % 0x200000usize == 0;
        };
        assert(page_ptr_valid(pcid_allocator_page)) by {
            reveal(page_ptr_valid);
            reveal(page_ptr_2m_valid);
            assert(pcid_allocator_page % 4096usize == 0) by (nonlinear_arith)
                requires pcid_allocator_page % 0x200000usize == 0;
        };
        assert(container_head != pcid_allocator_head);
        distinct_2m_heads_have_disjoint_tails(
            container_head,
            pcid_allocator_head,
        );
        assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
        assert(krnl.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
        assert(
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .is_init()
        ) by { reveal(container_perms_wf); };
        assert(
            krnl.pg_arr.spec_index(container_head).view().is_init()
                && krnl.pg_arr.spec_index(container_head).view().view().inv()
                && krnl.pg_arr.spec_index(container_head)
                    .view().view().addr == container_page
                && krnl.pg_arr.spec_index(container_head)
                    .view().view().perm_2m.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(pcid_allocator_head).view().is_init()
                && krnl.pg_arr.spec_index(pcid_allocator_head)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(pcid_allocator_head)
                    .view().view().addr == pcid_allocator_page
                && krnl.pg_arr.spec_index(pcid_allocator_head)
                    .view().view().perm_2m.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            bootstrap_pages.contains(allocator_4k_page)
                && bootstrap_pages.contains(allocator_2m_page)
                && bootstrap_pages.contains(allocator_1g_page)
                && bootstrap_pages.contains(scheduler_page)
                && bootstrap_pages.contains(process_page)
                && bootstrap_pages.contains(pagetable_page)
                && bootstrap_pages.contains(l4_page)
        ) by { reveal(new_container_bootstrap_4k_pages); };
        assert(
            krnl.pg_arr.spec_index(allocator_4k_index)
                .view().view().state
                == (PageState::Owned4k { thread_ptr: current_thread_ptr })
                && krnl.pg_arr.spec_index(allocator_2m_index)
                    .view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                && krnl.pg_arr.spec_index(allocator_1g_index)
                    .view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                && krnl.pg_arr.spec_index(scheduler_index)
                    .view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                && krnl.pg_arr.spec_index(process_index)
                    .view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                && krnl.pg_arr.spec_index(pagetable_index)
                    .view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                && krnl.pg_arr.spec_index(l4_index)
                    .view().view().state
                    == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
        );
        assert(
            krnl.pg_arr.spec_index(l4_index)
                .view().is_init()
                && krnl.pg_arr.spec_index(l4_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(l4_index)
                    .view().view().addr == l4_page
                && krnl.pg_arr.spec_index(l4_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(pagetable_index)
                .view().is_init()
                && krnl.pg_arr.spec_index(pagetable_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(pagetable_index)
                    .view().view().addr == pagetable_page
                && krnl.pg_arr.spec_index(pagetable_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(process_index)
                .view().is_init()
                && krnl.pg_arr.spec_index(process_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(process_index)
                    .view().view().addr == process_page
                && krnl.pg_arr.spec_index(process_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(allocator_4k_index).view().is_init()
                && krnl.pg_arr.spec_index(allocator_4k_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(allocator_4k_index)
                    .view().view().addr == allocator_4k_page
                && krnl.pg_arr.spec_index(allocator_4k_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(allocator_2m_index).view().is_init()
                && krnl.pg_arr.spec_index(allocator_2m_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(allocator_2m_index)
                    .view().view().addr == allocator_2m_page
                && krnl.pg_arr.spec_index(allocator_2m_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(allocator_1g_index).view().is_init()
                && krnl.pg_arr.spec_index(allocator_1g_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(allocator_1g_index)
                    .view().view().addr == allocator_1g_page
                && krnl.pg_arr.spec_index(allocator_1g_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(
            krnl.pg_arr.spec_index(scheduler_index).view().is_init()
                && krnl.pg_arr.spec_index(scheduler_index)
                    .view().view().inv()
                && krnl.pg_arr.spec_index(scheduler_index)
                    .view().view().addr == scheduler_page
                && krnl.pg_arr.spec_index(scheduler_index)
                    .view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(krnl.dflt_pt.view().wf()) by {
            reveal(KernelK::default_pagetable_wf);
        };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }
    let child_depth = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().depth + 1;
    let ghost parent_uppers = krnl.ctn_mp.spec_index(parent_container_ptr)
        .view_ghost().uppertree_seq.view();
    let ghost child_uppers = krnl.ctn_mp.spec_index(parent_container_ptr)
        .view_ghost().uppertree_seq.view().push(parent_container_ptr);
    let ghost moved_pages = new_container_moved_pages(
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page, cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ).union(funding_pages.to_set());
    proof {
        assert(krnl.prc_mp.perms_wf()) by { reveal(process_perms_wf); };
        assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
        assert(krnl.sched_mp.perms_wf()) by { reveal(scheduler_perms_wf); };
        assert(krnl.pcid_allc_mp.perms_wf()) by {
            reveal(pcid_allocator_perms_wf);
        };
        assert(krnl.allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        assert(krnl.allc_2m_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        assert(krnl.allc_1g_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        assert(
            parent_uppers.no_duplicates()
                && !parent_uppers.contains(parent_container_ptr)
        ) by {
            reveal(container_perms_wf);
            reveal(container_tree_fields_wf);
            reveal(container_uppertree_seq_wf);
            if parent_uppers.contains(parent_container_ptr) {
                assert(
                    krnl.ctn_mp.spec_index(parent_container_ptr)
                        .view_rodata().view().depth
                        == parent_uppers.index_of(parent_container_ptr)
                );
                assert(
                    parent_uppers.len()
                        == krnl.ctn_mp.spec_index(parent_container_ptr)
                            .view_rodata().view().depth
                );
            }
        };
        assert(child_uppers.no_duplicates()) by {
            seq_push_unique_lemma::<RwLockContainerPtr>();
        };
        assert(child_uppers.to_set().subset_of(krnl.ctn_mp.dom())) by {
            parent_uppers.to_set_ensures();
            child_uppers.to_set_ensures();
            seq_push_lemma::<RwLockContainerPtr>();
            reveal(container_uppertree_seq_wf);
        };
        assert(forall|index: PageIndex|
            #![trigger container_tail_lock_perms.dom().contains(index)]
            container_tail_lock_perms.dom().contains(index) ==> {
                &&& index_valid(NUM_PAGES, index)
                &&& krnl.pg_arr.spec_index(index).view().is_init()
                &&& krnl.pg_arr.spec_index(index).view().view().state
                    is Merged2m
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                &&& container_tail_lock_perms.spec_index(index)
                    .state() is WriteLock
                &&& container_tail_lock_perms.spec_index(index)
                    .thread_id() == lctx.thread_id()
                &&& container_tail_lock_perms.spec_index(index).lock_id()
                    == krnl.pg_arr.spec_index(index).view()
                        .locking_thread()->Write_lock_id
            }
        ) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_array_wf);
        };
        assert(forall|index: PageIndex|
            #![trigger pcid_allocator_tail_lock_perms.dom().contains(index)]
            pcid_allocator_tail_lock_perms.dom().contains(index) ==> {
                &&& index_valid(NUM_PAGES, index)
                &&& krnl.pg_arr.spec_index(index).view().is_init()
                &&& krnl.pg_arr.spec_index(index).view().view().state
                    is Merged2m
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                &&& pcid_allocator_tail_lock_perms.spec_index(index)
                    .state() is WriteLock
                &&& pcid_allocator_tail_lock_perms.spec_index(index)
                    .thread_id() == lctx.thread_id()
                &&& pcid_allocator_tail_lock_perms.spec_index(index).lock_id()
                    == krnl.pg_arr.spec_index(index).view()
                        .locking_thread()->Write_lock_id
            }
        ) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_array_wf);
        };
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            container_head,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            container_head,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            pcid_allocator_head,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            pcid_allocator_head,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            allocator_4k_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            allocator_4k_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            allocator_2m_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            allocator_2m_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            allocator_1g_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            allocator_1g_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            scheduler_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            scheduler_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            process_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            process_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            pagetable_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            pagetable_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            l4_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            l4_index,
        );
        non_merged_page_not_in_owned_2m_tails(
            *container_tail_lock_perms,
            krnl,
            lctx,
            container_head,
            page_ptr2page_index(thread_page),
        );
        non_merged_page_not_in_owned_2m_tails(
            *pcid_allocator_tail_lock_perms,
            krnl,
            lctx,
            pcid_allocator_head,
            page_ptr2page_index(thread_page),
        );
    }

    let ghost pages_before_container_tails = krnl.pg_arr;
    proof {
        assert(pages_before_container_tails == old(krnl).pg_arr);
    }
    set_owned_2m_page_tails_container(
        &mut krnl.pg_arr,
        container_head,
        child_container_ptr,
        Tracked(&*lctx),
        Tracked(container_tail_lock_perms),
    );
    proof {
        assert(
            krnl.pg_arr.spec_index(container_head)
                == pages_before_container_tails.spec_index(container_head)
        ) by {
            assert(
                krnl.pg_arr.spec_index(container_head).view().view()
                    == pages_before_container_tails.spec_index(container_head)
                        .view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(pcid_allocator_head)
                == pages_before_container_tails
                    .spec_index(pcid_allocator_head)
        ) by {
            assert(
                krnl.pg_arr.spec_index(pcid_allocator_head).view().view()
                    == pages_before_container_tails
                        .spec_index(pcid_allocator_head).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(allocator_4k_index)
                == pages_before_container_tails
                    .spec_index(allocator_4k_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(allocator_4k_index).view().view()
                    == pages_before_container_tails
                        .spec_index(allocator_4k_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(allocator_2m_index)
                == pages_before_container_tails
                    .spec_index(allocator_2m_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(allocator_2m_index).view().view()
                    == pages_before_container_tails
                        .spec_index(allocator_2m_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(allocator_1g_index)
                == pages_before_container_tails
                    .spec_index(allocator_1g_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(allocator_1g_index).view().view()
                    == pages_before_container_tails
                        .spec_index(allocator_1g_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(scheduler_index)
                == pages_before_container_tails.spec_index(scheduler_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(scheduler_index).view().view()
                    == pages_before_container_tails
                        .spec_index(scheduler_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(process_index)
                == pages_before_container_tails.spec_index(process_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(process_index).view().view()
                    == pages_before_container_tails
                        .spec_index(process_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(pagetable_index)
                == pages_before_container_tails.spec_index(pagetable_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(pagetable_index).view().view()
                    == pages_before_container_tails
                        .spec_index(pagetable_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(l4_index)
                == pages_before_container_tails.spec_index(l4_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(l4_index).view().view()
                    == pages_before_container_tails
                        .spec_index(l4_index).view().view()
            );
        };
        assert(forall|index: PageIndex|
            #![trigger pcid_allocator_tail_lock_perms.dom().contains(index)]
            pcid_allocator_tail_lock_perms.dom().contains(index) ==> {
                &&& index_valid(NUM_PAGES, index)
                &&& krnl.pg_arr.spec_index(index).view().is_init()
                &&& krnl.pg_arr.spec_index(index).view().view().state
                    is Merged2m
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                &&& pcid_allocator_tail_lock_perms.spec_index(index)
                    .state() is WriteLock
                &&& pcid_allocator_tail_lock_perms.spec_index(index)
                    .thread_id() == lctx.thread_id()
                &&& pcid_allocator_tail_lock_perms.spec_index(index).lock_id()
                    == krnl.pg_arr.spec_index(index).view()
                        .locking_thread()->Write_lock_id
            }
        ) by {
            assert(
                page_2m_tail_indices(container_head).disjoint(
                    page_2m_tail_indices(pcid_allocator_head),
                )
            );
            reveal(owned_2m_tail_lock_perms_wf);
        };
    }
    let ghost pages_before_pcid_allocator_tails = krnl.pg_arr;
    set_owned_2m_page_tails_container(
        &mut krnl.pg_arr,
        pcid_allocator_head,
        child_container_ptr,
        Tracked(&*lctx),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        assert(
            krnl.pg_arr.spec_index(container_head)
                == pages_before_pcid_allocator_tails
                    .spec_index(container_head)
        ) by {
            assert(
                krnl.pg_arr.spec_index(container_head).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(container_head).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(pcid_allocator_head)
                == pages_before_pcid_allocator_tails
                    .spec_index(pcid_allocator_head)
        ) by {
            assert(
                krnl.pg_arr.spec_index(pcid_allocator_head).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(pcid_allocator_head).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(allocator_4k_index)
                == pages_before_pcid_allocator_tails
                    .spec_index(allocator_4k_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(allocator_4k_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(allocator_4k_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(allocator_2m_index)
                == pages_before_pcid_allocator_tails
                    .spec_index(allocator_2m_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(allocator_2m_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(allocator_2m_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(allocator_1g_index)
                == pages_before_pcid_allocator_tails
                    .spec_index(allocator_1g_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(allocator_1g_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(allocator_1g_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(scheduler_index)
                == pages_before_pcid_allocator_tails
                    .spec_index(scheduler_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(scheduler_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(scheduler_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(process_index)
                == pages_before_pcid_allocator_tails
                    .spec_index(process_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(process_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(process_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(pagetable_index)
                == pages_before_pcid_allocator_tails
                    .spec_index(pagetable_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(pagetable_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(pagetable_index).view().view()
            );
        };
        assert(
            krnl.pg_arr.spec_index(l4_index)
                == pages_before_pcid_allocator_tails.spec_index(l4_index)
        ) by {
            assert(
                krnl.pg_arr.spec_index(l4_index).view().view()
                    == pages_before_pcid_allocator_tails
                        .spec_index(l4_index).view().view()
            );
        };
    }

    proof {
        assert forall|i: int|
            #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(
                funding_pages.spec_index(i),
            ))]
            0 <= i < funding_pages.len() implies {
                &&& page_ptr_valid(funding_pages.spec_index(i))
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                    funding_pages.spec_index(i),
                )) == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                    funding_pages.spec_index(i),
                ))
            } by {
                let page_ptr = funding_pages.spec_index(i);
                assert(funding_pages.to_set().contains(page_ptr)) by {
                    funding_pages.to_set_ensures();
                    reveal(Seq::contains);
                };
                assert(funding_page_lock_perms.dom().contains(page_ptr));
                assert(page_ptr_valid(page_ptr));
                page_ptr_valid_imply_page_index_valid();
                page_ptr_roundtrip();
                let page_index = page_ptr2page_index(page_ptr);
                assert(index_valid(NUM_PAGES, page_index));
                assert(
                    !page_2m_tail_indices(container_head)
                        .contains(page_index)
                ) by {
                    if page_2m_tail_indices(container_head)
                        .contains(page_index)
                    {
                        assert(
                            container_head
                                <= page_index
                                < container_head + 512
                        ) by {
                            reveal(page_2m_tail_indices);
                        };
                        page_2m_all_ptrs_contains_index(
                            container_head,
                            page_index,
                        );
                        assert(
                            new_container_moved_pages(
                                container_page,
                                pcid_allocator_page,
                                allocator_4k_page,
                                allocator_2m_page,
                                allocator_1g_page,
                                scheduler_page, cpu_set_page,
                                process_page,
                                pagetable_page,
                                l4_page,
                            ).contains(page_ptr)
                        ) by {
                            reveal(new_container_moved_pages);
                        };
                    }
                };
                assert(
                    !page_2m_tail_indices(pcid_allocator_head)
                        .contains(page_index)
                ) by {
                    if page_2m_tail_indices(pcid_allocator_head)
                        .contains(page_index)
                    {
                        assert(
                            pcid_allocator_head
                                <= page_index
                                < pcid_allocator_head + 512
                        ) by {
                            reveal(page_2m_tail_indices);
                        };
                        page_2m_all_ptrs_contains_index(
                            pcid_allocator_head,
                            page_index,
                        );
                        assert(
                            new_container_moved_pages(
                                container_page,
                                pcid_allocator_page,
                                allocator_4k_page,
                                allocator_2m_page,
                                allocator_1g_page,
                                scheduler_page, cpu_set_page,
                                process_page,
                                pagetable_page,
                                l4_page,
                            ).contains(page_ptr)
                        ) by {
                            reveal(new_container_moved_pages);
                        };
                    }
                };
                assert(
                    krnl.pg_arr.spec_index(page_index)
                        == pages_before_pcid_allocator_tails
                            .spec_index(page_index)
                ) by {
                    assert(
                        krnl.pg_arr.spec_index(page_index).view().view()
                            == pages_before_pcid_allocator_tails
                                .spec_index(page_index).view().view()
                    );
                };
                assert(
                    pages_before_pcid_allocator_tails.spec_index(page_index)
                        == pages_before_container_tails.spec_index(page_index)
                ) by {
                    assert(
                        pages_before_pcid_allocator_tails
                            .spec_index(page_index).view().view()
                            == pages_before_container_tails
                                .spec_index(page_index).view().view()
                    );
                };
                assert(
                    pages_before_container_tails.spec_index(page_index)
                        == old(krnl).pg_arr.spec_index(page_index)
                );
        };
        assert(staged_4k_page_chain(
            krnl.pg_arr,
            funding_pages,
        )) by {
            reveal(staged_4k_page_chain);
        };
        assert(krnl.pg_arr.inv()) by {
            reveal(page_array_wf);
        };
        assert(krnl.pg_arr.typed_lock_map_aligned(
            lctx.page_lock_map(),
            lctx.thread_id(),
        )) by {
            reveal(typed_lock_maps_aligned);
        };
        assert forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) implies {
                &&& page_ptr_valid(page_ptr)
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().is_init()
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().inv()
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).state()
                    is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id()
                    == lctx.thread_id()
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id()
                    == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                        .view().locking_thread()->Write_lock_id
            } by {
            reveal(page_array_wf);
        };
    }
    let funded_global_pool = build_staged_4k_global_pool(
        &mut krnl.pg_arr,
        funding_page_count,
        funding_page_head,
        Ghost(funding_pages),
        child_allocator_4k_ptr,
        child_container_ptr,
        child_depth,
        Tracked(&mut *lctx),
        Tracked(funding_page_lock_perms),
    );

    assert({
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write)
    }) by {
        let index = if !typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write) { container_head } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write) { pcid_allocator_head } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write) { allocator_4k_index } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write) { allocator_2m_index } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write) { allocator_1g_index } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write) { scheduler_index } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write) { cpu_set_index } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write) { process_index } else
            if !typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write) { pagetable_index } else
            { l4_index };
        let mapped = funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr));
        if mapped.to_set().contains(index) {
            let i = choose|i: int| 0 <= i < mapped.len() && mapped.spec_index(i) == index;
            assert(funding_pages.to_set().contains(funding_pages.spec_index(i))) by { funding_pages.to_set_ensures(); };
        }
        assert(typed_lock_map_contains_mode(lctx.page_lock_map().remove_keys(mapped.to_set()), index, TypedLockMode::Write)) by { broadcast use vstd::map::lemma_map_new_index; };
    };
    let ghost old_container_page_lock_id = krnl.pg_arr.lock_id_by_index(container_head);
    let Tracked(container_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            container_head,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(container_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_2m(page);
        page.state = PageState::Allocated2m {
            state: Allocated2MPageState::AsContainer,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(container_head),
            old_container_page_lock_id,
            krnl.pg_arr.lock_id_by_index(container_head),
        );
    }

    let ghost old_pcid_allocator_page_lock_id = krnl.pg_arr.lock_id_by_index(pcid_allocator_head);
    let Tracked(pcid_allocator_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            pcid_allocator_head,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(pcid_allocator_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_2m(page);
        page.state = PageState::Allocated2m {
            state: Allocated2MPageState::AsPcidAllocator,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(pcid_allocator_head),
            old_pcid_allocator_page_lock_id,
            krnl.pg_arr.lock_id_by_index(pcid_allocator_head),
        );
    }

    let allocator_4k_value = PageAllocator::new_with_global_pool(
        child_container_ptr,
        child_depth,
        funded_global_pool,
        allocator_quota_4k,
    );
    let allocator_2m_value = PageAllocator::new_empty(child_container_ptr, child_depth);
    let allocator_1g_value = PageAllocator::new_empty(child_container_ptr, child_depth);
    let scheduler_value = Scheduler::new_empty(
        child_scheduler_ptr,
        child_container_ptr,
        child_depth,
    );
    let mut pcid_allocator_value = PcidAllocator::new_empty(child_container_ptr, child_depth);
    proof {
        assert(pcid_valid(root_pcid)) by {
            reveal(pcid_valid);
        };
        assert(
            pcid_allocator_value.process_is_unallocated(child_process_ptr)
        ) by {
            reveal(PcidAllocator::process_is_unallocated);
        };
    }
    pcid_allocator_value.alloc(root_pcid, child_process_ptr);

    let default_pt = krnl.dflt_pt.borrow();
    let l4_index = page_ptr2page_index(l4_page);
    let ghost old_l4_lock_id = krnl.pg_arr.lock_id_by_index(l4_index);
    let (l4_ptr, Tracked(mut l4_perm)) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            l4_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(l4_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::PageTable {
                pagetable_root: child_pagetable_ptr,
            },
        };
        page.owning_container = child_container_ptr;
        page_perm_to_page_map(l4_page, Tracked(page_perm))
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(l4_index),
            old_l4_lock_id,
            krnl.pg_arr.lock_id_by_index(l4_index),
        );
    }
    default_pt.copy_kernel_entries_to_unpublished_root(
        l4_ptr,
        Tracked(&mut l4_perm),
    );
    proof {
        assert(
            default_pt.kernel_entries.view().len()
                == default_pt.kernel_l4_end
        ) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }
    let pagetable_value = PageTable::<PT_TYPE>::new(
        Some(root_pcid),
        Ghost(default_pt.kernel_entries.view()),
        l4_ptr,
        Tracked(l4_perm),
        default_pt.kernel_l4_end,
        child_process_ptr,
    );

    let pagetable_index = page_ptr2page_index(pagetable_page);
    let ghost old_pagetable_lock_id = krnl.pg_arr.lock_id_by_index(pagetable_index);
    let Tracked(pagetable_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            pagetable_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(pagetable_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::AsPageTableRoot,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(pagetable_index),
            old_pagetable_lock_id,
            krnl.pg_arr.lock_id_by_index(pagetable_index),
        );
    }
    let Tracked(child_pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(
            child_pagetable_ptr,
            pagetable_value,
            Tracked(pagetable_perm),
            Tracked(&mut *lctx),
        );

    let process_value = Process::new_fresh(
        child_process_ptr,
        root_pcid,
        child_pagetable_ptr,
        child_depth,
        process_quota_4k,
    );
    let process_rodata = ReadOnlyNode::new(
        ProcessRO {
            owning_container: child_container_ptr,
            container_depth: child_depth,
            parent: None,
            depth: 0,
            pagetable: child_pagetable_ptr,
            cr3: l4_ptr,
            pcid: root_pcid,
        },
        Ghost(child_process_ptr),
    );
    let process_ghost = ProcessGhost {
        uppertree_seq: Ghost(Seq::empty()),
        subtree_set: Ghost(Set::empty()),
    };
    let process_index = page_ptr2page_index(process_page);
    let ghost old_process_lock_id = krnl.pg_arr.lock_id_by_index(process_index);
    let Tracked(process_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            process_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(process_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::AsProcess,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(process_index),
            old_process_lock_id,
            krnl.pg_arr.lock_id_by_index(process_index),
        );
    }
    let Tracked(child_process_lock_perm) = krnl.retype_page_to_process_and_insert(
            child_process_ptr,
            process_value,
            process_rodata,
            process_ghost,
            Tracked(process_perm),
            Tracked(&mut *lctx),
        );

    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let ghost old_allocator_4k_page_lock_id = krnl.pg_arr.lock_id_by_index(allocator_4k_index);
    let Tracked(allocator_4k_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            allocator_4k_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(allocator_4k_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::As4KAllocator,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(allocator_4k_index),
            old_allocator_4k_page_lock_id,
            krnl.pg_arr.lock_id_by_index(allocator_4k_index),
        );
    }
    krnl.allc_4k_mp.retype_page_to_allocator_and_insert(
        allocator_4k_page,
        allocator_4k_value,
        Tracked(allocator_4k_perm),
    );

    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let ghost old_allocator_2m_page_lock_id = krnl.pg_arr.lock_id_by_index(allocator_2m_index);
    let Tracked(allocator_2m_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            allocator_2m_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(allocator_2m_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::As2MAllocator,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(allocator_2m_index),
            old_allocator_2m_page_lock_id,
            krnl.pg_arr.lock_id_by_index(allocator_2m_index),
        );
    }
    krnl.allc_2m_mp.retype_page_to_allocator_and_insert(
        allocator_2m_page,
        allocator_2m_value,
        Tracked(allocator_2m_perm),
    );

    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let ghost old_allocator_1g_page_lock_id = krnl.pg_arr.lock_id_by_index(allocator_1g_index);
    let Tracked(allocator_1g_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            allocator_1g_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(allocator_1g_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::As1GAllocator,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(allocator_1g_index),
            old_allocator_1g_page_lock_id,
            krnl.pg_arr.lock_id_by_index(allocator_1g_index),
        );
    }
    krnl.allc_1g_mp.retype_page_to_allocator_and_insert(
        allocator_1g_page,
        allocator_1g_value,
        Tracked(allocator_1g_perm),
    );

    let scheduler_index = page_ptr2page_index(scheduler_page);
    let ghost old_scheduler_page_lock_id = krnl.pg_arr.lock_id_by_index(scheduler_index);
    let Tracked(scheduler_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(
            scheduler_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(scheduler_page_lock_perm),
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::AsScheduler,
        };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(scheduler_index),
            old_scheduler_page_lock_id,
            krnl.pg_arr.lock_id_by_index(scheduler_index),
        );
    }
    let Tracked(child_scheduler_lock_perm) = krnl.sched_mp.retype_4k_and_insert(
            child_scheduler_ptr,
            scheduler_value,
            (),
            Ghost(()),
            Tracked(scheduler_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::Scheduler(child_scheduler_ptr)),
        );

    let cpu_set_value = CpuSet::new_empty(child_container_ptr, child_depth);
    let ghost old_cpu_set_page_lock_id = krnl.pg_arr.lock_id_by_index(cpu_set_index);
    let Tracked(cpu_set_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(cpu_set_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(cpu_set_page_lock_perm));
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet };
        page.owning_container = child_container_ptr;
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(KernelObjId::Page(cpu_set_index), old_cpu_set_page_lock_id, krnl.pg_arr.lock_id_by_index(cpu_set_index));
    }
    let Tracked(child_cpu_set_lock_perm) = krnl.cpu_set_mp.retype_4k_and_insert(child_cpu_set_ptr, cpu_set_value, (), Ghost(()), Tracked(cpu_set_perm), Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(child_cpu_set_ptr)));

    krnl.cpu_set_mp.wunlock(child_cpu_set_ptr, Tracked(&mut *lctx), Tracked(child_cpu_set_lock_perm), Ghost(KernelObjId::CpuSet(child_cpu_set_ptr)));

    let Tracked(child_pcid_allocator_lock_perm) = krnl.pcid_allc_mp.retype_2m_and_insert(
            child_pcid_allocator_ptr,
            pcid_allocator_value,
            (),
            Ghost(()),
            Tracked(pcid_allocator_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::PcidAllocator(child_pcid_allocator_ptr)),
        );

    let mut container_value = Container::new_staged(
        child_container_ptr,
        child_process_ptr,
        child_depth,
    );
    container_value.owned_processes = Ghost(Set::empty().insert(child_process_ptr));
    container_value.owned_pages = Ghost(moved_pages);
    let container_rodata = ReadOnlyNode::new(
        ContainerRO {
            parent: Some(parent_container_ptr),
            depth: child_depth,
            scheduler: child_scheduler_ptr,
            pcid_allocator: child_pcid_allocator_ptr,
            cpu_set: child_cpu_set_ptr,
            allocator_ptr_4k: child_allocator_4k_ptr,
            allocator_ptr_2m: child_allocator_2m_ptr,
            allocator_ptr_1g: child_allocator_1g_ptr,
        },
        Ghost(child_container_ptr),
    );
    let container_ghost = ContainerGhost {
        uppertree_seq: Ghost(child_uppers),
        subtree_set: Ghost(Set::empty()),
        owned_threads: Ghost(Set::empty()),
        owned_indirect_threads: Ghost(Set::empty()),
    };
    let Tracked(child_container_lock_perm) = krnl.ctn_mp.retype_2m_and_insert(
            child_container_ptr,
            container_value,
            container_rodata,
            Ghost(container_ghost),
            Tracked(container_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::Container(child_container_ptr)),
        );

    {
        let child = krnl.ctn_mp.borrow_mut_typed(
            child_container_ptr,
            Ghost(lctx.container_lock_map()),
            Tracked(&*lctx),
            Tracked(&child_container_lock_perm),
        );
        let (node_addr, mut node_perm) = child.parent_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, child_container_ptr);
        let parent = krnl.ctn_mp.borrow_mut_typed(
            parent_container_ptr,
            Ghost(lctx.container_lock_map()),
            Tracked(&*lctx),
            Tracked(parent_container_lock_perm),
        );
        parent.children.push_tail(node_addr, node_perm);
    }
    proof {
        container_insert_child_into_ancestor_subtree_sets(
            &mut krnl.ctn_mp,
            child_uppers,
            child_container_ptr,
        );
    }
    {
        let parent = krnl.ctn_mp.borrow_mut_typed(
            parent_container_ptr,
            Ghost(lctx.container_lock_map()),
            Tracked(&*lctx),
            Tracked(parent_container_lock_perm),
        );
        parent.owned_pages = Ghost(parent.owned_pages.view().difference(moved_pages));
    }
    {
        let thread = krnl.thr_mp.borrow_mut_typed(
            current_thread_ptr,
            Ghost(lctx.thread_lock_map()),
            Tracked(&*lctx),
            Tracked(current_thread_lock_perm),
        );
        thread.temp_alloc_cache_4k = Ghost(
            thread.temp_alloc_cache_4k.view().difference(
                new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page, cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).union(funding_pages.to_set()),
            ),
        );
        thread.temp_alloc_cache_2m = Ghost(Set::empty());
        thread.quota_4k = thread.quota_4k - 8 - funding_page_count;
        thread.quota_2m = thread.quota_2m - 2;
    }

    proof {
        assert(
            page_2m_tail_indices(container_head).disjoint(
                set![
                    container_head,
                    pcid_allocator_head,
                    allocator_4k_index,
                    allocator_2m_index,
                    allocator_1g_index,
                    scheduler_index,
                    process_index,
                    pagetable_index,
                    l4_index,
                    page_ptr2page_index(thread_page),
                ],
            )
        ) by {
            reveal(Set::disjoint);
        };
        assert(
            page_2m_tail_indices(pcid_allocator_head).disjoint(
                set![
                    container_head,
                    pcid_allocator_head,
                    allocator_4k_index,
                    allocator_2m_index,
                    allocator_1g_index,
                    scheduler_index,
                    process_index,
                    pagetable_index,
                    l4_index,
                    page_ptr2page_index(thread_page),
                ],
            )
        ) by {
            reveal(Set::disjoint);
        };
        assert(
            lctx.page_lock_map()
                .remove_keys(
                    funding_pages
                        .map_values(|page_ptr: PagePtr| {
                            page_ptr2page_index(page_ptr)
                        })
                        .to_set(),
                )
                .remove(container_head)
                .remove(pcid_allocator_head)
                .remove(allocator_4k_index)
                .remove(allocator_2m_index)
                .remove(allocator_1g_index)
                .remove(scheduler_index).remove(cpu_set_index)
                .remove(process_index)
                .remove(pagetable_index)
                .remove(l4_index)
                == old(lctx).page_lock_map()
                    .remove_keys(
                        funding_pages
                            .map_values(|page_ptr: PagePtr| {
                                page_ptr2page_index(page_ptr)
                            })
                            .to_set(),
                    )
                    .remove(container_head)
                    .remove(pcid_allocator_head)
                    .remove(allocator_4k_index)
                    .remove(allocator_2m_index)
                    .remove(allocator_1g_index)
                    .remove(scheduler_index).remove(cpu_set_index)
                    .remove(process_index)
                    .remove(pagetable_index)
                    .remove(l4_index)
        ) by {
            reveal(typed_lock_maps_inserted);
            reveal(Map::remove_keys);
        };
        assert(container_add_child_ensures(
            krnl.rt_ctn,
            old(krnl).ctn_mp,
            krnl.ctn_mp,
            parent_container_ptr,
            child_container_ptr,
        )) by {
            reveal(container_perms_wf);
            reveal(LinkedList::wf_value_list);
            seq_push_lemma::<RwLockContainerPtr>();
        };
        container_add_child_preserves_tree_wf(
            krnl.rt_ctn,
            old(krnl).ctn_mp,
            krnl.ctn_mp,
            parent_container_ptr,
            child_container_ptr,
        );
        assert(krnl.subsystems_inv()) by {
            reveal(KernelK::default_pagetable_wf);
            reveal(page_array_wf);
            reveal(container_perms_wf);
            reveal(process_perms_wf);
            reveal(pagetable_perms_wf);
            reveal(scheduler_perms_wf);
            reveal(pcid_allocator_perms_wf);

            reveal(allocator_perms_wf);
            reveal(thread_perms_wf);
            reveal(LinkedList::wf_value_list);
        };
        assert(krnl.memory_management_inv()) by {
            reveal(allocator_4k_pages_wf);
            reveal(allocator_2m_pages_wf);
            reveal(allocator_1g_pages_wf);
            reveal(container_page_owner_wf);
            reveal(hugepage_2m_wf);
            reveal(hugepage_1g_wf);
            reveal(mapped_4k_page_pagetable_wf);
            reveal(mapped_2m_page_pagetable_wf);
            reveal(mapped_1g_page_pagetable_wf);
            reveal(container_process_page_pagetable_wf);
            reveal(container_process_wf);
            reveal(container_pages_wf);
            reveal(process_pages_wf);
            reveal(pagetable_pages_wf);
            reveal(iommu_table_pages_wf);
            reveal(thread_pages_wf);
            reveal(scheduler_pages_wf);
            reveal(pcid_allocator_pages_wf);

            reveal(thread_staged_pages_4k_wf);
            reveal(thread_staged_pages_2m_wf);
            reveal(thread_staged_pages_1g_wf);
            reveal(endpoint_pages_wf);
            reveal(process_pagetable_match);
            reveal(process_iommu_table_match);
            reveal(allocator_free_page_ptrs_wf);
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
            reveal(container_allocator_wf);
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(container_allocator_free_2m_page_wf);
            reveal(container_allocator_global_free_2m_page_wf);
            reveal(container_allocator_cpu_cache_free_2m_page_wf);
            reveal(container_allocator_free_1g_page_wf);
            reveal(container_allocator_global_free_1g_page_wf);
            reveal(container_allocator_cpu_cache_free_1g_page_wf);
            lemma_process_effective_quota_4k_fold_sum_eq_forall();
            lemma_process_effective_quota_2m_fold_sum_eq_forall();
            lemma_process_effective_quota_1g_fold_sum_eq_forall();
        };
        assert(krnl.process_management_inv()) by {
            reveal(container_process_wf);
            reveal(per_container_process_tree_wf);
            reveal(process_root_wf);
            reveal(process_children_parent_wf);
            reveal(process_linkedlist_wf);
            reveal(process_children_depth_wf);
            reveal(process_subtree_set_wf);
            reveal(process_uppertree_seq_wf);
            reveal(process_subtree_set_exclusive);
            reveal(container_endpoint_wf);
            reveal(container_cpu_wf);
            reveal(container_scheduler_wf);
            reveal(container_pcid_allocator_wf);

            reveal(process_pcid_allocator_wf);
            reveal(thread_endpoint_ref_counter_wf);
            reveal(thread_endpoint_queue_wf);
            reveal(thread_caller_callee_wf);
            reveal(container_thread_endpoint_wf);
            reveal(container_thread_scheduler_wf);
            reveal(container_thread_wf);
            reveal(process_cpu_wf);
            reveal(process_thread_wf);
            reveal(process_empty_lists_wlocked);
            reveal(thread_cpu_wf);
        };
        assert(cpu_dirty_map_wf(
            krnl.ctn_mp, krnl.cpu_set_mp,
            krnl.prc_mp,
            krnl.cpu_arr,
            krnl.cpu_tlb,
            krnl.pt_mp, krnl.pcid_needflush,
        )) by {
            reveal(cpu_dirty_map_contains_container_processes);
            reveal(cpu_dirty_map_proc_pcid_match);
            reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by {
            reveal(tlb_wf_spec);
        };
        assert(iommu_root_table_process_wf(
            &krnl.irt,
            krnl.prc_mp,
            krnl.it_mp,
        )) by { reveal(iommu_root_table_process_wf); };
        assert(process_pci_function_ownership_wf(
            &krnl.irt,
            krnl.prc_mp,
        )) by { reveal(process_pci_function_ownership_wf); };
        assert(iommu_tlb_wf_spec(
            krnl.iommu_tlb,
            &krnl.irt,
            krnl.prc_mp,
            krnl.it_mp,
        )) by { reveal(iommu_tlb_wf_spec); };
    }

    (
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(child_pcid_allocator_lock_perm),
    )
}

}

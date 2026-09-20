use vstd::{assert_maps_equal, assert_seqs_equal, assert_sets_equal};
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn cleanup_published_4k_page_chain(
    krnl: &mut KernelK, count: usize, head: PagePtr, Ghost(page_ptrs): Ghost<Seq<PagePtr>>,
    child_allocator_ptr: RwLockPageAllocatorPtr, child_container_ptr: RwLockContainerPtr,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(krnl).allc_4k_mp.dom().contains(child_allocator_ptr),
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
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
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
        final(lctx).cpu_id() == old(lctx).cpu_id(),
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
        final(krnl).allc_4k_mp.dom().contains(child_allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(child_allocator_ptr)
            == old(krnl).allc_4k_mp.spec_index(child_allocator_ptr),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ..*old(krnl)
        }),
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
                &&& !final(lctx).page_lock_map().dom().contains(page_ptr2page_index(page_ptr))
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
            lctx.cpu_id() == old(lctx).cpu_id(),
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
            krnl.pt_mp == old(krnl).pt_mp,
            krnl.it_mp == old(krnl).it_mp,
            krnl.irt == old(krnl).irt,
            krnl.cpu_arr == old(krnl).cpu_arr,
            krnl.pcid_needflush == old(krnl).pcid_needflush,
            krnl.cpu_published == old(krnl).cpu_published,
            krnl.ctn_mp == old(krnl).ctn_mp,
            krnl.sched_mp == old(krnl).sched_mp,
            krnl.pcid_allc_mp == old(krnl).pcid_allc_mp,
            krnl.cpu_set_mp == old(krnl).cpu_set_mp,
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
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
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
            broadcast use page_ptr_sequence_index_in_equal_set;
            assert({
                &&& 0 <= remaining - 1 < page_ptrs.len()
                &&& page_ptr == page_ptrs.spec_index(remaining - 1)
            }) by {
                reveal(Seq::contains);
            };
            assert(page_ptrs.to_set().contains(page_ptr)) by { page_ptrs.to_set_ensures(); };
            page_ptr_valid_imply_page_index_valid();
            vstd::seq::lemma_seq_subrange_index(
                page_ptrs,
                0,
                remaining as int,
                remaining - 1,
            );
        }
        let page_index = page_ptr2page_index(page_ptr);
        proof { page_array_wf_at(krnl.pg_arr, page_index); }
        let next = {
            let page = krnl.pg_arr.borrow_typed(
                page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perms.tracked_borrow(page_ptr)));
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
            page_ptr_sequence_index_in_mapped_set(
                page_ptrs,
                old_remaining - 1,
            );
            reveal(page_ptrs_to_indices);
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
                assert(lctx.page_lock_map().submap_of(lctx_before.page_lock_map())) by { broadcast use vstd::map::axiom_map_remove_different; };
                submap_by_transitivity(lctx.page_lock_map(), lctx_before.page_lock_map(), old(lctx).page_lock_map());
            };
            assert forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(
                    page_ptrs.spec_index(i),
                )).view().view().free_list]
                0 <= i < remaining implies {
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
                };
                assert(
                    page_ptr2page_index(other_ptr) != page_index
                ) by {
                    page_ptr2page_index_injective();
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
                        ) by {
                            page_ptrs.to_set_ensures();
                            page_ptr_valid_imply_page_index_valid();
                        };
                        assert(
                            !lctx_before.page_lock_map().dom().contains(
                                page_ptr2page_index(other_ptr),
                            )
                        ) by {
                            page_ptrs.to_set_ensures();
                            page_ptr_valid_imply_page_index_valid();
                        };
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
        assert(held_pages_unchanged_except(
            old(krnl).pg_arr,
            krnl.pg_arr,
            old(lctx),
            page_ptrs_to_indices(page_ptrs),
        )) by {
            held_pages_unchanged_except_for_changed_set(
                old(krnl).pg_arr,
                krnl.pg_arr,
                old(lctx),
                page_ptrs_to_indices(page_ptrs),
            );
        };
        let mapped = page_ptrs.map_values(
            |p: PagePtr| page_ptr2page_index(p),
        );
        assert(
            lctx.page_lock_map().dom().disjoint(
                page_ptrs_to_indices(page_ptrs),
            )
        ) by {
            reveal(page_ptrs_to_indices);
            let held_indices = lctx.page_lock_map().dom();
            let staged_indices = mapped.to_set();
            assert(held_indices.intersect(staged_indices)
                =~= Set::<PageIndex>::empty()) by {
                assert_sets_equal!(
                    held_indices.intersect(staged_indices)
                        == Set::<PageIndex>::empty(),
                    page_index => {
                        if held_indices.contains(page_index)
                            && staged_indices.contains(page_index)
                        {
                            mapped.to_set_ensures();
                            assert(mapped.contains(page_index));
                            mapped.index_of_first_ensures(page_index);
                            let i = mapped.index_of_first(page_index).unwrap();
                            assert(page_ptrs.to_set().contains(
                                page_ptrs.spec_index(i),
                            )) by {
                                page_ptrs.to_set_ensures();
                                assert(page_ptrs.contains(
                                    page_ptrs.spec_index(i),
                                ));
                            };
                            assert(
                                page_index == page_ptr2page_index(
                                    page_ptrs.spec_index(i),
                                )
                            ) by {
                                reveal(Seq::map_values);
                            };
                            assert(
                                krnl.pg_arr.spec_index(page_index)
                                    .view().view().free_list == 0
                            ) by {
                                page_ptrs.to_set_ensures();
                                page_ptr_valid_imply_page_index_valid();
                            };
                        }
                    }
                );
            };
            vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(
                held_indices,
                staged_indices,
            );
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


}

use vstd::prelude::*;
use crate::*;
use super::*;

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
            )).view().view().free_list == if i == 0 {
                    STAGED_4K_PAGE_CHAIN_END
                } else {
                    page_ptrs.spec_index(i - 1)
                }
    }
}

pub(super) proof fn staged_4k_page_chain_page_ptrs_valid(pages: PageLockedArray, page_ptrs: Seq<PagePtr>,)
    requires
        staged_4k_page_chain(pages, page_ptrs),
    ensures
        forall|i: int|
            #![trigger page_ptr_valid(page_ptrs.spec_index(i))]
            0 <= i < page_ptrs.len() ==> page_ptr_valid(page_ptrs.spec_index(i)),
{
    assert forall|i: int|
        #![trigger page_ptr_valid(page_ptrs.spec_index(i))]
        0 <= i < page_ptrs.len()
            implies page_ptr_valid(page_ptrs.spec_index(i)) by {
        assert(pages.spec_index(page_ptr2page_index(
            page_ptrs.spec_index(i),
        )).view().view().free_list == if i == 0 {
            STAGED_4K_PAGE_CHAIN_END
        } else {
            page_ptrs.spec_index(i - 1)
        }) by { reveal(staged_4k_page_chain); };
        reveal(staged_4k_page_chain);
    };
}

pub open spec fn staged_4k_page_chain_head(page_ptrs: Seq<PagePtr>) -> PagePtr {
    if page_ptrs.len() == 0 {
        STAGED_4K_PAGE_CHAIN_END
    } else {
        page_ptrs.last()
    }
}

#[verifier::spinoff_prover]
pub(super) fn build_staged_4k_global_pool(
    pages: &mut PageLockedArray, count: usize, head: PagePtr, Ghost(page_ptrs): Ghost<Seq<PagePtr>>,
    Ghost(page_indices): Ghost<Set<PageIndex>>, Ghost(process_map): Ghost<ProcessLockedMap>,
    Ghost(scheduler_map): Ghost<SchedulerLockedMap>, Ghost(cpu_set_map): Ghost<CpuSetLockedMap>,
    child_allocator_ptr: RwLockPageAllocatorPtr, child_container_ptr: RwLockContainerPtr, child_depth: usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
) -> (ret: LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        process_pages_wf(*old(pages), process_map),
        scheduler_pages_wf(scheduler_map, *old(pages)),
        cpu_set_pages_wf(cpu_set_map, *old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id(),),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptrs.len() == count,
        page_ptrs.no_duplicates(),
        page_indices == page_ptrs.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ).to_set(),
        head == staged_4k_page_chain_head(page_ptrs),
        staged_4k_page_chain(*old(pages), page_ptrs),
        page_lock_perms.dom() == page_ptrs.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).state()
                    is WriteLock
                &&& page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(page_ptr).lock_id() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        process_pages_wf(*final(pages), process_map),
        scheduler_pages_wf(scheduler_map, *final(pages)),
        cpu_set_pages_wf(cpu_set_map, *final(pages)),
        ret.wf(),
        ret.view() == page_ptrs,
        forall|page_ptr: PagePtr|
            #![trigger ret.view().contains(page_ptr)]
            ret.view().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& page_ptr_valid(page_ptr) ==> {
                    let node_addr = final(pages).spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().view().free_list_node_storage.addr();
                    &&& ret.map().dom().contains(node_addr)
                    &&& ret.map().spec_index(node_addr) == page_ptr
                }
            },
        ret.container_depth == Some(child_depth),
        ret.minor == Some(child_container_ptr),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(lctx).page_lock_map().remove_keys(page_indices) == old(lctx).page_lock_map().remove_keys(page_indices),
        forall|index: PageIndex|
            #![trigger page_indices.contains(index)]
            !page_indices.contains(index) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
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
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id(),),
        lock_id_set_aligned(final(lctx)),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view().free_list]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list
            },
        staged_4k_page_chain(*final(pages), page_ptrs),
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(
                page_ptr2page_index(page_ptr),
            )]
            page_ptr_valid(page_ptr) && !page_ptrs.to_set().contains(page_ptr) ==> final(pages).spec_index(page_ptr2page_index(page_ptr)) == old(pages).spec_index(page_ptr2page_index(page_ptr)),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_indices.contains(index) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).lock_id() == final(pages).spec_index(
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
        broadcast use page_ptr_sequence_index_in_equal_set;
        reveal(staged_4k_page_chain);
    }
    while remaining > 0
        invariant
            pages.inv(),
            page_array_wf(*pages),
            forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view().mappings()]
                index_valid(NUM_PAGES, index) ==> pages.spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
            pages.typed_lock_map_aligned(
                lctx.page_lock_map(),
                lctx.thread_id(),
            ),
            lock_id_set_aligned(lctx),
            lctx.kernel_view_locking_state() is Release,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom(),
            lctx.page_lock_map().remove_keys(page_indices) == old(lctx).page_lock_map().remove_keys(page_indices),
            forall|index: PageIndex|
                #![trigger page_indices.contains(index)]
                !page_indices.contains(index) ==> lctx.page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|page_ptr: PagePtr|
                #![trigger pages.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().free_list]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& pages.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == old(pages).spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().free_list
                },
            forall|page_ptr: PagePtr|
                #![trigger pages.spec_index(
                    page_ptr2page_index(page_ptr),
                )]
                page_ptr_valid(page_ptr) && !page_ptrs.to_set().contains(page_ptr) ==> pages.spec_index(page_ptr2page_index(page_ptr)) == old(pages).spec_index(
                        page_ptr2page_index(page_ptr),
                    ),
            forall|index: PageIndex|
                #![trigger page_indices.contains(index)]
                index_valid(NUM_PAGES, index) && !page_indices.contains(index) ==> pages.spec_index(index) == old(pages).spec_index(index),
            page_ptrs.len() == count,
            page_ptrs.no_duplicates(),
            page_indices == page_ptrs.map_values(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
            ).to_set(),
            page_lock_perms.dom() == page_ptrs.to_set(),
            0 <= remaining <= count,
            current == if remaining == 0 {
                STAGED_4K_PAGE_CHAIN_END
            } else {
                page_ptrs.spec_index(remaining - 1)
            },
            global_pool.wf(),
            global_pool.view() == page_ptrs.subrange(remaining as int, count as int),
            forall|page_ptr: PagePtr|
                #![trigger global_pool.view().contains(page_ptr)]
                global_pool.view().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& page_ptr_valid(page_ptr) ==> {
                        let node_addr = pages.spec_index(
                            page_ptr2page_index(page_ptr),
                        ).view().view().free_list_node_storage.addr();
                        &&& global_pool.map().dom().contains(node_addr)
                        &&& global_pool.map().spec_index(node_addr) == page_ptr
                    }
                },
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
                    )).view().view().free_list == if i == 0 {
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
                    )).view().view().owning_container == child_container_ptr
                    &&& pages.spec_index(page_ptr2page_index(
                        page_ptrs.spec_index(i),
                    )).view().view().free_list == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                },
            forall|page_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(page_ptr)]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                    &&& page_lock_perms.spec_index(page_ptr).state()
                        is WriteLock
                    &&& page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
                    &&& page_lock_perms.spec_index(page_ptr).lock_id() == pages.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
                },
        decreases remaining,
    {
        let page_ptr = current;
        proof {
            assert(page_ptrs.to_set().contains(page_ptr)) by { page_ptrs.to_set_ensures(); reveal(Seq::contains); };
            page_ptr_valid_imply_page_index_valid();
        }
        let page_index = page_ptr2page_index(page_ptr);
        proof { page_array_wf_at(*pages, page_index); }
        let ghost pages_before_step = *pages;
        let ghost old_page_lock_id = pages.lock_id_by_index(page_index);
        let (next, node_addr, Tracked(node_perm)) = {
            let page = pages.borrow_mut_typed(
                page_index,
                Ghost(lctx.page_lock_map()),
                Tracked(&*lctx),
                Tracked(page_lock_perms.tracked_borrow(page_ptr)),
            );
            let next = page.free_list;
            let (addr, Tracked(perm)) = convert_owned_4k_to_free_global(page, child_allocator_ptr, child_container_ptr,);
            (next, addr, Tracked(perm))
        };
        proof {
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                pages.lock_id_by_index(page_index),
            );
            assert(pages.spec_index(page_index).view().inv()) by { reveal(RwLock::inv); };
            assert(pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by {
                assert(pages_before_step.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { reveal(page_array_wf); };
            };
            assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
            let mapped_page_indices = page_ptrs.map_values(
                |mapped_page_ptr: PagePtr| {
                    page_ptr2page_index(mapped_page_ptr)
                },
            );
            assert(mapped_page_indices.spec_index(remaining - 1) == page_index) by {
                vstd::seq::lemma_seq_new_index(
                    page_ptrs.len(),
                    |i: int| {
                        page_ptr2page_index(page_ptrs.spec_index(i))
                    },
                    remaining - 1,
                );
            };
            assert(mapped_page_indices.to_set().contains(page_index)) by { mapped_page_indices.to_set_ensures(); };
            assert(page_indices.contains(page_index));
            assert forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view().mappings()]
                index_valid(NUM_PAGES, index) implies
                    pages.spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings() by {
                if index == page_index {
                    assert(pages.spec_index(index).view().view().mappings() == pages_before_step.spec_index(index).view().view().mappings());
                }
            };
            assert(lctx.page_lock_map().remove_keys(page_indices) == old(lctx).page_lock_map().remove_keys(page_indices)) by { reveal(typed_lock_maps_inserted); reveal(Map::remove_keys); };
        }
        let mut node_perm = Tracked(node_perm);
        node_update_value(node_addr, &mut node_perm, page_ptr);
        global_pool.push_head(node_addr, node_perm);
        proof { seq_push_head_lemma::<PagePtr>(); }
        current = next;
        remaining = remaining - 1;
        proof {
            assert(global_pool.view() == page_ptrs.subrange(remaining as int, count as int,)) by { seq_subrange_split_lemma::<PagePtr>(); };
        }
    }
    proof {
        assert(remaining == 0);
        assert(staged_4k_page_chain(*pages, page_ptrs)) by { broadcast use page_ptr_sequence_index_in_equal_set; reveal(staged_4k_page_chain); };
        let mapped_page_indices = page_ptrs.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        );
        assert(mapped_page_indices.to_set() == page_indices);
        assert forall|index: PageIndex|
            #![trigger page_indices.contains(index)]
            index_valid(NUM_PAGES, index) && page_indices.contains(index)
            implies {
                &&& old(pages).spec_index(index).view().view().state
                    is Owned4k
                &&& pages.spec_index(index).view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    })
            } by {
            mapped_page_indices.to_set_ensures();
            assert(mapped_page_indices.contains(index));
            mapped_page_indices.index_of_first_ensures(index);
            let i = mapped_page_indices.index_of_first(index).unwrap();
            reveal(Seq::map_values);
            let page_ptr = page_ptrs.spec_index(i);
            assert(page_ptrs.to_set().contains(page_ptr)) by { page_ptrs.to_set_ensures(); };
            assert(page_lock_perms.dom().contains(page_ptr));
        };
        assert({
            &&& process_pages_wf(*pages, process_map)
            &&& scheduler_pages_wf(scheduler_map, *pages)
            &&& cpu_set_pages_wf(cpu_set_map, *pages)
        }) by {
            assert forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view().state]
                index_valid(NUM_PAGES, index) && {
                        ||| old(pages).spec_index(index).view().view().state
                            is Allocated4k
                        ||| pages.spec_index(index).view().view().state
                            is Allocated4k
                    }
                implies pages.spec_index(index).view().view().state == old(pages).spec_index(index).view().view().state by {
                if page_indices.contains(index) {
                    assert(old(pages).spec_index(index).view().view().state is Owned4k);
                    assert(pages.spec_index(index).view().view().state is Free4k);
                }
            };
            process_pages_wf_preserved_for_page_state_eq(*old(pages), *pages, process_map, process_map,);
            scheduler_pages_wf_preserved_for_page_state_eq(scheduler_map, scheduler_map, *old(pages), *pages,);
            reveal(cpu_set_pages_wf);
        };
        page_ptrs.to_set_ensures();
    }
    global_pool
}
}

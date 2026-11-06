use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub const STAGED_4K_PAGE_CHAIN_END: PagePtr = usize::MAX;

pub open spec fn staged_4k_page_chain(pages: PageLockedArray, page_ptrs: Seq<PagePtr>) -> bool {
    forall|i: int|
        #![trigger pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list]
        #![trigger page_ptr_valid(page_ptrs.spec_index(i))]
        0 <= i < page_ptrs.len() ==> {
            &&& page_ptr_valid(page_ptrs.spec_index(i))
            &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(i - 1) }
    }
}

pub open spec fn staged_4k_page_chain_head(page_ptrs: Seq<PagePtr>) -> PagePtr {
    if page_ptrs.len() == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.last() }
}

pub(super) fn build_staged_4k_global_pool(
    pages: &mut PageLockedArray, count: usize, head: PagePtr, Ghost(page_ptrs): Ghost<Seq<PagePtr>>, Ghost(page_indices): Ghost<Set<PageIndex>>,
    child_allc_ptr: RwLockPageAllocatorPtr, child_ctn_ptr: RwLockContainerPtr, child_depth: usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
) -> (ret: (LinkedList<PagePtr, 233>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        page_ptrs.len() == count,
        page_ptrs.no_duplicates(),
        page_indices == page_ptrs.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr),).to_set(),
        head == staged_4k_page_chain_head(page_ptrs),
        staged_4k_page_chain(*old(pages), page_ptrs),
        page_lock_perms.dom() == page_ptrs.to_set(),
        forall|pg_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(pg_ptr)]
            page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& old(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(pg_ptr).state() is WriteLock
                &&& page_lock_perms.spec_index(pg_ptr).thread_id() == lctx.thread_id()
                &&& page_lock_perms.spec_index(pg_ptr).lock_id() == old(pages).spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id
            },
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        ret.0.wf(),
        ret.0.view() == page_ptrs,
        forall|pg_ptr: PagePtr|
            #![trigger ret.0.view().contains(pg_ptr)]
            ret.0.view().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& page_ptr_valid(pg_ptr) ==> {
                    let node_addr = final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr();
                    &&& ret.0.map().dom().contains(node_addr)
                    &&& ret.0.map().spec_index(node_addr) == pg_ptr
                }
            },
        ret.0.container_depth.view() == Some(child_depth),
        ret.0.minor.view() == Some(child_ctn_ptr),
        final(pages).typed_lock_map_aligned(ret.1.view(), lctx.thread_id()),
        ret.1.view().dom() == lctx.page_lock_map().dom(),
        forall|index: PageIndex| #![trigger page_indices.contains(index)] !page_indices.contains(index) ==> ret.1.view().get(index) == lctx.page_lock_map().get(index),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        forall|pg_ptr: PagePtr|
            #![trigger final(pages).spec_index(page_ptr2page_index(pg_ptr),).view().view().free_list]
            page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list == old(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list
            },
        staged_4k_page_chain(*final(pages), page_ptrs),
        forall|pg_ptr: PagePtr|
            #![trigger final(pages).spec_index(page_ptr2page_index(pg_ptr),)]
            page_ptr_valid(pg_ptr) && !page_ptrs.to_set().contains(pg_ptr) ==> final(pages).spec_index(page_ptr2page_index(pg_ptr)) == old(pages).spec_index(page_ptr2page_index(pg_ptr)),
        forall|index: PageIndex| #![trigger final(pages).spec_index(index)] index_valid(NUM_PAGES, index) && !page_indices.contains(index) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
        forall|pg_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(pg_ptr)]
            page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(child_allc_ptr), state: FreePageAllocatorState::GlobalList })
                &&& final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == child_ctn_ptr
                &&& typed_lock_map_contains_mode(ret.1.view(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(pg_ptr).lock_id() == final(pages).spec_index(page_ptr2page_index(pg_ptr),).view().locking_thread()->Write_lock_id
            },
        forall|i: int|
            #![trigger page_ptrs.spec_index(i)]
            0 <= i < page_ptrs.len() ==> {
                &&& typed_lock_map_contains_mode(ret.1.view(), page_ptr2page_index(page_ptrs.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptrs.spec_index(i)), TypedLockMode::Write)
            },
{
    let mut global_pool = LinkedList::new(Some(child_depth), Some(child_ctn_ptr));
    let ghost mut page_locks = lctx.page_lock_map();
    let mut current = head;
    let mut remaining = count;
    proof { broadcast use page_ptr_sequence_index_in_equal_set; }
    while remaining > 0
        invariant
            pages.inv(),
            page_array_wf(*old(pages)),
            forall|index: PageIndex|
                #![trigger pages.spec_index(index)]
                index_valid(NUM_PAGES, index) ==> pages.spec_index(index) == old(pages).spec_index(index) || (pages.spec_index(index).view().inv() && pages.spec_index(index).view().view().addr == old(pages).spec_index(index).view().view().addr),
            forall|index: PageIndex| #![trigger pages.spec_index(index).view().view().mappings()] index_valid(NUM_PAGES, index) ==> pages.spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
            forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view().iommu_mappings()]
                index_valid(NUM_PAGES, index) ==> pages.spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
            pages.typed_lock_map_aligned(page_locks, lctx.thread_id()),
            page_locks.dom() == lctx.page_lock_map().dom(),
            forall|index: PageIndex| #![trigger page_indices.contains(index)] !page_indices.contains(index) ==> page_locks.get(index) == lctx.page_lock_map().get(index),
            forall|pg_ptr: PagePtr|
                #![trigger pages.spec_index(page_ptr2page_index(pg_ptr),).view().view().free_list]
                page_lock_perms.dom().contains(pg_ptr) ==> {
                    &&& page_ptr_valid(pg_ptr)
                    &&& pages.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list == old(pages).spec_index(page_ptr2page_index(pg_ptr),).view().view().free_list
                },
            forall|pg_ptr: PagePtr|
                #![trigger pages.spec_index(page_ptr2page_index(pg_ptr),)]
                page_ptr_valid(pg_ptr) && !page_ptrs.to_set().contains(pg_ptr) ==> pages.spec_index(page_ptr2page_index(pg_ptr)) == old(pages).spec_index(page_ptr2page_index(pg_ptr)),
            forall|index: PageIndex| #![trigger page_indices.contains(index)] index_valid(NUM_PAGES, index) && !page_indices.contains(index) ==> pages.spec_index(index) == old(pages).spec_index(index),
            page_ptrs.len() == count,
            page_ptrs.no_duplicates(),
            page_indices == page_ptrs.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr),).to_set(),
            page_lock_perms.dom() == page_ptrs.to_set(),
            0 <= remaining <= count,
            current == if remaining == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(remaining - 1) },
            global_pool.wf(),
            global_pool.view() == page_ptrs.subrange(remaining as int, count as int),
            forall|pg_ptr: PagePtr|
                #![trigger global_pool.view().contains(pg_ptr)]
                global_pool.view().contains(pg_ptr) ==> {
                    &&& page_ptr_valid(pg_ptr)
                    &&& page_ptr_valid(pg_ptr) ==> {
                        let node_addr = pages.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr();
                        &&& global_pool.map().dom().contains(node_addr)
                        &&& global_pool.map().spec_index(node_addr) == pg_ptr
                    }
                },
            global_pool.length == count - remaining,
            global_pool.container_depth.view() == Some(child_depth),
            global_pool.minor.view() == Some(child_ctn_ptr),
            forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().state]
                0 <= i < remaining ==> {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().state is Owned4k
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(i - 1) }
                },
            forall|i: int|
                #![trigger page_ptrs.spec_index(i)]
                remaining <= i < count ==> {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(child_allc_ptr), state: FreePageAllocatorState::GlobalList })
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().owning_container == child_ctn_ptr
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(i - 1) }
                },
            forall|pg_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(pg_ptr)]
                page_lock_perms.dom().contains(pg_ptr) ==> {
                    &&& page_ptr_valid(pg_ptr)
                    &&& typed_lock_map_contains_mode(page_locks, page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                    &&& page_lock_perms.spec_index(pg_ptr).state() is WriteLock
                    &&& page_lock_perms.spec_index(pg_ptr).thread_id() == lctx.thread_id()
                    &&& page_lock_perms.spec_index(pg_ptr).lock_id() == pages.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id
                },
        decreases remaining,
    {
        let pg_ptr = current;
        proof { assert(page_ptrs.to_set().contains(pg_ptr)) by { page_ptrs.to_set_ensures(); }; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); }
        let pg_idx = page_ptr2page_index(pg_ptr);
        proof { page_array_wf_at(*old(pages), pg_idx); }
        let ghost pages_before_step = *pages;
        let (next, node_addr, Tracked(node_perm)) = {
            let page = pages.borrow_mut_typed(pg_idx, Ghost(page_locks), Tracked(lctx), Tracked(page_lock_perms.tracked_borrow(pg_ptr)));
            let next = page.free_list;
            let (addr, Tracked(perm)) = convert_owned_4k_to_free_global(page, child_allc_ptr, child_ctn_ptr,);
            (next, addr, Tracked(perm))
        };
        proof {
            page_locks = page_locks.insert(pg_idx, TypedHeldLock { lock_id: pages.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
            let mapped_page_indices = page_ptrs.map_values(|mapped_pg_ptr: PagePtr| { page_ptr2page_index(mapped_pg_ptr) });
            assert(mapped_page_indices.spec_index(remaining - 1) == pg_idx) by { vstd::seq::lemma_seq_new_index(page_ptrs.len(), |i: int| { page_ptr2page_index(page_ptrs.spec_index(i)) }, remaining - 1); };
            assert(pages.spec_index(pg_idx).view().view().mappings() == pages_before_step.spec_index(pg_idx).view().view().mappings());
            assert(pages.spec_index(pg_idx).view().view().iommu_mappings() == pages_before_step.spec_index(pg_idx).view().view().iommu_mappings());
        }
        let mut node_perm = Tracked(node_perm);
        node_update_value(node_addr, &mut node_perm, pg_ptr);
        global_pool.push_head(node_addr, node_perm);
        proof { seq_insert_head_implies_contains::<PagePtr>(); }
        current = next;
        remaining = remaining - 1;
    }
    proof {
        page_ptrs.to_set_ensures();
        create_container_from_staged_pages_eof_page_array_wf(*old(pages), *pages);
    }
    (global_pool, Ghost(page_locks))
}

/// Rekeys 4K pages that the publish chain flipped while it held Acquire, in reverse sequence order.
pub(super) proof fn rekey_published_4k_page_chain(tracked lctx: &mut LocalContext, page_ptrs: Seq<PagePtr>, remaining: int, page_locks: Map<PageIndex, TypedHeldLock>)
    requires
        old(lctx).kernel_view_locking_state() is Release,
        0 <= remaining <= page_ptrs.len(),
        page_ptrs.no_duplicates(),
        page_locks.dom() =~= old(lctx).page_lock_map().dom(),
        forall|index: PageIndex|
            #![trigger page_locks.get(index)]
            #![trigger page_locks.index(index)]
            !page_ptrs.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr)).to_set().contains(index) ==> page_locks.get(index) == old(lctx).page_lock_map().get(index),
        forall|i: int|
            #![trigger page_ptrs.spec_index(i)]
            0 <= i < page_ptrs.len() ==> {
                &&& page_ptr_valid(page_ptrs.spec_index(i))
                &&& typed_lock_map_contains_mode(page_locks, page_ptr2page_index(page_ptrs.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptrs.spec_index(i)), TypedLockMode::Write)
                &&& remaining <= i ==> old(lctx).page_lock_map().index(page_ptr2page_index(page_ptrs.spec_index(i))) == page_locks.index(page_ptr2page_index(page_ptrs.spec_index(i)))
            },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map() == page_locks,
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
    decreases remaining,
{
    if remaining > 0 {
        let index = page_ptr2page_index(page_ptrs.spec_index(remaining - 1));
        let old_lock_id = lctx.page_lock_map().index(index).lock_id;
        lctx.update_lock_id(KernelObjId::Page(index), old_lock_id, page_locks.index(index).lock_id);
        page_ptr2page_index_injective(); page_ptr_sequence_index_in_mapped_set(page_ptrs, remaining - 1);
        rekey_published_4k_page_chain(lctx, page_ptrs, remaining - 1, page_locks);
    } else {
        assert(lctx.page_lock_map() =~= page_locks) by { page_ptrs.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr)).to_set_ensures(); };
    }
}

pub(super) fn retype_new_container_owned_2m_pages(
    pages: &mut PageLockedArray, child_ctn_ptr: RwLockContainerPtr, container_page: PagePtr, pcid_allocator_page: PagePtr,
    Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<PagePerm2m>, Tracked<PagePerm2m>))
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(page_locks, lctx.thread_id()),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        old(pages).spec_index(page_ptr2page_index(container_page)).view().view().state is Owned2m,
        old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state is Owned2m,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == lctx.thread_id(),
        container_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == lctx.thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(page_locks.insert(page_ptr2page_index(container_page), TypedHeldLock { lock_id: final(pages).lock_id_by_index(page_ptr2page_index(container_page)), mode: TypedLockMode::Write })
            .insert(page_ptr2page_index(pcid_allocator_page), TypedHeldLock { lock_id: final(pages).lock_id_by_index(page_ptr2page_index(pcid_allocator_page)), mode: TypedLockMode::Write }), lctx.thread_id()),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().owning_container == child_ctn_ptr,
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == child_ctn_ptr,
        container_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        ret.0.view().is_init(),
        ret.0.view().addr() == container_page,
        ret.1.view().is_init(),
        ret.1.view().addr() == pcid_allocator_page,
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    proof { assert(container_head != pcid_allocator_head) by { page_ptr2page_index_neq(container_page, pcid_allocator_page); }; }
    let Tracked(container_perm) = page_array_retype_owned_2m_for_container(
        pages, child_ctn_ptr, container_page, Allocated2MPageState::AsContainer, Ghost(page_locks), Tracked(lctx), Tracked(container_page_lock_perm),
    );
    let ghost container_page_locks = page_locks.insert(container_head, TypedHeldLock { lock_id: pages.lock_id_by_index(container_head), mode: TypedLockMode::Write });
    let Tracked(pcid_allocator_perm) = page_array_retype_owned_2m_for_container(
        pages, child_ctn_ptr, pcid_allocator_page, Allocated2MPageState::AsPcidAllocator, Ghost(container_page_locks), Tracked(lctx), Tracked(pcid_allocator_page_lock_perm),
    );
    (Tracked(container_perm), Tracked(pcid_allocator_perm))
}

pub(super) fn prepare_new_container_backing_pages(
    pages: &mut PageLockedArray, container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr,
    thread_page: PagePtr, funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    Ghost(funding_indices): Ghost<Set<PageIndex>>, child_allocator_4k_ptr: RwLockPageAllocatorPtr, child_ctn_ptr: RwLockContainerPtr,
    child_depth: usize, Ghost(reference_krnl): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>,
) -> (ret: (LinkedList<PagePtr, 233>, Tracked<PagePerm2m>, Tracked<PagePerm2m>, Ghost<Map<PageIndex, TypedHeldLock>>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        reference_krnl.pg_arr == *old(pages),
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
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
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state is Owned2m,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state is Owned2m,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(process_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state is Owned4k,
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_indices == funding_pages.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr)).to_set(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(reference_krnl.pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        forall|pg_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(pg_ptr)]
            funding_page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& reference_krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(pg_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(pg_ptr).thread_id() == lctx.thread_id()
                &&& funding_page_lock_perms.spec_index(pg_ptr).lock_id() == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id
            },
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page)),
        !funding_pages.to_set().contains(thread_page),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == lctx.thread_id(),
        container_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == lctx.thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(ret.4.view(), lctx.thread_id()),
        ret.4.view().dom() == ret.3.view().dom(),
        forall|index: PageIndex|
            #![trigger ret.4.view().get(index)]
            #![trigger ret.4.view().dom().contains(index)]
            index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> ret.4.view().get(index) == ret.3.view().get(index),
        typed_lock_map_contains_mode(ret.4.view(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.4.view(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        ret.3.view().dom() == lctx.page_lock_map().dom(),
        forall|i: int|
            #![trigger funding_pages.spec_index(i)]
            0 <= i < funding_pages.len() ==> {
                &&& typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
            },
        forall|index: PageIndex| #![trigger ret.3.view().get(index)] #![trigger ret.3.view().dom().contains(index)] !funding_indices.contains(index) ==> ret.3.view().get(index) == lctx.page_lock_map().get(index),
        ret.0.wf(),
        ret.0.view() == funding_pages,
        forall|pg_ptr: PagePtr|
            #![trigger ret.0.view().contains(pg_ptr)]
            ret.0.view().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& page_ptr_valid(pg_ptr) ==> {
                    let node_addr = final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr();
                    &&& ret.0.map().dom().contains(node_addr)
                    &&& ret.0.map().spec_index(node_addr) == pg_ptr
                }
            },
        ret.0.container_depth.view() == Some(child_depth),
        ret.0.minor.view() == Some(child_ctn_ptr),
        ret.1.view().is_init(),
        ret.1.view().addr() == container_page,
        ret.2.view().is_init(),
        ret.2.view().addr() == pcid_allocator_page,
        forall|pg_ptr: PagePtr|
            #![trigger final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list]
            funding_pages.to_set().contains(pg_ptr) ==> final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list,
        staged_4k_page_chain(*final(pages), funding_pages),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == reference_krnl.pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == reference_krnl.pg_arr.spec_index(index).view().view().iommu_mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page)
                ==> final(pages).spec_index(index) == reference_krnl.pg_arr.spec_index(index),
        forall|pg_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(pg_ptr)]
            funding_page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_4k_ptr), state: FreePageAllocatorState::GlobalList,
                })
                &&& final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == child_ctn_ptr
                &&& typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(pg_ptr).lock_id() == final(pages).spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id
            },
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().owning_container == child_ctn_ptr,
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == child_ctn_ptr,
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        final(pages).spec_index(page_ptr2page_index(allocator_4k_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)),
        final(pages).spec_index(page_ptr2page_index(allocator_2m_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)),
        final(pages).spec_index(page_ptr2page_index(allocator_1g_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)),
        final(pages).spec_index(page_ptr2page_index(scheduler_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)),
        final(pages).spec_index(page_ptr2page_index(cpu_set_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(cpu_set_page)),
        final(pages).spec_index(page_ptr2page_index(process_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(process_page)),
        final(pages).spec_index(page_ptr2page_index(pagetable_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)),
        final(pages).spec_index(page_ptr2page_index(l4_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)),
        final(pages).spec_index(page_ptr2page_index(thread_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)),
        ret.3.view().get(page_ptr2page_index(allocator_4k_page)) == lctx.page_lock_map().get(page_ptr2page_index(allocator_4k_page)),
        ret.3.view().get(page_ptr2page_index(allocator_2m_page)) == lctx.page_lock_map().get(page_ptr2page_index(allocator_2m_page)),
        ret.3.view().get(page_ptr2page_index(allocator_1g_page)) == lctx.page_lock_map().get(page_ptr2page_index(allocator_1g_page)),
        ret.3.view().get(page_ptr2page_index(scheduler_page)) == lctx.page_lock_map().get(page_ptr2page_index(scheduler_page)),
        ret.3.view().get(page_ptr2page_index(cpu_set_page)) == lctx.page_lock_map().get(page_ptr2page_index(cpu_set_page)),
        ret.3.view().get(page_ptr2page_index(process_page)) == lctx.page_lock_map().get(page_ptr2page_index(process_page)),
        ret.3.view().get(page_ptr2page_index(pagetable_page)) == lctx.page_lock_map().get(page_ptr2page_index(pagetable_page)),
        ret.3.view().get(page_ptr2page_index(l4_page)) == lctx.page_lock_map().get(page_ptr2page_index(l4_page)),
        ret.3.view().get(page_ptr2page_index(thread_page)) == lctx.page_lock_map().get(page_ptr2page_index(thread_page)),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(process_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3.view(), page_ptr2page_index(l4_page), TypedLockMode::Write),
{
    hide(Seq::contains);
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
    let thread_pg_idx = page_ptr2page_index(thread_page);
    let (global_pool, Ghost(pool_page_locks)) = build_staged_4k_global_pool(
        pages, funding_page_count, funding_page_head, Ghost(funding_pages), Ghost(funding_indices), child_allocator_4k_ptr, child_ctn_ptr, child_depth,
        Tracked(lctx), Tracked(funding_page_lock_perms),
    );
    proof {
        assert({
            &&& !funding_pages.to_set().contains(container_page)
            &&& !funding_pages.to_set().contains(pcid_allocator_page)
            &&& !funding_pages.to_set().contains(allocator_4k_page)
            &&& !funding_pages.to_set().contains(allocator_2m_page)
            &&& !funding_pages.to_set().contains(allocator_1g_page)
            &&& !funding_pages.to_set().contains(scheduler_page)
            &&& !funding_pages.to_set().contains(cpu_set_page)
            &&& !funding_pages.to_set().contains(process_page)
            &&& !funding_pages.to_set().contains(pagetable_page)
            &&& !funding_pages.to_set().contains(l4_page)
        }) by { reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages); };
        page_ptr_seq_indices_excludes_page(funding_pages, container_page); page_ptr_seq_indices_excludes_page(funding_pages, pcid_allocator_page);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_4k_page); page_ptr_seq_indices_excludes_page(funding_pages, allocator_2m_page);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_1g_page); page_ptr_seq_indices_excludes_page(funding_pages, scheduler_page);
        page_ptr_seq_indices_excludes_page(funding_pages, cpu_set_page); page_ptr_seq_indices_excludes_page(funding_pages, process_page);
        page_ptr_seq_indices_excludes_page(funding_pages, pagetable_page); page_ptr_seq_indices_excludes_page(funding_pages, l4_page);
        page_ptr_seq_indices_excludes_page(funding_pages, thread_page);
        page_array_wf_at(*pages, container_head); page_array_wf_at(*pages, pcid_allocator_head);
    }
    let (Tracked(container_perm), Tracked(pcid_allocator_perm)) = retype_new_container_owned_2m_pages(
        pages, child_ctn_ptr, container_page, pcid_allocator_page, Ghost(pool_page_locks), Tracked(lctx), Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm),
    );
    proof {
        assert(staged_4k_page_chain(*pages, funding_pages)) by { broadcast use page_ptr_sequence_index_in_equal_set; broadcast use page_ptr_sequence_index_in_mapped_set; };
    }
    let ghost prepared_page_locks = pool_page_locks.insert(container_head, TypedHeldLock { lock_id: pages.lock_id_by_index(container_head), mode: TypedLockMode::Write })
        .insert(pcid_allocator_head, TypedHeldLock { lock_id: pages.lock_id_by_index(pcid_allocator_head), mode: TypedLockMode::Write });
    (global_pool, Tracked(container_perm), Tracked(pcid_allocator_perm), Ghost(pool_page_locks), Ghost(prepared_page_locks))
}
}

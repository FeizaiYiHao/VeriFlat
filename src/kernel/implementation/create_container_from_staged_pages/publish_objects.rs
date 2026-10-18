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

pub(super) proof fn staged_4k_page_chain_page_ptrs_valid(pages: PageLockedArray, page_ptrs: Seq<PagePtr>,)
    requires
        staged_4k_page_chain(pages, page_ptrs),
    ensures
        forall|i: int|
            #![trigger page_ptr_valid(page_ptrs.spec_index(i))]
            0 <= i < page_ptrs.len() ==> page_ptr_valid(page_ptrs.spec_index(i)),
{}

pub open spec fn staged_4k_page_chain_head(page_ptrs: Seq<PagePtr>) -> PagePtr {
    if page_ptrs.len() == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.last() }
}

#[verifier::spinoff_prover]
pub(super) fn build_staged_4k_global_pool(
    pages: &mut PageLockedArray, count: usize, head: PagePtr, Ghost(page_ptrs): Ghost<Seq<PagePtr>>, Ghost(page_indices): Ghost<Set<PageIndex>>,
    child_allocator_ptr: RwLockPageAllocatorPtr, child_container_ptr: RwLockContainerPtr, child_depth: usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
) -> (ret: (LinkedList<PagePtr, ALLOCATOR_GLOBAL_POOL_MAJOR>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        page_ptrs.len() == count,
        page_ptrs.no_duplicates(),
        page_indices == page_ptrs.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr),).to_set(),
        head == staged_4k_page_chain_head(page_ptrs),
        staged_4k_page_chain(*old(pages), page_ptrs),
        page_lock_perms.dom() == page_ptrs.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
                &&& page_lock_perms.spec_index(page_ptr).lock_id() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        ret.0.wf(),
        ret.0.view() == page_ptrs,
        forall|page_ptr: PagePtr|
            #![trigger ret.0.view().contains(page_ptr)]
            ret.0.view().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& page_ptr_valid(page_ptr) ==> {
                    let node_addr = final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr();
                    &&& ret.0.map().dom().contains(node_addr)
                    &&& ret.0.map().spec_index(node_addr) == page_ptr
                }
            },
        ret.0.container_depth.view() == Some(child_depth),
        ret.0.minor.view() == Some(child_container_ptr),
        final(pages).typed_lock_map_aligned(ret.1@, lctx.thread_id()),
        ret.1@.dom() == lctx.page_lock_map().dom(),
        forall|index: PageIndex|
            #![trigger page_indices.contains(index)]
            !page_indices.contains(index) ==> ret.1@.get(index) == lctx.page_lock_map().get(index),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().free_list]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list
            },
        staged_4k_page_chain(*final(pages), page_ptrs),
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(page_ptr2page_index(page_ptr),)]
            page_ptr_valid(page_ptr) && !page_ptrs.to_set().contains(page_ptr) ==> final(pages).spec_index(page_ptr2page_index(page_ptr)) == old(pages).spec_index(page_ptr2page_index(page_ptr)),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_indices.contains(index) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(child_allocator_ptr), state: FreePageAllocatorState::GlobalList })
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(ret.1@, page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr),).view().locking_thread()->Write_lock_id
            },
        forall|i: int|
            #![trigger page_ptrs.spec_index(i)]
            0 <= i < page_ptrs.len() ==> {
                &&& typed_lock_map_contains_mode(ret.1@, page_ptr2page_index(page_ptrs.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptrs.spec_index(i)), TypedLockMode::Write)
            },
{
    let mut global_pool = LinkedList::new(Some(child_depth), Some(child_container_ptr));
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
            forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view().mappings()]
                index_valid(NUM_PAGES, index) ==> pages.spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
            forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view().iommu_mappings()]
                index_valid(NUM_PAGES, index) ==> pages.spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
            pages.typed_lock_map_aligned(page_locks, lctx.thread_id()),
            page_locks.dom() == lctx.page_lock_map().dom(),
            forall|index: PageIndex|
                #![trigger page_indices.contains(index)]
                !page_indices.contains(index) ==> page_locks.get(index) == lctx.page_lock_map().get(index),
            forall|page_ptr: PagePtr|
                #![trigger pages.spec_index(page_ptr2page_index(page_ptr),).view().view().free_list]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& pages.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().free_list
                },
            forall|page_ptr: PagePtr|
                #![trigger pages.spec_index(page_ptr2page_index(page_ptr),)]
                page_ptr_valid(page_ptr) && !page_ptrs.to_set().contains(page_ptr) ==> pages.spec_index(page_ptr2page_index(page_ptr)) == old(pages).spec_index(page_ptr2page_index(page_ptr)),
            forall|index: PageIndex|
                #![trigger page_indices.contains(index)]
                index_valid(NUM_PAGES, index) && !page_indices.contains(index) ==> pages.spec_index(index) == old(pages).spec_index(index),
            page_ptrs.len() == count,
            page_ptrs.no_duplicates(),
            page_indices == page_ptrs.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr),).to_set(),
            page_lock_perms.dom() == page_ptrs.to_set(),
            0 <= remaining <= count,
            current == if remaining == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(remaining - 1) },
            global_pool.wf(),
            global_pool.view() == page_ptrs.subrange(remaining as int, count as int),
            forall|page_ptr: PagePtr|
                #![trigger global_pool.view().contains(page_ptr)]
                global_pool.view().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& page_ptr_valid(page_ptr) ==> {
                        let node_addr = pages.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr();
                        &&& global_pool.map().dom().contains(node_addr)
                        &&& global_pool.map().spec_index(node_addr) == page_ptr
                    }
                },
            global_pool.length == count - remaining,
            global_pool.container_depth.view() == Some(child_depth),
            global_pool.minor.view() == Some(child_container_ptr),
            forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().state]
                0 <= i < remaining ==> {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().state is Owned4k
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(i - 1) }
                },
            forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().state]
                remaining <= i < count ==> {
                    &&& page_ptr_valid(page_ptrs.spec_index(i))
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(child_allocator_ptr), state: FreePageAllocatorState::GlobalList })
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i),)).view().view().owning_container == child_container_ptr
                    &&& pages.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 { STAGED_4K_PAGE_CHAIN_END } else { page_ptrs.spec_index(i - 1) }
                },
            forall|page_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(page_ptr)]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& typed_lock_map_contains_mode(page_locks, page_ptr2page_index(page_ptr), TypedLockMode::Write)
                    &&& page_lock_perms.spec_index(page_ptr).state() is WriteLock
                    &&& page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
                    &&& page_lock_perms.spec_index(page_ptr).lock_id() == pages.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
                },
        decreases remaining,
    {
        let page_ptr = current;
        proof { assert(page_ptrs.to_set().contains(page_ptr)) by { page_ptrs.to_set_ensures(); }; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); }
        let page_index = page_ptr2page_index(page_ptr);
        proof { page_array_wf_at(*old(pages), page_index); }
        let ghost pages_before_step = *pages;
        let (next, node_addr, Tracked(node_perm)) = {
            let page = pages.borrow_mut_typed(page_index, Ghost(page_locks), Tracked(lctx), Tracked(page_lock_perms.tracked_borrow(page_ptr)));
            let next = page.free_list;
            let (addr, Tracked(perm)) = convert_owned_4k_to_free_global(page, child_allocator_ptr, child_container_ptr,);
            (next, addr, Tracked(perm))
        };
        proof {
            page_locks = page_locks.insert(page_index, TypedHeldLock { lock_id: pages.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            let mapped_page_indices = page_ptrs.map_values(|mapped_page_ptr: PagePtr| { page_ptr2page_index(mapped_page_ptr) });
            assert(mapped_page_indices.spec_index(remaining - 1) == page_index) by { vstd::seq::lemma_seq_new_index(page_ptrs.len(), |i: int| { page_ptr2page_index(page_ptrs.spec_index(i)) }, remaining - 1); };
            assert(pages.spec_index(page_index).view().view().mappings() == pages_before_step.spec_index(page_index).view().view().mappings());
            assert(pages.spec_index(page_index).view().view().iommu_mappings() == pages_before_step.spec_index(page_index).view().view().iommu_mappings());
        }
        let mut node_perm = Tracked(node_perm);
        node_update_value(node_addr, &mut node_perm, page_ptr);
        global_pool.push_head(node_addr, node_perm);
        proof { seq_push_head_lemma::<PagePtr>(); }
        current = next;
        remaining = remaining - 1;
    }
    proof {
        let mapped_page_indices = page_ptrs.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr),);
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
            !page_ptrs.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set().contains(index) ==> page_locks.get(index) == old(lctx).page_lock_map().get(index),
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
        assert(lctx.page_lock_map() =~= page_locks) by { page_ptrs.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set_ensures(); };
    }
}

pub(super) fn set_new_container_owned_2m_page_tail_pair(
    pages: &mut PageLockedArray, container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr,
    thread_page: PagePtr, owning_container: RwLockContainerPtr, Ghost(reference_krnl): Ghost<KernelK>, Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    Ghost(funding_indices): Ghost<Set<PageIndex>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>, Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        reference_krnl.inv(),
        reference_krnl.pg_arr == *old(pages),
        old(pages).inv(),
        page_array_wf(*old(pages)),
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
        funding_indices == funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr),).to_set(),
        staged_4k_page_chain(reference_krnl.pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> page_ptr_valid(page_ptr),
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page)),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *old(pages), lctx, page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *old(pages), lctx, page_ptr2page_index(pcid_allocator_page),),
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *final(pages), lctx, page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *final(pages), lctx, page_ptr2page_index(pcid_allocator_page),),
        funding_indices.disjoint(page_2m_tail_indices(page_ptr2page_index(container_page),)),
        funding_indices.disjoint(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page),)),
        page_2m_tail_indices(page_ptr2page_index(container_page),).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ]),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page),).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ]),
        staged_4k_page_chain(*final(pages), funding_pages),
        forall|index: PageIndex|
            #![trigger container_tail_lock_perms.dom().contains(index)]
            container_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == owning_container,
        forall|index: PageIndex|
            #![trigger pcid_allocator_tail_lock_perms.dom().contains(index)]
            pcid_allocator_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == owning_container,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == reference_krnl.pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == reference_krnl.pg_arr.spec_index(index).view().view().iommu_mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().state]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().state == reference_krnl.pg_arr.spec_index(index).view().view().state,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().owning_container]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().owning_container]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(page_ptr2page_index(container_page)).contains(index) && !page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(index)
                ==> final(pages).spec_index(index).view().view().owning_container == reference_krnl.pg_arr.spec_index(index).view().view().owning_container,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            #![trigger reference_krnl.pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(page_ptr2page_index(container_page)).contains(index) && !page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(index)
                ==> final(pages).spec_index(index) == reference_krnl.pg_arr.spec_index(index),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> final(pages).spec_index(page_ptr2page_index(page_ptr)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)),
        final(pages).spec_index(page_ptr2page_index(container_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(container_page),),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page),),
        final(pages).spec_index(page_ptr2page_index(allocator_4k_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),),
        final(pages).spec_index(page_ptr2page_index(allocator_2m_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),),
        final(pages).spec_index(page_ptr2page_index(allocator_1g_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),),
        final(pages).spec_index(page_ptr2page_index(scheduler_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page),),
        final(pages).spec_index(page_ptr2page_index(cpu_set_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(cpu_set_page),),
        final(pages).spec_index(page_ptr2page_index(process_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(process_page),),
        final(pages).spec_index(page_ptr2page_index(pagetable_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page),),
        final(pages).spec_index(page_ptr2page_index(l4_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(l4_page),),
        final(pages).spec_index(page_ptr2page_index(thread_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(thread_page),),
{
    hide(Seq::contains);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let ghost protected_page_index_seq = seq![
        container_head,
        pcid_allocator_head,
        page_ptr2page_index(allocator_4k_page),
        page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(scheduler_page),
        page_ptr2page_index(cpu_set_page),
        page_ptr2page_index(process_page),
        page_ptr2page_index(pagetable_page),
        page_ptr2page_index(l4_page),
        page_ptr2page_index(thread_page),
    ];
    let ghost protected_page_indices = protected_page_index_seq.to_set();
    proof {
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page,);
        assert(container_head != pcid_allocator_head) by { page_ptr2page_index_injective(); };
        distinct_2m_heads_have_disjoint_tails(container_head, pcid_allocator_head,);
        distinct_2m_heads_have_disjoint_all_ptrs(container_head, pcid_allocator_head,);
        page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head);
        assert(!page_2m_tail_indices(container_head).contains(pcid_allocator_head) && !page_2m_tail_indices(pcid_allocator_head).contains(container_head)) by {
            if page_2m_tail_indices(container_head).contains(pcid_allocator_head) { page_2m_all_ptrs_contains_index(container_head, pcid_allocator_head,); }
            if page_2m_tail_indices(pcid_allocator_head).contains(container_head) { page_2m_all_ptrs_contains_index(pcid_allocator_head, container_head,); }
        };
        assert(page_2m_tail_indices(container_head).disjoint(protected_page_indices) && page_2m_tail_indices(pcid_allocator_head).disjoint(protected_page_indices)) by {
            reveal(Seq::contains);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_4k_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_2m_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_1g_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, scheduler_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, cpu_set_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, process_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, pagetable_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, l4_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, thread_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_4k_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_2m_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_1g_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, scheduler_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, cpu_set_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, process_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, pagetable_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, l4_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, thread_page, pcid_allocator_head,);
            protected_page_index_seq.to_set_ensures();
        };
        assert(funding_pages.to_set().disjoint(page_2m_all_ptrs(container_head),)) by { reveal(new_container_moved_pages); };
        assert(funding_pages.to_set().disjoint(page_2m_all_ptrs(pcid_allocator_head),)) by { reveal(new_container_moved_pages); };
        page_ptr_indices_disjoint_from_2m_tail(funding_pages, funding_indices, container_head,);
        page_ptr_indices_disjoint_from_2m_tail(funding_pages, funding_indices, pcid_allocator_head,);
        assert(funding_pages.to_set().map(|page_ptr: PagePtr| page_ptr2page_index(page_ptr),) =~= funding_indices) by { broadcast use Seq::lemma_to_set_map_commutes; };
    }
    set_owned_2m_page_tail_pair_container(
        pages, container_head, pcid_allocator_head, owning_container, Ghost(reference_krnl.pg_arr), Ghost(funding_pages),
        Ghost(funding_page_lock_perms.dom()), Ghost(funding_indices), Ghost(protected_page_indices), Tracked(lctx),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        assert({
            &&& pages.spec_index(container_head) == reference_krnl.pg_arr.spec_index(container_head)
            &&& pages.spec_index(pcid_allocator_head) == reference_krnl.pg_arr.spec_index(pcid_allocator_head)
            &&& pages.spec_index(page_ptr2page_index(allocator_4k_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),)
            &&& pages.spec_index(page_ptr2page_index(allocator_2m_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),)
            &&& pages.spec_index(page_ptr2page_index(allocator_1g_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),)
            &&& pages.spec_index(page_ptr2page_index(scheduler_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page),)
            &&& pages.spec_index(page_ptr2page_index(cpu_set_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(cpu_set_page),)
            &&& pages.spec_index(page_ptr2page_index(process_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(process_page),)
            &&& pages.spec_index(page_ptr2page_index(pagetable_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page),)
            &&& pages.spec_index(page_ptr2page_index(l4_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(l4_page),)
            &&& pages.spec_index(page_ptr2page_index(thread_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(thread_page),)
        }) by { page_ptr_valid_imply_page_index_valid(); protected_page_index_seq.to_set_ensures(); };
    }
}

pub(super) fn retype_new_container_owned_2m_pages(
    pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, container_page: PagePtr, pcid_allocator_page: PagePtr,
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
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().owning_container == child_container_ptr,
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == child_container_ptr,
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
        pages, child_container_ptr, container_page, Allocated2MPageState::AsContainer, Ghost(page_locks), Tracked(lctx), Tracked(container_page_lock_perm),
    );
    let ghost container_page_locks = page_locks.insert(container_head, TypedHeldLock { lock_id: pages.lock_id_by_index(container_head), mode: TypedLockMode::Write });
    let Tracked(pcid_allocator_perm) = page_array_retype_owned_2m_for_container(
        pages, child_container_ptr, pcid_allocator_page, Allocated2MPageState::AsPcidAllocator, Ghost(container_page_locks), Tracked(lctx), Tracked(pcid_allocator_page_lock_perm),
    );
    (Tracked(container_perm), Tracked(pcid_allocator_perm))
}

pub(super) fn prepare_new_container_backing_pages(
    pages: &mut PageLockedArray, container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr,
    thread_page: PagePtr, funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    Ghost(funding_indices): Ghost<Set<PageIndex>>, child_allocator_4k_ptr: RwLockPageAllocatorPtr, child_container_ptr: RwLockContainerPtr,
    child_depth: usize, Ghost(reference_krnl): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (LinkedList<PagePtr, ALLOCATOR_GLOBAL_POOL_MAJOR>, Tracked<PagePerm2m>, Tracked<PagePerm2m>, Ghost<Map<PageIndex, TypedHeldLock>>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        reference_krnl.inv(),
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
        funding_indices == funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(reference_krnl.pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page)),
        !funding_pages.to_set().contains(thread_page),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *old(pages), lctx, page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *old(pages), lctx, page_ptr2page_index(pcid_allocator_page),),
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
        final(pages).typed_lock_map_aligned(ret.4@, lctx.thread_id()),
        ret.4@.dom() == ret.3@.dom(),
        forall|index: PageIndex|
            #![trigger ret.4@.get(index)]
            #![trigger ret.4@.dom().contains(index)]
            index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> ret.4@.get(index) == ret.3@.get(index),
        typed_lock_map_contains_mode(ret.4@, page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.4@, page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        ret.3@.dom() == lctx.page_lock_map().dom(),
        forall|i: int|
            #![trigger funding_pages.spec_index(i)]
            0 <= i < funding_pages.len() ==> {
                &&& typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
            },
        forall|index: PageIndex|
            #![trigger ret.3@.get(index)]
            #![trigger ret.3@.dom().contains(index)]
            !funding_indices.contains(index) ==> ret.3@.get(index) == lctx.page_lock_map().get(index),
        ret.0.wf(),
        ret.0.view() == funding_pages,
        forall|page_ptr: PagePtr|
            #![trigger ret.0.view().contains(page_ptr)]
            ret.0.view().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& page_ptr_valid(page_ptr) ==> {
                    let node_addr = final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr();
                    &&& ret.0.map().dom().contains(node_addr)
                    &&& ret.0.map().spec_index(node_addr) == page_ptr
                }
            },
        ret.0.container_depth.view() == Some(child_depth),
        ret.0.minor.view() == Some(child_container_ptr),
        ret.1.view().is_init(),
        ret.1.view().addr() == container_page,
        ret.2.view().is_init(),
        ret.2.view().addr() == pcid_allocator_page,
        forall|page_ptr: PagePtr|
            #![trigger final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list]
            funding_pages.to_set().contains(page_ptr) ==> final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list,
        staged_4k_page_chain(*final(pages), funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *final(pages), lctx, page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *final(pages), lctx, page_ptr2page_index(pcid_allocator_page),),
        funding_indices.disjoint(page_2m_tail_indices(page_ptr2page_index(container_page))),
        funding_indices.disjoint(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))),
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
            #![trigger reference_krnl.pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(page_ptr2page_index(container_page)).contains(index)
                && !page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(index) && index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page)
                ==> final(pages).spec_index(index) == reference_krnl.pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger container_tail_lock_perms.dom().contains(index)]
            container_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == child_container_ptr,
        forall|index: PageIndex|
            #![trigger pcid_allocator_tail_lock_perms.dom().contains(index)]
            pcid_allocator_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == child_container_ptr,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_4k_ptr), state: FreePageAllocatorState::GlobalList,
                })
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().owning_container == child_container_ptr,
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
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
        ret.3@.get(page_ptr2page_index(allocator_4k_page)) == lctx.page_lock_map().get(page_ptr2page_index(allocator_4k_page)),
        ret.3@.get(page_ptr2page_index(allocator_2m_page)) == lctx.page_lock_map().get(page_ptr2page_index(allocator_2m_page)),
        ret.3@.get(page_ptr2page_index(allocator_1g_page)) == lctx.page_lock_map().get(page_ptr2page_index(allocator_1g_page)),
        ret.3@.get(page_ptr2page_index(scheduler_page)) == lctx.page_lock_map().get(page_ptr2page_index(scheduler_page)),
        ret.3@.get(page_ptr2page_index(cpu_set_page)) == lctx.page_lock_map().get(page_ptr2page_index(cpu_set_page)),
        ret.3@.get(page_ptr2page_index(process_page)) == lctx.page_lock_map().get(page_ptr2page_index(process_page)),
        ret.3@.get(page_ptr2page_index(pagetable_page)) == lctx.page_lock_map().get(page_ptr2page_index(pagetable_page)),
        ret.3@.get(page_ptr2page_index(l4_page)) == lctx.page_lock_map().get(page_ptr2page_index(l4_page)),
        ret.3@.get(page_ptr2page_index(thread_page)) == lctx.page_lock_map().get(page_ptr2page_index(thread_page)),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(process_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.3@, page_ptr2page_index(l4_page), TypedLockMode::Write),
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
    let thread_page_index = page_ptr2page_index(thread_page);
    set_new_container_owned_2m_page_tail_pair(
        pages, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, thread_page, child_container_ptr, Ghost(reference_krnl), Ghost(funding_pages), Ghost(funding_indices),
        Tracked(lctx), Tracked(funding_page_lock_perms), Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let (global_pool, Ghost(pool_page_locks)) = build_staged_4k_global_pool(
        pages, funding_page_count, funding_page_head, Ghost(funding_pages), Ghost(funding_indices), child_allocator_4k_ptr, child_container_ptr, child_depth,
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
        staged_4k_page_chain_page_ptrs_valid(reference_krnl.pg_arr, funding_pages);
        page_ptr_seq_indices_excludes_page(funding_pages, container_page); page_ptr_seq_indices_excludes_page(funding_pages, pcid_allocator_page);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_4k_page); page_ptr_seq_indices_excludes_page(funding_pages, allocator_2m_page);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_1g_page); page_ptr_seq_indices_excludes_page(funding_pages, scheduler_page);
        page_ptr_seq_indices_excludes_page(funding_pages, cpu_set_page); page_ptr_seq_indices_excludes_page(funding_pages, process_page);
        page_ptr_seq_indices_excludes_page(funding_pages, pagetable_page); page_ptr_seq_indices_excludes_page(funding_pages, l4_page);
        page_ptr_seq_indices_excludes_page(funding_pages, thread_page);
        page_array_wf_at(*pages, container_head); page_array_wf_at(*pages, pcid_allocator_head);
    }
    let ghost pages_before_2m_retype = *pages;
    let (Tracked(container_perm), Tracked(pcid_allocator_perm)) = retype_new_container_owned_2m_pages(
        pages, child_container_ptr, container_page, pcid_allocator_page, Ghost(pool_page_locks), Tracked(lctx), Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm),
    );
    proof {
        assert(staged_4k_page_chain(*pages, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_before_2m_retype, funding_pages);
            broadcast use page_ptr_sequence_index_in_equal_set; broadcast use page_ptr_sequence_index_in_mapped_set;
        };
    }
    let ghost prepared_page_locks = pool_page_locks.insert(container_head, TypedHeldLock { lock_id: pages.lock_id_by_index(container_head), mode: TypedLockMode::Write })
        .insert(pcid_allocator_head, TypedHeldLock { lock_id: pages.lock_id_by_index(pcid_allocator_head), mode: TypedLockMode::Write });
    (global_pool, Tracked(container_perm), Tracked(pcid_allocator_perm), Ghost(pool_page_locks), Ghost(prepared_page_locks))
}

pub(super) fn publish_new_container_process_and_pagetable(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr, child_pagetable_ptr: RwLockPageTableRoot,
    l4_page: PagePtr, root_pcid: Pcid, child_depth: usize, process_quota_4k: usize, container_head: PageIndex, pcid_allocator_head: PageIndex,
    Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(process_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>, Tracked(l4_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        old(krnl).prc_mp.perms_wf(),
        old(krnl).pt_mp.perms_wf(),
        old(krnl).dflt_pt.view().wf(),
        pei_valid(old(krnl).dflt_pt.view().kernel_l4_end),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, old(lctx).thread_id()),
        old(krnl).prc_mp.typed_lock_map_aligned(old(lctx).process_lock_map(), old(lctx).thread_id()),
        old(krnl).pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pcid_valid(root_pcid),
        root_pcid != KERNEL_DEFAULT_PCID,
        page_ptr_valid(child_process_ptr),
        page_ptr_valid(child_pagetable_ptr),
        page_ptr_valid(l4_page),
        child_process_ptr != child_pagetable_ptr,
        child_process_ptr != l4_page,
        child_pagetable_ptr != l4_page,
        !old(krnl).prc_mp.dom().contains(child_process_ptr),
        !old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(l4_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(child_process_ptr),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(child_pagetable_ptr),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(l4_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(child_process_ptr),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(child_pagetable_ptr),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(l4_page),),
    ensures
        final(krnl).prc_mp.spec_index(child_process_ptr).inv(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).pg_arr.typed_lock_map_aligned(ret.2@, final(lctx).thread_id()),
        ret.2@.dom() == page_locks.dom(),
        forall|index: PageIndex|
            #![trigger ret.2@.get(index)]
            #![trigger ret.2@.dom().contains(index)]
            index != page_ptr2page_index(l4_page) && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(child_process_ptr) ==> ret.2@.get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret.2@, page_ptr2page_index(l4_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.2@, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.2@, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        final(krnl).prc_mp.typed_lock_map_aligned(final(lctx).process_lock_map(), final(lctx).thread_id()),
        final(krnl).pt_mp.typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).prc_mp.perms_wf(),
        process_perms_wf(old(krnl).prc_mp) ==> process_perms_wf(final(krnl).prc_mp),
        final(krnl).pt_mp.perms_wf(),
        pagetable_perms_wf(old(krnl).pt_mp) ==> pagetable_perms_wf(final(krnl).pt_mp),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx),),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx),),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(child_process_ptr) && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(l4_page) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: child_pagetable_ptr, table_type: PT_TYPE } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().owning_container == child_container_ptr,
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom() =~= old(krnl).prc_mp.dom().insert(child_process_ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(ptr)]
            old(krnl).prc_mp.dom().contains(ptr) ==> final(krnl).prc_mp.spec_index(ptr) == old(krnl).prc_mp.spec_index(ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().container_depth == child_depth,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().parent is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().depth == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().cr3 == l4_page,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().iommu_cr3 is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pcid == root_pcid,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pcid == root_pcid,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().iommu_table is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().owned_pci_functions.view().is_empty(),
        !final(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_4k == process_quota_4k,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().owned_threads.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().parent_linkedlist_node.is_init(),
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().uppertree_seq.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().subtree_set.view().is_empty(),
        final(krnl).pt_mp.dom() =~= old(krnl).pt_mp.dom().insert(child_pagetable_ptr),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(krnl).pt_mp.spec_index(ptr)]
            old(krnl).pt_mp.dom().contains(ptr) ==> final(krnl).pt_mp.spec_index(ptr) == old(krnl).pt_mp.spec_index(ptr),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().is_empty(),
        !final(krnl).pt_mp.spec_index(child_pagetable_ptr).being_killed(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().proc_ptr == child_process_ptr,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().pcid is Some,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().pcid_value() == root_pcid,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().cr3 == l4_page,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end == old(krnl).dflt_pt.view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().page_closure() == set![l4_page],
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(child_process_ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            ptr != child_process_ptr ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(child_pagetable_ptr),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            ptr != child_pagetable_ptr ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write,),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.spec_index(child_process_ptr).write_lock_perm_match(&ret.0.view()),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
{
    let process_index = page_ptr2page_index(child_process_ptr);
    let pagetable_index = page_ptr2page_index(child_pagetable_ptr);
    let l4_index = page_ptr2page_index(l4_page);
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert({
            &&& process_index != pagetable_index
            &&& process_index != l4_index
            &&& pagetable_index != l4_index
        });
    }
    let default_pt = krnl.dflt_pt.borrow();
    let Tracked(l4_page_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, l4_page, Allocated4KPageState::PageTable { pagetable_root: child_pagetable_ptr, table_type: PT_TYPE }, Ghost(page_locks), Tracked(&*lctx), Tracked(l4_page_lock_perm));
    let ghost l4_page_locks = page_locks.insert(l4_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(l4_index), mode: TypedLockMode::Write });
    let (l4_ptr, Tracked(mut l4_perm)) = page_perm_to_page_map(l4_page, Tracked(l4_page_perm));
    default_pt.copy_kernel_entries_to_unpublished_root(l4_ptr, Tracked(&mut l4_perm));
    proof { assert(default_pt.kernel_entries.view().len() == default_pt.kernel_l4_end) by { default_pt.kernel_entries_wf_len_at(); }; }
    let pagetable_value = PageTable::<PT_TYPE>::new(Some(root_pcid), Ghost(default_pt.kernel_entries.view()), l4_ptr, Tracked(l4_perm), default_pt.kernel_l4_end, child_process_ptr);
    let Tracked(pagetable_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, child_pagetable_ptr, Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE }, Ghost(l4_page_locks), Tracked(&*lctx), Tracked(pagetable_page_lock_perm));
    let ghost pagetable_page_locks = l4_page_locks.insert(pagetable_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pagetable_index), mode: TypedLockMode::Write });
    let Tracked(child_pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(child_pagetable_ptr, pagetable_value, Tracked(pagetable_perm), Tracked(&mut *lctx));
    let mut process_value = Process::new_fresh(child_process_ptr, root_pcid, child_pagetable_ptr, child_depth, 0);
    process_value.quota_4k = process_quota_4k;
    let process_rodata = ReadOnlyNode::new(
        ProcessRO {
            owning_container: child_container_ptr, container_depth: child_depth, parent: None, depth: 0, pagetable: child_pagetable_ptr,
            cr3: l4_ptr, iommu_cr3: None, pcid: root_pcid,
        },
        Ghost(child_process_ptr),
    );
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(Seq::empty()), subtree_set: Ghost(Set::empty()), owned_pci_functions: Ghost(Set::empty()) };
    let Tracked(process_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, child_process_ptr, Allocated4KPageState::AsProcess, Ghost(pagetable_page_locks), Tracked(&*lctx), Tracked(process_page_lock_perm));
    let ghost process_page_locks = pagetable_page_locks.insert(process_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(process_index), mode: TypedLockMode::Write });
    let Tracked(child_process_lock_perm) =
        krnl.retype_page_to_process_and_insert(child_process_ptr, process_value, process_rodata, process_ghost, Tracked(process_perm), Tracked(&mut *lctx),);
    proof {
        assert(!old(lctx).process_lock_map().dom().contains(child_process_ptr,)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx),)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(!old(lctx).pagetable_lock_map().dom().contains(child_pagetable_ptr,)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx),)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    (Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Ghost(process_page_locks))
}

pub(super) fn publish_new_container_allocator(
    pages: &mut PageLockedArray, allocator_map: &mut PageAllocatorUnLockedMap, child_container_ptr: RwLockContainerPtr, allocator_page: PagePtr,
    allocator_state: Allocated4KPageState, allocator_value: PageAllocator, Ghost(quota_lock_map): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
    Ghost(cache_lock_map): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
    Ghost(global_pool_lock_map): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(allocator_page_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(allocator_map).perms_wf(),
        old(pages).typed_lock_map_aligned(page_locks, lctx.thread_id()),
        old(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        old(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        old(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        allocator_value.inv(),
        allocator_state is As4KAllocator || allocator_state is As2MAllocator || allocator_state is As1GAllocator,
        !allocator_value.quota.locked(),
        !allocator_value.global_pool.locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked()]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked_by_thread(lctx.thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().rlocked_by_thread(lctx.thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_value.cpu_caches.spec_index(cpu_id).view().locked(),
        !old(allocator_map).dom().contains(allocator_page),
        page_ptr_valid(allocator_page),
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_page), TypedLockMode::Write),
        allocator_page_lock_perm.state() is WriteLock,
        allocator_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(allocator_page),).view().locking_thread()->Write_lock_id,
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(allocator_map).perms_wf(),
        allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*final(allocator_map)),
        final(pages).typed_lock_map_aligned(page_locks.insert(page_ptr2page_index(allocator_page), TypedHeldLock { lock_id: final(pages).lock_id_by_index(page_ptr2page_index(allocator_page)), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        final(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        final(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(allocator_page),),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        final(pages).spec_index(page_ptr2page_index(allocator_page)).view().view().state == (PageState::Allocated4k { state: allocator_state }),
        final(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().owning_container == child_container_ptr,
        allocator_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(allocator_page),).view().locking_thread()->Write_lock_id,
        final(allocator_map).dom() =~= old(allocator_map).dom().insert(allocator_page),
        final(allocator_map).spec_index(allocator_page) == allocator_value,
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(allocator_map).spec_index(ptr)]
            old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
{
    let Tracked(allocator_perm) =
        page_array_retype_owned_4k_for_container(pages, child_container_ptr, allocator_page, allocator_state, Ghost(page_locks), Tracked(lctx), Tracked(allocator_page_lock_perm));
    page_allocator_map_insert_new(allocator_map, allocator_page, allocator_value, Ghost(quota_lock_map), Ghost(cache_lock_map), Ghost(global_pool_lock_map), Tracked(lctx), Tracked(allocator_perm));
}

pub(super) fn publish_new_container_allocators(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    allocator_4k_value: PageAllocator, allocator_2m_value: PageAllocator, allocator_1g_value: PageAllocator, container_head: PageIndex,
    pcid_allocator_head: PageIndex, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: Ghost<Map<PageIndex, TypedHeldLock>>)
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        allocator_perms_wf(old(krnl).allc_4k_mp),
        allocator_perms_wf(old(krnl).allc_2m_mp),
        allocator_perms_wf(old(krnl).allc_1g_mp),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, lctx.thread_id()),
        old(krnl).allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id()),
        old(krnl).allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id()),
        old(krnl).allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id()),
        old(krnl).allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id()),
        old(krnl).allc_2m_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id()),
        old(krnl).allc_2m_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id()),
        old(krnl).allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id()),
        old(krnl).allc_1g_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_1g_lock_map(), lctx.thread_id()),
        old(krnl).allc_1g_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        allocator_4k_value.inv(),
        allocator_2m_value.inv(),
        allocator_1g_value.inv(),
        !allocator_4k_value.quota.locked(),
        !allocator_2m_value.quota.locked(),
        !allocator_1g_value.quota.locked(),
        !allocator_4k_value.global_pool.locked(),
        !allocator_2m_value.global_pool.locked(),
        !allocator_1g_value.global_pool.locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_4k_value.cpu_caches.spec_index(cpu_id).view().locked()]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_4k_value.cpu_caches.spec_index(cpu_id).view().locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_2m_value.cpu_caches.spec_index(cpu_id).view().locked()]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_2m_value.cpu_caches.spec_index(cpu_id).view().locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_1g_value.cpu_caches.spec_index(cpu_id).view().locked()]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_1g_value.cpu_caches.spec_index(cpu_id).view().locked(),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr2page_index(allocator_4k_page) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(allocator_4k_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(allocator_2m_page) != page_ptr2page_index(allocator_1g_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_2m_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_1g_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, lctx, pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(allocator_4k_page),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(allocator_2m_page),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(allocator_1g_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(allocator_4k_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(allocator_2m_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(allocator_1g_page),),
    ensures
        final(krnl).pg_arr.typed_lock_map_aligned(ret@, lctx.thread_id()),
        ret@.dom() == page_locks.dom(),
        forall|index: PageIndex|
            #![trigger ret@.get(index)]
            #![trigger ret@.dom().contains(index)]
            index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page) && index != page_ptr2page_index(allocator_1g_page) ==> ret@.get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret@, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret@, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret@, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        final(krnl).allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id()),
        final(krnl).allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id()),
        final(krnl).allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id()),
        final(krnl).allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id()),
        final(krnl).allc_2m_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id()),
        final(krnl).allc_2m_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id()),
        final(krnl).allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id()),
        final(krnl).allc_1g_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_1g_lock_map(), lctx.thread_id()),
        final(krnl).allc_1g_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_1g_mp.perms_wf(),
        allocator_perms_wf(final(krnl).allc_4k_mp),
        allocator_perms_wf(final(krnl).allc_2m_mp),
        allocator_perms_wf(final(krnl).allc_1g_mp),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page) && index != page_ptr2page_index(allocator_1g_page) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        forall|index: PageIndex|
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index) && old(krnl).pg_arr.spec_index(index).view().view().state is Merged2m ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().owning_container == child_container_ptr,
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        final(krnl).allc_4k_mp.dom() =~= old(krnl).allc_4k_mp.dom().insert(allocator_4k_page),
        final(krnl).allc_2m_mp.dom() =~= old(krnl).allc_2m_mp.dom().insert(allocator_2m_page),
        final(krnl).allc_1g_mp.dom() =~= old(krnl).allc_1g_mp.dom().insert(allocator_1g_page),
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page) == allocator_4k_value,
        final(krnl).allc_2m_mp.spec_index(allocator_2m_page) == allocator_2m_value,
        final(krnl).allc_1g_mp.spec_index(allocator_1g_page) == allocator_1g_value,
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(krnl).allc_4k_mp.spec_index(ptr)]
            old(krnl).allc_4k_mp.dom().contains(ptr) ==> final(krnl).allc_4k_mp.spec_index(ptr) == old(krnl).allc_4k_mp.spec_index(ptr),
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(krnl).allc_2m_mp.spec_index(ptr)]
            old(krnl).allc_2m_mp.dom().contains(ptr) ==> final(krnl).allc_2m_mp.spec_index(ptr) == old(krnl).allc_2m_mp.spec_index(ptr),
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(krnl).allc_1g_mp.spec_index(ptr)]
            old(krnl).allc_1g_mp.dom().contains(ptr) ==> final(krnl).allc_1g_mp.spec_index(ptr) == old(krnl).allc_1g_mp.spec_index(ptr),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, lctx, pcid_allocator_head,),
{
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let ghost allocator_4k_quota_lock_map = lctx.allocator_quota_4k_lock_map();
    let ghost allocator_4k_cache_lock_map = lctx.allocator_cache_4k_lock_map();
    let ghost allocator_4k_global_pool_lock_map = lctx.allocator_global_pool_4k_lock_map();
    let ghost allocator_2m_quota_lock_map = lctx.allocator_quota_2m_lock_map();
    let ghost allocator_2m_cache_lock_map = lctx.allocator_cache_2m_lock_map();
    let ghost allocator_2m_global_pool_lock_map = lctx.allocator_global_pool_2m_lock_map();
    let ghost allocator_1g_quota_lock_map = lctx.allocator_quota_1g_lock_map();
    let ghost allocator_1g_cache_lock_map = lctx.allocator_cache_1g_lock_map();
    let ghost allocator_1g_global_pool_lock_map = lctx.allocator_global_pool_1g_lock_map();
    proof {
        assert({
            &&& krnl.allc_4k_mp.perms_wf()
            &&& krnl.allc_2m_mp.perms_wf()
            &&& krnl.allc_1g_mp.perms_wf()
        }) by { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_map(krnl.allc_1g_mp); };
    }
    publish_new_container_allocator(
        &mut krnl.pg_arr, &mut krnl.allc_4k_mp, child_container_ptr, allocator_4k_page, Allocated4KPageState::As4KAllocator, allocator_4k_value,
        Ghost(allocator_4k_quota_lock_map), Ghost(allocator_4k_cache_lock_map), Ghost(allocator_4k_global_pool_lock_map),
        Ghost(page_locks), Tracked(lctx), Tracked(allocator_4k_page_lock_perm),
    );
    let ghost allocator_4k_page_locks = page_locks.insert(allocator_4k_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(allocator_4k_index), mode: TypedLockMode::Write });
    publish_new_container_allocator(
        &mut krnl.pg_arr, &mut krnl.allc_2m_mp, child_container_ptr, allocator_2m_page, Allocated4KPageState::As2MAllocator, allocator_2m_value,
        Ghost(allocator_2m_quota_lock_map), Ghost(allocator_2m_cache_lock_map), Ghost(allocator_2m_global_pool_lock_map),
        Ghost(allocator_4k_page_locks), Tracked(lctx), Tracked(allocator_2m_page_lock_perm),
    );
    let ghost allocator_2m_page_locks = allocator_4k_page_locks.insert(allocator_2m_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(allocator_2m_index), mode: TypedLockMode::Write });
    publish_new_container_allocator(
        &mut krnl.pg_arr, &mut krnl.allc_1g_mp, child_container_ptr, allocator_1g_page, Allocated4KPageState::As1GAllocator, allocator_1g_value,
        Ghost(allocator_1g_quota_lock_map), Ghost(allocator_1g_cache_lock_map), Ghost(allocator_1g_global_pool_lock_map),
        Ghost(allocator_2m_page_locks), Tracked(lctx), Tracked(allocator_1g_page_lock_perm),
    );
    Ghost(allocator_2m_page_locks.insert(allocator_1g_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(allocator_1g_index), mode: TypedLockMode::Write }))
}

pub(super) fn publish_new_container_scheduler(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_scheduler_ptr: RwLockSchedulerPtr, scheduler_page: PagePtr,
    scheduler_value: Scheduler, container_head: PageIndex, pcid_allocator_head: PageIndex, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: Ghost<Map<PageIndex, TypedHeldLock>>)
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        old(krnl).sched_mp.perms_wf(),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, lctx.thread_id()),
        old(krnl).sched_mp.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        scheduler_value.inv(),
        forall|cpu_id: CpuId| #![trigger scheduler_value.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> !scheduler_value.shards.spec_index(cpu_id).view().locked(),
        child_scheduler_ptr == scheduler_page,
        !old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        page_ptr_valid(scheduler_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == lctx.thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, lctx, pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(scheduler_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(scheduler_page),),
    ensures
        final(krnl).sched_mp.spec_index(child_scheduler_ptr).inv(),
        final(krnl).pg_arr.typed_lock_map_aligned(ret@, lctx.thread_id()),
        ret@.dom() == page_locks.dom(),
        forall|index: PageIndex|
            #![trigger ret@.get(index)]
            #![trigger ret@.dom().contains(index)]
            index != page_ptr2page_index(scheduler_page) ==> ret@.get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret@, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        final(krnl).sched_mp.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).sched_mp.perms_wf(),
        scheduler_perms_wf(old(krnl).sched_mp) ==> scheduler_perms_wf(final(krnl).sched_mp),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(scheduler_page),),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().owning_container == child_container_ptr,
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().locking_thread()->Write_lock_id,
        final(krnl).sched_mp.dom() =~= old(krnl).sched_mp.dom().insert(child_scheduler_ptr),
        final(krnl).sched_mp.spec_index(child_scheduler_ptr) == scheduler_value,
        forall|ptr: RwLockSchedulerPtr|
            #![trigger final(krnl).sched_mp.spec_index(ptr)]
            old(krnl).sched_mp.dom().contains(ptr) ==> final(krnl).sched_mp.spec_index(ptr) == old(krnl).sched_mp.spec_index(ptr),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, lctx, pcid_allocator_head,),
{
    let Tracked(scheduler_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, scheduler_page, Allocated4KPageState::AsScheduler, Ghost(page_locks), Tracked(lctx), Tracked(scheduler_page_lock_perm));
    let ghost scheduler_page_locks = page_locks.insert(page_ptr2page_index(scheduler_page), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(scheduler_page)), mode: TypedLockMode::Write });
    scheduler_map_insert_new_4k(&mut krnl.sched_mp, child_scheduler_ptr, scheduler_value, Tracked(scheduler_perm), Tracked(lctx));
    Ghost(scheduler_page_locks)
}

pub(super) fn publish_new_container_cpu_set(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_cpu_set_ptr: RwLockCpuSetPtr, cpu_set_page: PagePtr, cpu_set_value: CpuSet,
    container_head: PageIndex, pcid_allocator_head: PageIndex, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>, Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        old(krnl).cpu_set_mp.perms_wf(),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, old(lctx).thread_id()),
        old(krnl).cpu_set_mp.typed_lock_map_aligned(old(lctx).cpu_set_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        cpu_set_value.inv(),
        child_cpu_set_ptr == cpu_set_page,
        !old(krnl).cpu_set_mp.dom().contains(child_cpu_set_ptr),
        page_ptr_valid(cpu_set_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        cpu_set_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(cpu_set_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(cpu_set_page),),
    ensures
        final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).pg_arr.typed_lock_map_aligned(ret.1@, final(lctx).thread_id()),
        ret.1@.dom() == page_locks.dom(),
        forall|index: PageIndex|
            #![trigger ret.1@.get(index)]
            #![trigger ret.1@.dom().contains(index)]
            index != page_ptr2page_index(cpu_set_page) ==> ret.1@.get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret.1@, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        final(krnl).cpu_set_mp.typed_lock_map_aligned(final(lctx).cpu_set_lock_map(), final(lctx).thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).cpu_set_mp.perms_wf(),
        cpu_set_perms_wf(old(krnl).cpu_set_mp) ==> cpu_set_perms_wf(final(krnl).cpu_set_mp),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(cpu_set_page),),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map().dom() == old(lctx).cpu_set_lock_map().dom().insert(child_cpu_set_ptr),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), child_cpu_set_ptr, TypedLockMode::Write),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(lctx).cpu_set_lock_map().get(ptr)]
            ptr != child_cpu_set_ptr ==> final(lctx).cpu_set_lock_map().get(ptr) == old(lctx).cpu_set_lock_map().get(ptr),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().owning_container == child_container_ptr,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().locking_thread()->Write_lock_id,
        final(krnl).cpu_set_mp.dom() =~= old(krnl).cpu_set_mp.dom().insert(child_cpu_set_ptr),
        final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).view() == cpu_set_value,
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(krnl).cpu_set_mp.spec_index(ptr)]
            old(krnl).cpu_set_mp.dom().contains(ptr) ==> final(krnl).cpu_set_mp.spec_index(ptr) == old(krnl).cpu_set_mp.spec_index(ptr),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).locking_thread()->Write_lock_id,
{
    let Tracked(cpu_set_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, cpu_set_page, Allocated4KPageState::AsCpuSet, Ghost(page_locks), Tracked(&*lctx), Tracked(cpu_set_page_lock_perm));
    let ghost cpu_set_page_locks = page_locks.insert(page_ptr2page_index(cpu_set_page), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(cpu_set_page)), mode: TypedLockMode::Write });
    let cpu_set_lock_perm = cpu_set_map_insert_new_4k(&mut krnl.cpu_set_mp, child_cpu_set_ptr, cpu_set_value, Tracked(cpu_set_perm), Tracked(&mut *lctx));
    (cpu_set_lock_perm, Ghost(cpu_set_page_locks))
}

pub(super) fn publish_new_container_pcid_allocator_and_container(
    krnl: &mut KernelK, child_pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid_allocator_value: PcidAllocator,
    child_container_ptr: RwLockContainerPtr, container_value: Container, container_rodata: ReadOnlyNode<ContainerRO>, container_ghost: ContainerGhost,
    Ghost(allocator_4k_page): Ghost<PagePtr>, Ghost(allocator_2m_page): Ghost<PagePtr>, Ghost(allocator_1g_page): Ghost<PagePtr>, Ghost(scheduler_page): Ghost<PagePtr>,
    Ghost(cpu_set_page): Ghost<PagePtr>, Ghost(child_process_ptr): Ghost<PagePtr>, Ghost(child_pagetable_ptr): Ghost<PagePtr>, Ghost(l4_page): Ghost<PagePtr>,
    Ghost(bootstrap_seq): Ghost<Seq<PagePtr>>, Ghost(funding_pages): Ghost<Seq<PagePtr>>, Ghost(funding_indices): Ghost<Set<PageIndex>>,
    Ghost(pool_page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Ghost(cpu_set_page_locks): Ghost<Map<PageIndex, TypedHeldLock>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pcid_allocator_perm): Tracked<PagePerm2m>, Tracked(container_perm): Tracked<PagePerm2m>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).pcid_allc_mp.perms_wf(),
        old(krnl).ctn_mp.perms_wf(),
        old(krnl).cpu_offline_mp.perms_wf(),
        old(krnl).pcid_allc_mp.typed_lock_map_aligned(old(lctx).pcid_allocator_lock_map(), old(lctx).thread_id()),
        old(krnl).ctn_mp.typed_lock_map_aligned(old(lctx).container_lock_map(), old(lctx).thread_id()),
        old(krnl).cpu_offline_mp.typed_flag_lock_map_aligned(old(lctx).cpu_offline_flag_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pcid_allocator_value.inv(),
        container_value.inv(),
        !old(krnl).pcid_allc_mp.dom().contains(child_pcid_allocator_ptr),
        !old(krnl).ctn_mp.dom().contains(child_container_ptr),
        !old(krnl).cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child_container_ptr)),
        page_ptr_2m_valid(child_container_ptr),
        pcid_allocator_perm.is_init(),
        pcid_allocator_perm.addr() == child_pcid_allocator_ptr,
        container_perm.is_init(),
        container_perm.addr() == child_container_ptr,
        bootstrap_seq == seq![allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, child_process_ptr, child_pagetable_ptr, l4_page],
        bootstrap_seq.no_duplicates(),
        page_ptr2page_index(child_container_ptr) != page_ptr2page_index(child_pcid_allocator_ptr),
        page_ptr2page_index(allocator_2m_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(allocator_1g_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(allocator_1g_page) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(scheduler_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(scheduler_page) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(scheduler_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(cpu_set_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(cpu_set_page) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(cpu_set_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(cpu_set_page) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(child_process_ptr) != page_ptr2page_index(allocator_1g_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(cpu_set_page),
        page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(cpu_set_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(child_process_ptr),
        page_ptr2page_index(l4_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(l4_page) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(cpu_set_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(child_process_ptr),
        page_ptr2page_index(l4_page) != page_ptr2page_index(child_pagetable_ptr),
        page_ptr_valid(allocator_4k_page) && page_ptr_valid(allocator_2m_page) && page_ptr_valid(allocator_1g_page) && page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page) && page_ptr_valid(child_process_ptr) && page_ptr_valid(child_pagetable_ptr) && page_ptr_valid(l4_page),
        funding_indices == funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set(),
        funding_pages.no_duplicates(),
        forall|i: int| #![trigger page_ptr_valid(funding_pages.spec_index(i))] 0 <= i < funding_pages.len() ==> page_ptr_valid(funding_pages.spec_index(i)),
        pool_page_locks.dom() == old(lctx).page_lock_map().dom(),
        forall|i: int|
            #![trigger funding_pages.spec_index(i)]
            0 <= i < funding_pages.len() ==> {
                &&& typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
            },
        forall|index: PageIndex|
            #![trigger pool_page_locks.get(index)]
            #![trigger pool_page_locks.dom().contains(index)]
            !funding_indices.contains(index) ==> pool_page_locks.get(index) == old(lctx).page_lock_map().get(index),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_container_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_pcid_allocator_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(l4_page), TypedLockMode::Write),
        cpu_set_page_locks.dom() == pool_page_locks.dom(),
        forall|index: PageIndex|
            #![trigger cpu_set_page_locks.get(index)]
            #![trigger cpu_set_page_locks.dom().contains(index)]
            index != page_ptr2page_index(child_container_ptr) && index != page_ptr2page_index(child_pcid_allocator_ptr) && index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page)
                && index != page_ptr2page_index(allocator_1g_page) && index != page_ptr2page_index(scheduler_page) && index != page_ptr2page_index(cpu_set_page) && index != page_ptr2page_index(child_process_ptr)
                && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(l4_page) ==> cpu_set_page_locks.get(index) == pool_page_locks.get(index),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_container_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_pcid_allocator_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr).inv(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).pcid_allc_mp.typed_lock_map_aligned(final(lctx).pcid_allocator_lock_map(), final(lctx).thread_id()),
        final(krnl).ctn_mp.typed_lock_map_aligned(final(lctx).container_lock_map(), final(lctx).thread_id()),
        final(krnl).cpu_offline_mp.typed_flag_lock_map_aligned(final(lctx).cpu_offline_flag_lock_map(), final(lctx).thread_id()),
        *final(krnl) == (KernelK { pcid_allc_mp: final(krnl).pcid_allc_mp, ctn_mp: final(krnl).ctn_mp, cpu_offline_mp: final(krnl).cpu_offline_mp, ..*old(krnl) }),
        final(krnl).cpu_offline_mp.perms_wf(),
        final(krnl).cpu_offline_mp.dom() =~= old(krnl).cpu_offline_mp.dom().insert(cpu_offline_flags_ptr(child_container_ptr)),
        forall|ptr: RwLockCpuOfflineFlagsPtr|
            #![trigger final(krnl).cpu_offline_mp.spec_index(ptr)]
            old(krnl).cpu_offline_mp.dom().contains(ptr) ==> final(krnl).cpu_offline_mp.spec_index(ptr) == old(krnl).cpu_offline_mp.spec_index(ptr),
        final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).inv(),
        final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).owning_container.view() == child_container_ptr,
        forall|cpu_id: CpuId|
            #![trigger final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id)]
            index_valid(NUM_CPUS, cpu_id) ==> {
                &&& !final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id).view().locked()
                &&& final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id).view().view().index() == (cpu_offline_flags_ptr(child_container_ptr), cpu_id)
                &&& !final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id).view().view().requested
            },
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(krnl).pcid_allc_mp.perms_wf(),
        pcid_allocator_perms_wf(old(krnl).pcid_allc_mp) ==> pcid_allocator_perms_wf(final(krnl).pcid_allc_mp),
        final(krnl).ctn_mp.perms_wf(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).page_lock_map() == cpu_set_page_locks,
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(child_pcid_allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(lctx).pcid_allocator_lock_map().get(ptr)]
            #![trigger final(lctx).pcid_allocator_lock_map().dom().contains(ptr)]
            ptr != child_pcid_allocator_ptr ==> final(lctx).pcid_allocator_lock_map().get(ptr) == old(lctx).pcid_allocator_lock_map().get(ptr),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(child_container_ptr),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger final(lctx).container_lock_map().dom().contains(ptr)]
            ptr != child_container_ptr ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(krnl).pcid_allc_mp.dom() =~= old(krnl).pcid_allc_mp.dom().insert(child_pcid_allocator_ptr),
        final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr).view() == pcid_allocator_value,
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(krnl).pcid_allc_mp.spec_index(ptr)]
            old(krnl).pcid_allc_mp.dom().contains(ptr) ==> final(krnl).pcid_allc_mp.spec_index(ptr) == old(krnl).pcid_allc_mp.spec_index(ptr),
        final(krnl).ctn_mp.dom() =~= old(krnl).ctn_mp.dom().insert(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).is_init(),
        !final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view() == container_value,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata() == container_rodata,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost() == container_ghost,
        forall|ptr: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(ptr)]
            old(krnl).ctn_mp.dom().contains(ptr) ==> final(krnl).ctn_mp.spec_index(ptr) == old(krnl).ctn_mp.spec_index(ptr),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr,).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), child_pcid_allocator_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write,),
{
    hide(Seq::contains);
    let child_pcid_allocator_lock_perm = pcid_allocator_map_insert_new_2m(&mut krnl.pcid_allc_mp, child_pcid_allocator_ptr, pcid_allocator_value, Tracked(pcid_allocator_perm), Tracked(&mut *lctx));
    let child_container_lock_perm = container_map_insert_new_2m(&mut krnl.ctn_mp, child_container_ptr, container_value, container_rodata, container_ghost, Tracked(container_perm), Tracked(&mut *lctx));
    let flags_value = CpuOfflineFlags::new_empty(Ghost(child_container_ptr), Ghost(cpu_offline_flags_ptr(child_container_ptr)));
    krnl.cpu_offline_mp.retype_container_page_tail_and_insert(&krnl.ctn_mp, child_container_ptr, flags_value, Tracked(&*lctx));
    proof {
        assert(krnl.cpu_offline_mp.typed_flag_lock_map_aligned(lctx.cpu_offline_flag_lock_map(), lctx.thread_id())) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        let container_head = page_ptr2page_index(child_container_ptr);
        let pcid_allocator_head = page_ptr2page_index(child_pcid_allocator_ptr);
        lctx.enter_kernel_view_release();
        rekey_published_4k_page_chain(lctx, funding_pages, funding_pages.len() as int, pool_page_locks);
        lctx.update_lock_id(KernelObjId::Page(container_head), pool_page_locks.index(container_head).lock_id, cpu_set_page_locks.index(container_head).lock_id);
        lctx.update_lock_id(KernelObjId::Page(pcid_allocator_head), pool_page_locks.index(pcid_allocator_head).lock_id, cpu_set_page_locks.index(pcid_allocator_head).lock_id);
        page_ptr_seq_indices_no_duplicates(bootstrap_seq);
        page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 0); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 1); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 2);
        page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 3); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 4); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 5);
        page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 6); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 7);
        rekey_published_4k_page_chain(lctx, bootstrap_seq, 8, cpu_set_page_locks);
    }
    (child_pcid_allocator_lock_perm, child_container_lock_perm)
}

pub(super) fn link_new_container_into_tree(
    containers: &mut ContainerLockedMap, root_container: RwLockContainerPtr, parent_container_ptr: RwLockContainerPtr,
    child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr, child_scheduler_ptr: RwLockSchedulerPtr,
    child_pcid_allocator_ptr: RwLockPcidAllocatorPtr, child_cpu_set_ptr: RwLockCpuSetPtr, child_allocator_4k_ptr: RwLockPageAllocatorPtr,
    child_allocator_2m_ptr: RwLockPageAllocatorPtr, child_allocator_1g_ptr: RwLockPageAllocatorPtr, child_depth: usize,
    thread_page: PagePtr, Ghost(child_uppers): Ghost<Seq<RwLockContainerPtr>>, Ghost(moved_pages): Ghost<Set<PagePtr>>,
    Ghost(base_containers): Ghost<ContainerLockedMap>, Ghost(base_pages): Ghost<PageLockedArray>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
)
    requires
        container_perms_wf(base_containers),
        container_tree_wf(root_container, base_containers),
        container_pages_wf(base_pages, base_containers),
        base_containers.dom().contains(parent_container_ptr),
        !base_containers.dom().contains(child_container_ptr),
        base_containers.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(containers).perms_wf(),
        old(containers).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),),
        old(containers).dom() == base_containers.dom().insert(child_container_ptr),
        forall|container_ptr: RwLockContainerPtr|
            #![trigger old(containers).spec_index(container_ptr)]
            base_containers.dom().contains(container_ptr) ==> old(containers).spec_index(container_ptr) == base_containers.spec_index(container_ptr),
        old(containers).spec_index(child_container_ptr).is_init(),
        old(containers).spec_index(child_container_ptr).inv(),
        !old(containers).spec_index(child_container_ptr).being_killed(),
        old(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.is_init(),
        old(containers).spec_index(child_container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty(),
        old(containers).spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        old(containers).spec_index(child_container_ptr).view_rodata().view().depth == child_depth,
        old(containers).spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().pcid_allocator == child_pcid_allocator_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_2m == child_allocator_2m_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_1g == child_allocator_1g_ptr,
        old(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq.view() == child_uppers,
        old(containers).spec_index(child_container_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty(),
        old(containers).spec_index(child_container_ptr).view().owned_pages.view() == moved_pages,
        old(containers).spec_index(child_container_ptr).view().root_process == child_process_ptr,
        !old(containers).spec_index(child_container_ptr).view().zombie,
        old(containers).spec_index(child_container_ptr).view_ghost().owned_processes.view() == set![child_process_ptr],
        child_depth == base_containers.spec_index(parent_container_ptr).view_rodata().view().depth + 1,
        child_uppers == base_containers.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        child_uppers.no_duplicates(),
        child_uppers.to_set().subset_of(base_containers.dom()),
        !child_uppers.to_set().contains(child_container_ptr),
        moved_pages.subset_of(base_containers.spec_index(parent_container_ptr).view().owned_pages.view()),
        !moved_pages.contains(thread_page),
        base_containers.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        typed_lock_map_contains_mode(lctx.container_lock_map(), parent_container_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(lctx.container_lock_map(), child_container_ptr, TypedLockMode::Write,),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == lctx.thread_id(),
        parent_container_lock_perm.lock_id() == old(containers).spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == lctx.thread_id(),
        child_container_lock_perm.lock_id() == old(containers).spec_index(child_container_ptr).locking_thread()->Write_lock_id,
    ensures
        final(containers).spec_index(parent_container_ptr).inv(),
        final(containers).spec_index(child_container_ptr).inv(),
        final(containers).perms_wf(),
        final(containers).dom() == old(containers).dom(),
        final(containers).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),),
        final(containers).spec_index(child_container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty(),
        !final(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.is_init(),
        final(containers).spec_index(child_container_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(containers).spec_index(ptr).view_ghost().uppertree_seq]
            #![trigger base_containers.spec_index(ptr).view_ghost().uppertree_seq]
            base_containers.dom().contains(ptr) ==> final(containers).spec_index(ptr).view_ghost().uppertree_seq == base_containers.spec_index(ptr).view_ghost().uppertree_seq,
        forall|ptr: RwLockContainerPtr|
            #![trigger child_uppers.contains(ptr)]
            child_uppers.contains(ptr) ==> final(containers).spec_index(ptr).view_ghost().subtree_set.view() == base_containers.spec_index(ptr).view_ghost().subtree_set.view().insert(child_container_ptr),
        forall|ptr: RwLockContainerPtr|
            #![trigger base_containers.dom().contains(ptr)]
            base_containers.dom().contains(ptr) && !child_uppers.contains(ptr) ==> final(containers).spec_index(ptr).view_ghost().subtree_set == base_containers.spec_index(ptr).view_ghost().subtree_set,
        final(containers).spec_index(parent_container_ptr).view().children.view() == base_containers.spec_index(parent_container_ptr).view().children.view().push(child_container_ptr),
        final(containers).spec_index(parent_container_ptr).view().children.map().dom().contains(final(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.addr()),
        final(containers).spec_index(parent_container_ptr).view().children.map().spec_index(final(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.addr()) == child_container_ptr,
        forall|node_addr: usize|
            #![trigger base_containers.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr)]
            base_containers.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr) ==> {
                &&& final(containers).spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr)
                &&& final(containers).spec_index(parent_container_ptr).view().children.map().spec_index(node_addr) == base_containers.spec_index(parent_container_ptr).view().children.map().spec_index(node_addr)
            },
        final(containers).spec_index(parent_container_ptr).view().owned_pages.view() == base_containers.spec_index(parent_container_ptr).view().owned_pages.view().difference(moved_pages),
        final(containers).spec_index(parent_container_ptr).view() == (Container {
            children: final(containers).spec_index(parent_container_ptr).view().children,
            owned_pages: final(containers).spec_index(parent_container_ptr).view().owned_pages,
            ..base_containers.spec_index(parent_container_ptr).view()
        }),
        final(containers).spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        final(containers).spec_index(child_container_ptr).view().owned_pages.view() == moved_pages,
        !final(containers).spec_index(child_container_ptr).being_killed(),
        final(containers).spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        final(containers).spec_index(child_container_ptr).view_rodata().view().depth == child_depth,
        final(containers).spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().pcid_allocator == child_pcid_allocator_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_2m == child_allocator_2m_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_1g == child_allocator_1g_ptr,
        final(containers).spec_index(child_container_ptr).view().root_process == child_process_ptr,
        !final(containers).spec_index(child_container_ptr).view().zombie,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_processes.view() == set![child_process_ptr],
        final(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq == old(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq,
        final(containers).spec_index(child_container_ptr).view().owned_endpoints == old(containers).spec_index(child_container_ptr).view().owned_endpoints,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_threads == old(containers).spec_index(child_container_ptr).view_ghost().owned_threads,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_indirect_threads == old(containers).spec_index(child_container_ptr).view_ghost().owned_indirect_threads,
        parent_container_lock_perm.lock_id() == final(containers).spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.lock_id() == final(containers).spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        forall|container_ptr: RwLockContainerPtr|
            #![trigger final(containers).spec_index(container_ptr)]
            base_containers.dom().contains(container_ptr) ==> {
                &&& final(containers).spec_index(container_ptr).is_init() == base_containers.spec_index(container_ptr).is_init()
                &&& final(containers).spec_index(container_ptr).view_rodata() == base_containers.spec_index(container_ptr).view_rodata()
                &&& final(containers).spec_index(container_ptr).locking_thread() == base_containers.spec_index(container_ptr).locking_thread()
                &&& final(containers).spec_index(container_ptr).being_killed() == base_containers.spec_index(container_ptr).being_killed()
                &&& final(containers).spec_index(container_ptr).view().parent_linkedlist_node == base_containers.spec_index(container_ptr).view().parent_linkedlist_node
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_threads == base_containers.spec_index(container_ptr).view_ghost().owned_threads
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_processes == base_containers.spec_index(container_ptr).view_ghost().owned_processes
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_indirect_threads == base_containers.spec_index(container_ptr).view_ghost().owned_indirect_threads
                &&& container_ptr != parent_container_ptr ==> final(containers).spec_index(container_ptr).view() == base_containers.spec_index(container_ptr).view()
            },
{
    proof { assert(old(containers).spec_index(parent_container_ptr).inv()) by { container_perms_wf_at(base_containers, parent_container_ptr); }; }
    let (node_addr, node_perm) = container_map_take_parent_node(containers, child_container_ptr, Tracked(lctx), Tracked(child_container_lock_perm));
    proof {
        let ghost original_children = base_containers.spec_index(parent_container_ptr).view().children.view();
        assert(original_children.no_duplicates()) by { container_perms_wf_at(base_containers, parent_container_ptr); };
        assert(original_children.len() <= NUM_PAGES * 4096) by { reveal(container_children_parent_wf); reveal(container_pages_wf); seq_unique_bounded_usize_len(original_children, (NUM_PAGES * 4096) as usize); };
        assert(containers.spec_index(parent_container_ptr).view().children.length == original_children.len()) by { containers.spec_index(parent_container_ptr).view().children.lemma_len_view(); };
        assert(!original_children.contains(child_container_ptr)) by {
            if original_children.contains(child_container_ptr) { assert(base_containers.dom().contains(child_container_ptr)) by { container_children_parent_wf_at(root_container, base_containers, parent_container_ptr, child_container_ptr); }; }
        };
    }
    container_map_push_child(containers, parent_container_ptr, child_container_ptr, node_addr, node_perm, Tracked(lctx), Tracked(parent_container_lock_perm));
    proof { container_insert_child_into_ancestor_subtree_sets(containers, child_uppers, child_container_ptr, lctx.container_lock_map(), lctx.thread_id()); }
    container_map_remove_owned_pages(containers, parent_container_ptr, Ghost(moved_pages), Tracked(lctx), Tracked(parent_container_lock_perm));
}
}

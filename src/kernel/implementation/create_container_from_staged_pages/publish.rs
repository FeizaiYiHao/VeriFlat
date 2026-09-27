use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::opaque]
pub open spec fn new_container_bootstrap_4k_pages(
    allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr,
    process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr
) -> Set<PagePtr> {
    seq![
        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page
    ].to_set()
}

#[verifier::opaque]
pub open spec fn new_container_moved_pages(
    container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr,
    l4_page: PagePtr
) -> Set<PagePtr> {
    page_2m_all_ptrs(page_ptr2page_index(container_page)).union(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))).union(new_container_bootstrap_4k_pages(
        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page
    ))
}

#[verifier::opaque]
pub open spec fn publish_staged_container_root_kernel_state_framing(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize
) -> bool {
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
    let root_pcid: Pcid = (KERNEL_DEFAULT_PCID + 1) as usize;
    let child_uppers = pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr);
    let moved_pages = new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page
    ).union(funding_pages.to_set());
    let funding_indices = funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set();
    let unpublished = |index: PageIndex| index != container_head && index != pcid_allocator_head && index != allocator_4k_index && index != allocator_2m_index && index != allocator_1g_index && index != scheduler_index && index != cpu_set_index && index != process_index && index != pagetable_index && index != l4_index;
    &&& pre.ctn_mp.dom().contains(parent_container_ptr)
    &&& pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page)
    &&& !moved_pages.contains(thread_page)
    &&& !pre.ctn_mp.spec_index(parent_container_ptr).being_killed()
    &&& pre.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
    &&& pre.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr
    &&& pre.thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 8
    &&& funding_pages.len() <= pre.thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8
    &&& pre.thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2
    &&& !pre.ctn_mp.dom().contains(container_page)
    &&& !pre.pcid_allc_mp.dom().contains(pcid_allocator_page)
    &&& !pre.allc_4k_mp.dom().contains(allocator_4k_page)
    &&& !pre.allc_2m_mp.dom().contains(allocator_2m_page)
    &&& !pre.allc_1g_mp.dom().contains(allocator_1g_page)
    &&& !pre.sched_mp.dom().contains(scheduler_page)
    &&& !pre.cpu_set_mp.dom().contains(cpu_set_page)
    &&& !pre.prc_mp.dom().contains(process_page)
    &&& !pre.pt_mp.dom().contains(pagetable_page)
    &&& pre.thr_mp.dom().contains(current_thread_ptr)
    &&& funding_pages.len() == allocator_quota_4k + process_quota_4k
    &&& forall|page_ptr: PagePtr|
        #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
        #![trigger funding_pages.to_set().contains(page_ptr)]
        #![trigger new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page
        ).contains(page_ptr)]
        pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page
        ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page
    &&& forall|page_ptr: PagePtr|
        #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
        pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page
    &&& pre.pg_arr.spec_index(container_head).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })
    &&& pre.pg_arr.spec_index(pcid_allocator_head).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })
    &&& moved_pages.subset_of(pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view())
    &&& post.it_mp == pre.it_mp
    &&& post.irt == pre.irt
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.pcid_needflush == pre.pcid_needflush
    &&& post.cpu_published == pre.cpu_published
    &&& post.ep_mp == pre.ep_mp
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index).view().view().mappings()]
        #![trigger pre.pg_arr.spec_index(index).view().view().mappings()]
        index_valid(NUM_PAGES, index) ==> post.pg_arr.spec_index(index).view().view().mappings() == pre.pg_arr.spec_index(index).view().view().mappings()
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index).view().view().state]
        #![trigger pre.pg_arr.spec_index(index).view().view().state]
        index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(container_head).contains(index) && !page_2m_tail_indices(pcid_allocator_head).contains(index) && unpublished(index) ==> post.pg_arr.spec_index(index).view().view().state == pre.pg_arr.spec_index(index).view().view().state
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index).view().view().owning_container]
        #![trigger pre.pg_arr.spec_index(index).view().view().owning_container]
        index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(container_head).contains(index) && !page_2m_tail_indices(pcid_allocator_head).contains(index) && unpublished(index) ==> post.pg_arr.spec_index(index).view().view().owning_container == pre.pg_arr.spec_index(index).view().view().owning_container
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index).view().view().free_list_node_storage]
        #![trigger pre.pg_arr.spec_index(index).view().view().free_list_node_storage]
        index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(container_head).contains(index) && !page_2m_tail_indices(pcid_allocator_head).contains(index) && unpublished(index) ==> post.pg_arr.spec_index(index).view().view().free_list_node_storage == pre.pg_arr.spec_index(index).view().view().free_list_node_storage
    &&& forall|index: PageIndex|
        #![trigger page_2m_tail_indices(container_head).contains(index)]
        page_2m_tail_indices(container_head).contains(index) ==> {
            &&& spec_page_index_merge_2m_valid(container_head, index)
            &&& post.pg_arr.spec_index(index).view().view().state is Merged2m
            &&& post.pg_arr.spec_index(index).view().view().owning_container == container_page
        }
    &&& forall|index: PageIndex|
        #![trigger page_2m_tail_indices(pcid_allocator_head).contains(index)]
        page_2m_tail_indices(pcid_allocator_head).contains(index) ==> {
            &&& spec_page_index_merge_2m_valid(pcid_allocator_head, index)
            &&& post.pg_arr.spec_index(index).view().view().state is Merged2m
            &&& post.pg_arr.spec_index(index).view().view().owning_container == container_page
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger funding_pages.to_set().contains(page_ptr)]
        #![trigger funding_pages.contains(page_ptr)]
        funding_pages.to_set().contains(page_ptr) ==> {
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                allocator_ptr: Ghost(allocator_4k_page), state: FreePageAllocatorState::GlobalList,
            })
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_page
        }
    &&& staged_4k_page_chain(pre.pg_arr, funding_pages)
    &&& forall|page_ptr: PagePtr|
        #![trigger post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list]
        #![trigger pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list]
        funding_pages.to_set().contains(page_ptr) ==> post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list
    &&& post.pg_arr.spec_index(container_head).view().view().state == (PageState::Allocated2m {
        state: Allocated2MPageState::AsContainer,
    })
    &&& post.pg_arr.spec_index(pcid_allocator_head).view().view().state == (PageState::Allocated2m {
        state: Allocated2MPageState::AsPcidAllocator,
    })
    &&& post.pg_arr.spec_index(allocator_4k_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::As4KAllocator,
    })
    &&& post.pg_arr.spec_index(allocator_2m_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::As2MAllocator,
    })
    &&& post.pg_arr.spec_index(allocator_1g_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::As1GAllocator,
    })
    &&& post.pg_arr.spec_index(scheduler_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::AsScheduler,
    })
    &&& post.pg_arr.spec_index(cpu_set_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::AsCpuSet,
    })
    &&& post.pg_arr.spec_index(process_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::AsProcess,
    })
    &&& post.pg_arr.spec_index(pagetable_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::AsPageTableRoot,
    })
    &&& post.pg_arr.spec_index(l4_index).view().view().state == (PageState::Allocated4k {
        state: Allocated4KPageState::PageTable { pagetable_root: pagetable_page },
    })
    &&& post.pg_arr.spec_index(container_head).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(pcid_allocator_head).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(allocator_4k_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(allocator_2m_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(allocator_1g_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(scheduler_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(cpu_set_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(process_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(pagetable_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(l4_index).view().view().owning_container == container_page
    &&& post.pg_arr.spec_index(page_ptr2page_index(thread_page)) == pre.pg_arr.spec_index(page_ptr2page_index(thread_page))
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom().insert(container_page)
    &&& forall|ptr: RwLockContainerPtr|
        #![trigger post.ctn_mp.dom().contains(ptr)]
        #![trigger post.ctn_mp.spec_index(ptr)]
        post.ctn_mp.dom().contains(ptr) && ptr != container_page ==> {
            &&& pre.ctn_mp.dom().contains(ptr)
            &&& post.ctn_mp.spec_index(ptr).is_init() == pre.ctn_mp.spec_index(ptr).is_init()
            &&& post.ctn_mp.spec_index(ptr).view_rodata() == pre.ctn_mp.spec_index(ptr).view_rodata()
            &&& post.ctn_mp.spec_index(ptr).locking_thread() == pre.ctn_mp.spec_index(ptr).locking_thread()
            &&& post.ctn_mp.spec_index(ptr).being_killed() == pre.ctn_mp.spec_index(ptr).being_killed()
            &&& post.ctn_mp.spec_index(ptr).view().parent_linkedlist_node == pre.ctn_mp.spec_index(ptr).view().parent_linkedlist_node
            &&& post.ctn_mp.spec_index(ptr).view_ghost().owned_threads == pre.ctn_mp.spec_index(ptr).view_ghost().owned_threads
            &&& post.ctn_mp.spec_index(ptr).view_ghost().owned_indirect_threads == pre.ctn_mp.spec_index(ptr).view_ghost().owned_indirect_threads
            &&& ptr != parent_container_ptr ==> post.ctn_mp.spec_index(ptr).view() == pre.ctn_mp.spec_index(ptr).view()
        }
    &&& forall|ptr: RwLockContainerPtr|
        #![trigger post.ctn_mp.spec_index(ptr).view_ghost().uppertree_seq]
        #![trigger pre.ctn_mp.spec_index(ptr).view_ghost().uppertree_seq]
        pre.ctn_mp.dom().contains(ptr) ==> post.ctn_mp.spec_index(ptr).view_ghost().uppertree_seq == pre.ctn_mp.spec_index(ptr).view_ghost().uppertree_seq
    &&& forall|ptr: RwLockContainerPtr|
        #![trigger child_uppers.contains(ptr)]
        child_uppers.contains(ptr) ==> post.ctn_mp.spec_index(ptr).view_ghost().subtree_set.view() == pre.ctn_mp.spec_index(ptr).view_ghost().subtree_set.view().insert(container_page)
    &&& forall|ptr: RwLockContainerPtr|
        #![trigger pre.ctn_mp.dom().contains(ptr)]
        pre.ctn_mp.dom().contains(ptr) && !child_uppers.contains(ptr) ==> post.ctn_mp.spec_index(ptr).view_ghost().subtree_set == pre.ctn_mp.spec_index(ptr).view_ghost().subtree_set
    &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.view() == pre.ctn_mp.spec_index(parent_container_ptr).view().children.view().push(container_page)
    &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.map().dom().contains(post.ctn_mp.spec_index(container_page).view().parent_linkedlist_node.addr())
    &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.map().spec_index(post.ctn_mp.spec_index(container_page).view().parent_linkedlist_node.addr()) == container_page
    &&& forall|node_addr: usize|
        #![trigger pre.ctn_mp.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr)]
        pre.ctn_mp.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr) ==> {
            &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr)
            &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.map().spec_index(node_addr) == pre.ctn_mp.spec_index(parent_container_ptr).view().children.map().spec_index(node_addr)
        }
    &&& post.ctn_mp.spec_index(parent_container_ptr).view() == (Container {
        children: post.ctn_mp.spec_index(parent_container_ptr).view().children,
        owned_pages: post.ctn_mp.spec_index(parent_container_ptr).view().owned_pages,
        ..pre.ctn_mp.spec_index(parent_container_ptr).view()
    })
    &&& post.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() == pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().difference(moved_pages)
    &&& post.ctn_mp.spec_index(container_page).view().root_process == process_page
    &&& !post.ctn_mp.spec_index(container_page).being_killed()
    &&& post.ctn_mp.spec_index(container_page).view().owned_processes.view() == set![process_page]
    &&& post.ctn_mp.spec_index(container_page).view().owned_endpoints.view().is_empty()
    &&& post.ctn_mp.spec_index(container_page).view().owned_pages.view() == moved_pages
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_container_ptr)
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().depth == pre.ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth + 1
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().scheduler == scheduler_page
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().pcid_allocator == pcid_allocator_page
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().cpu_set == cpu_set_page
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_4k == allocator_4k_page
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_2m == allocator_2m_page
    &&& post.ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_1g == allocator_1g_page
    &&& post.ctn_mp.spec_index(container_page).view().children.view().len() == 0
    &&& !post.ctn_mp.spec_index(container_page).view().parent_linkedlist_node.is_init()
    &&& post.ctn_mp.spec_index(container_page).view_ghost().uppertree_seq.view() == child_uppers
    &&& post.ctn_mp.spec_index(container_page).view_ghost().subtree_set.view().is_empty()
    &&& post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view().is_empty()
    &&& post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view().is_empty()
    &&& post.prc_mp.dom() =~= pre.prc_mp.dom().insert(process_page)
    &&& forall|ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.spec_index(ptr)]
        pre.prc_mp.dom().contains(ptr) ==> post.prc_mp.spec_index(ptr) == pre.prc_mp.spec_index(ptr)
    &&& post.prc_mp.spec_index(process_page).wlocked()
    &&& !post.prc_mp.spec_index(process_page).being_killed()
    &&& !post.prc_mp.spec_index(process_page).view().zombie
    &&& post.prc_mp.spec_index(process_page).view().pcid == root_pcid
    &&& post.prc_mp.spec_index(process_page).view().pagetable == pagetable_page
    &&& post.prc_mp.spec_index(process_page).view().iommu_table is None
    &&& post.prc_mp.spec_index(process_page).view().pci_function_ref_counter == 0
    &&& post.prc_mp.spec_index(process_page).view().owned_pci_functions.view().is_empty()
    &&& post.prc_mp.spec_index(process_page).view().quota_4k == process_quota_4k
    &&& post.prc_mp.spec_index(process_page).view().quota_2m == 0
    &&& post.prc_mp.spec_index(process_page).view().quota_1g == 0
    &&& post.prc_mp.spec_index(process_page).view().children.view().len() == 0
    &&& post.prc_mp.spec_index(process_page).view().owned_threads.view().len() == 0
    &&& post.prc_mp.spec_index(process_page).view().parent_linkedlist_node.is_init()
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().owning_container == container_page
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().container_depth == post.ctn_mp.spec_index(container_page).view_rodata().view().depth
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().parent is None
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().depth == 0
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().pagetable == pagetable_page
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().cr3 == l4_page
    &&& post.prc_mp.spec_index(process_page).view_rodata().view().pcid == root_pcid
    &&& post.prc_mp.spec_index(process_page).view_ghost().uppertree_seq.view().len() == 0
    &&& post.prc_mp.spec_index(process_page).view_ghost().subtree_set.view().is_empty()
    &&& post.pt_mp.dom() =~= pre.pt_mp.dom().insert(pagetable_page)
    &&& forall|ptr: RwLockPageTableRoot|
        #![trigger post.pt_mp.spec_index(ptr)]
        pre.pt_mp.dom().contains(ptr) ==> post.pt_mp.spec_index(ptr) == pre.pt_mp.spec_index(ptr)
    &&& !post.pt_mp.spec_index(pagetable_page).being_killed()
    &&& post.pt_mp.spec_index(pagetable_page).view().proc_ptr == process_page
    &&& post.pt_mp.spec_index(pagetable_page).view().pcid is Some
    &&& post.pt_mp.spec_index(pagetable_page).view().pcid_value() == root_pcid
    &&& post.pt_mp.spec_index(pagetable_page).view().cr3 == l4_page
    &&& post.pt_mp.spec_index(pagetable_page).view().kernel_l4_end == pre.dflt_pt.view().kernel_l4_end
    &&& post.pt_mp.spec_index(pagetable_page).view().is_empty()
    &&& post.pt_mp.spec_index(pagetable_page).view().page_closure() == set![l4_page]
    &&& post.sched_mp.dom() =~= pre.sched_mp.dom().insert(scheduler_page)
    &&& forall|ptr: RwLockSchedulerPtr|
        #![trigger post.sched_mp.spec_index(ptr)]
        pre.sched_mp.dom().contains(ptr) ==> post.sched_mp.spec_index(ptr) == pre.sched_mp.spec_index(ptr)
    &&& !post.sched_mp.spec_index(scheduler_page).being_killed()
    &&& post.sched_mp.spec_index(scheduler_page).view().owning_container == container_page
    &&& post.sched_mp.spec_index(scheduler_page).view().queue.view().len() == 0
    &&& post.cpu_set_mp.dom() =~= pre.cpu_set_mp.dom().insert(cpu_set_page)
    &&& forall|ptr: RwLockCpuSetPtr|
        #![trigger post.cpu_set_mp.spec_index(ptr)]
        pre.cpu_set_mp.dom().contains(ptr) ==> post.cpu_set_mp.spec_index(ptr) == pre.cpu_set_mp.spec_index(ptr)
    &&& post.cpu_set_mp.spec_index(cpu_set_page).view().owning_container.view() == container_page
    &&& post.cpu_set_mp.spec_index(cpu_set_page).view().container_depth.view() == post.ctn_mp.spec_index(container_page).view_rodata().view().depth
    &&& post.cpu_set_mp.spec_index(cpu_set_page).view().owned_cpus.view().is_empty()
    &&& post.cpu_set_mp.spec_index(cpu_set_page).view().owned_cpus.closed_view().is_empty()
    &&& post.pcid_allc_mp.dom() =~= pre.pcid_allc_mp.dom().insert(pcid_allocator_page)
    &&& forall|ptr: RwLockPcidAllocatorPtr|
        #![trigger post.pcid_allc_mp.spec_index(ptr)]
        pre.pcid_allc_mp.dom().contains(ptr) ==> post.pcid_allc_mp.spec_index(ptr) == pre.pcid_allc_mp.spec_index(ptr)
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_page).view().owning_container.view() == container_page
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_page).view().container_depth.view() == post.ctn_mp.spec_index(container_page).view_rodata().view().depth
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_page).view().ref_counters.spec_index(root_pcid) == 1
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_page).view().id_to_proc.view().spec_index(root_pcid as int)
        =~= set![process_page]
    &&& forall|pcid: Pcid|
        #![trigger post.pcid_allc_mp.spec_index(pcid_allocator_page).view().ref_counters.spec_index(pcid)]
        pcid_valid(pcid) && pcid != root_pcid ==> post.pcid_allc_mp.spec_index(pcid_allocator_page).view().ref_counters.spec_index(pcid) == 0
    &&& post.allc_4k_mp.dom() =~= pre.allc_4k_mp.dom().insert(allocator_4k_page)
    &&& post.allc_2m_mp.dom() =~= pre.allc_2m_mp.dom().insert(allocator_2m_page)
    &&& post.allc_1g_mp.dom() =~= pre.allc_1g_mp.dom().insert(allocator_1g_page)
    &&& forall|ptr: RwLockPageAllocatorPtr|
        #![trigger post.allc_4k_mp.spec_index(ptr)]
        pre.allc_4k_mp.dom().contains(ptr) ==> post.allc_4k_mp.spec_index(ptr) == pre.allc_4k_mp.spec_index(ptr)
    &&& forall|ptr: RwLockPageAllocatorPtr|
        #![trigger post.allc_2m_mp.spec_index(ptr)]
        pre.allc_2m_mp.dom().contains(ptr) ==> post.allc_2m_mp.spec_index(ptr) == pre.allc_2m_mp.spec_index(ptr)
    &&& forall|ptr: RwLockPageAllocatorPtr|
        #![trigger post.allc_1g_mp.spec_index(ptr)]
        pre.allc_1g_mp.dom().contains(ptr) ==> post.allc_1g_mp.spec_index(ptr) == pre.allc_1g_mp.spec_index(ptr)
    &&& post.allc_4k_mp.spec_index(allocator_4k_page).owning_container == container_page
    &&& post.allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().view() == funding_pages
    &&& forall|page_ptr: PagePtr|
        #![trigger funding_pages.to_set().contains(page_ptr)]
        #![trigger funding_pages.contains(page_ptr)]
        funding_pages.to_set().contains(page_ptr) ==> {
            &&& page_ptr_valid(page_ptr)
            &&& page_ptr_valid(page_ptr) ==> {
                let node_addr = post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr();
                &&& post.allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().map().dom().contains(node_addr)
                &&& post.allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().map().spec_index(node_addr) == page_ptr
            }
        }
    &&& post.allc_4k_mp.spec_index(allocator_4k_page).total_free_pages.view() == funding_pages.len()
    &&& post.allc_4k_mp.spec_index(allocator_4k_page).quota.view().view() == allocator_quota_4k
    &&& post.allc_4k_mp.spec_index(allocator_4k_page).quota.view().container_depth == post.ctn_mp.spec_index(container_page).view_rodata().view().depth
    &&& forall|cpu_id: CpuId|
        #![trigger post.allc_4k_mp.spec_index(allocator_4k_page).cpu_caches.spec_index(cpu_id).view().view().view()]
        index_valid(NUM_CPUS, cpu_id) ==> post.allc_4k_mp.spec_index(allocator_4k_page).cpu_caches.spec_index(cpu_id).view().view().view() == Seq::<PagePtr>::empty()
    &&& post.allc_2m_mp.spec_index(allocator_2m_page).owning_container == container_page
    &&& post.allc_2m_mp.spec_index(allocator_2m_page).global_pool.view().view() == Seq::<PagePtr>::empty()
    &&& post.allc_2m_mp.spec_index(allocator_2m_page).total_free_pages.view() == 0
    &&& post.allc_2m_mp.spec_index(allocator_2m_page).quota.view().view() == 0
    &&& post.allc_2m_mp.spec_index(allocator_2m_page).quota.view().container_depth == post.ctn_mp.spec_index(container_page).view_rodata().view().depth
    &&& forall|cpu_id: CpuId|
        #![trigger post.allc_2m_mp.spec_index(allocator_2m_page).cpu_caches.spec_index(cpu_id).view().view().view()]
        index_valid(NUM_CPUS, cpu_id) ==> post.allc_2m_mp.spec_index(allocator_2m_page).cpu_caches.spec_index(cpu_id).view().view().view() == Seq::<PagePtr>::empty()
    &&& post.allc_1g_mp.spec_index(allocator_1g_page).owning_container == container_page
    &&& post.allc_1g_mp.spec_index(allocator_1g_page).global_pool.view().view() == Seq::<PagePtr>::empty()
    &&& post.allc_1g_mp.spec_index(allocator_1g_page).total_free_pages.view() == 0
    &&& post.allc_1g_mp.spec_index(allocator_1g_page).quota.view().view() == 0
    &&& post.allc_1g_mp.spec_index(allocator_1g_page).quota.view().container_depth == post.ctn_mp.spec_index(container_page).view_rodata().view().depth
    &&& forall|cpu_id: CpuId|
        #![trigger post.allc_1g_mp.spec_index(allocator_1g_page).cpu_caches.spec_index(cpu_id).view().view().view()]
        index_valid(NUM_CPUS, cpu_id) ==> post.allc_1g_mp.spec_index(allocator_1g_page).cpu_caches.spec_index(cpu_id).view().view().view() == Seq::<PagePtr>::empty()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, current_thread_ptr)
    &&& post.thr_mp.spec_index(current_thread_ptr).view() == (Thread {
        temp_alloc_cache_4k: Ghost(set![thread_page]), temp_alloc_cache_2m: Ghost(Set::empty()),
        quota_4k: (pre.thr_mp.spec_index(current_thread_ptr).view().quota_4k as int - 8 - funding_pages.len()) as usize,
        quota_2m: (pre.thr_mp.spec_index(current_thread_ptr).view().quota_2m as int - 2) as usize,
        ..pre.thr_mp.spec_index(current_thread_ptr).view()
    })
    &&& post.thr_mp.spec_index(current_thread_ptr).locking_thread() == pre.thr_mp.spec_index(current_thread_ptr).locking_thread()
    &&& post.thr_mp.spec_index(current_thread_ptr).locking_thread() is Write
    &&& post.thr_mp.spec_index(current_thread_ptr).being_killed() == pre.thr_mp.spec_index(current_thread_ptr).being_killed()
    &&& thread_quota_4k_fields_unchanged(pre.thr_mp, post.thr_mp)
    &&& thread_quota_2m_fields_unchanged(pre.thr_mp, post.thr_mp)
    &&& thread_quota_1g_fields_unchanged(pre.thr_mp, post.thr_mp)
}

#[verifier::spinoff_prover]
pub(super) fn publish_staged_container_root_mutation(
    krnl: &mut KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, allocator_quota_4k: usize,
    process_quota_4k: usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>, Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count <= old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        forall|page_ptr: PagePtr|
            #![trigger old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
            #![trigger funding_pages.to_set().contains(page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
                l4_page,
            ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
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
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        )),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        ).union(funding_pages.to_set()).subset_of(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view(),),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        !old(krnl).sched_mp.dom().contains(scheduler_page),
        !old(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        !old(krnl).prc_mp.dom().contains(process_page),
        !old(krnl).pt_mp.dom().contains(pagetable_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& funding_page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr),).view().view().owning_container == parent_container_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr),).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page),),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).pt_mp.perms_wf(),
        final(krnl).pt_mp.spec_index(pagetable_page).inv(),
        final(krnl).ctn_mp.perms_wf(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).inv(),
        final(krnl).ctn_mp.spec_index(container_page).inv(),
        final(krnl).prc_mp.perms_wf(),
        final(krnl).prc_mp.spec_index(process_page).inv(),
        final(krnl).thr_mp.perms_wf(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).inv(),
        final(krnl).sched_mp.perms_wf(),
        final(krnl).sched_mp.spec_index(scheduler_page).inv(),
        final(krnl).cpu_set_mp.perms_wf(),
        final(krnl).cpu_set_mp.spec_index(cpu_set_page).inv(),
        final(krnl).pcid_allc_mp.perms_wf(),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).inv(),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).inv(),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_2m_mp.spec_index(allocator_2m_page).inv(),
        final(krnl).allc_1g_mp.perms_wf(),
        final(krnl).allc_1g_mp.spec_index(allocator_1g_page).inv(),
        publish_staged_container_root_kernel_state_framing(
            *old(krnl), *final(krnl), parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        ),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(container_page),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger final(lctx).container_lock_map().spec_index(ptr)]
            #![trigger old(lctx).container_lock_map().get(ptr)]
            #![trigger old(lctx).container_lock_map().spec_index(ptr)]
            old(lctx).container_lock_map().dom().contains(ptr) && ptr != container_page ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            #![trigger final(lctx).process_lock_map().spec_index(ptr)]
            #![trigger old(lctx).process_lock_map().get(ptr)]
            #![trigger old(lctx).process_lock_map().spec_index(ptr)]
            old(lctx).process_lock_map().dom().contains(ptr) && ptr != process_page ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom().insert(scheduler_page),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(pcid_allocator_page),
        final(lctx).cpu_set_lock_map().dom() == old(lctx).cpu_set_lock_map().dom().insert(cpu_set_page),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger final(lctx).cpu_set_lock_map().spec_index(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().spec_index(ptr)]
            old(lctx).cpu_set_lock_map().dom().contains(ptr) && ptr != cpu_set_page ==> final(lctx).cpu_set_lock_map().get(ptr) == old(lctx).cpu_set_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            #![trigger final(lctx).pagetable_lock_map().spec_index(ptr)]
            #![trigger old(lctx).pagetable_lock_map().get(ptr)]
            #![trigger old(lctx).pagetable_lock_map().spec_index(ptr)]
            old(lctx).pagetable_lock_map().dom().contains(ptr) && ptr != pagetable_page ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), cpu_set_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(pcid_allocator_page),),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(process_page).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).sched_mp.spec_index(scheduler_page).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).cpu_set_mp.spec_index(cpu_set_page).locking_thread()->Write_lock_id,
{
    hide(Seq::contains);
    hide(Seq::no_duplicates);
    let ghost pre_krnl = *krnl;
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
        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    );
    let ghost bootstrap_seq = seq![allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page];
    let ghost funding_indices = funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set();
    proof {
        assert(bootstrap_seq.to_set() == bootstrap_pages) by { reveal(new_container_bootstrap_4k_pages); };
        bootstrap_seq.lemma_no_dup_set_cardinality();
        page_ptr_seq_indices_no_duplicates(bootstrap_seq);
        assert({
            &&& allocator_2m_index != allocator_4k_index
            &&& allocator_1g_index != allocator_4k_index
            &&& allocator_1g_index != allocator_2m_index
            &&& scheduler_index != allocator_4k_index
            &&& scheduler_index != allocator_2m_index
            &&& scheduler_index != allocator_1g_index
            &&& cpu_set_index != allocator_4k_index
            &&& cpu_set_index != allocator_2m_index
            &&& cpu_set_index != allocator_1g_index
            &&& cpu_set_index != scheduler_index
            &&& process_index != allocator_4k_index
            &&& process_index != allocator_2m_index
            &&& process_index != allocator_1g_index
            &&& process_index != scheduler_index
            &&& process_index != cpu_set_index
            &&& pagetable_index != allocator_4k_index
            &&& pagetable_index != allocator_2m_index
            &&& pagetable_index != allocator_1g_index
            &&& pagetable_index != scheduler_index
            &&& pagetable_index != cpu_set_index
            &&& pagetable_index != process_index
            &&& l4_index != allocator_4k_index
            &&& l4_index != allocator_2m_index
            &&& l4_index != allocator_1g_index
            &&& l4_index != scheduler_index
            &&& l4_index != cpu_set_index
            &&& l4_index != process_index
            &&& l4_index != pagetable_index
        }) by { reveal(Seq::no_duplicates); };
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        assert(container_head != pcid_allocator_head) by { page_ptr2page_index_neq(container_page, pcid_allocator_page); };
        distinct_2m_heads_have_disjoint_tails(container_head, pcid_allocator_head);
        assert(!page_2m_tail_indices(container_head).contains(pcid_allocator_head) && !page_2m_tail_indices(pcid_allocator_head).contains(container_head)) by {
            page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); distinct_2m_heads_have_disjoint_all_ptrs(container_head, pcid_allocator_head);
            if page_2m_tail_indices(container_head).contains(pcid_allocator_head) { page_2m_all_ptrs_contains_index(container_head, pcid_allocator_head); }
            if page_2m_tail_indices(pcid_allocator_head).contains(container_head) { page_2m_all_ptrs_contains_index(pcid_allocator_head, container_head); }
        };
        assert(krnl.pg_arr.inv()) by { page_array_wf_at(krnl.pg_arr, container_head); };
        assert(krnl.ctn_mp.perms_wf()) by { container_perms_wf_map(krnl.ctn_mp); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).is_init()) by { container_perms_wf_at(krnl.ctn_mp, parent_container_ptr); };
        assert(bootstrap_pages.contains(allocator_4k_page) && bootstrap_pages.contains(allocator_2m_page) && bootstrap_pages.contains(allocator_1g_page) && bootstrap_pages.contains(scheduler_page) && bootstrap_pages.contains(cpu_set_page) && bootstrap_pages.contains(process_page) && bootstrap_pages.contains(pagetable_page) && bootstrap_pages.contains(l4_page)) by { bootstrap_seq.to_set_ensures(); reveal(new_container_bootstrap_4k_pages); reveal(Seq::contains); };
        assert(krnl.dflt_pt.view().wf()) by { krnl.default_pagetable_view_inv(); };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by { krnl.dflt_pt.view().kernel_l4_end_valid(); };
    }
    let child_depth = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().depth + 1;
    let ghost parent_uppers = krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view();
    let ghost child_uppers = parent_uppers.push(parent_container_ptr);
    let ghost moved_pages = new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).union(funding_pages.to_set());
    proof {
        assert(krnl.prc_mp.perms_wf()) by { process_perms_wf_map(krnl.prc_mp); };
        assert(krnl.pt_mp.perms_wf()) by { pagetable_perms_wf_map(krnl.pt_mp); };
        assert(krnl.sched_mp.perms_wf()) by { scheduler_perms_wf_map(krnl.sched_mp); };
        assert(krnl.cpu_set_mp.perms_wf()) by { cpu_set_perms_wf_map(krnl.cpu_set_mp); };
        assert(krnl.pcid_allc_mp.perms_wf()) by { pcid_allocator_perms_wf_map(krnl.pcid_allc_mp); };
        assert(parent_uppers.no_duplicates() && parent_uppers.len() == krnl.ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth) by { container_perms_wf_at(krnl.ctn_mp, parent_container_ptr); };
        assert(!parent_uppers.contains(parent_container_ptr)) by { container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, parent_container_ptr); };
        assert(child_uppers.no_duplicates()) by { seq_push_unique_lemma::<RwLockContainerPtr>(); };
        assert(child_uppers.to_set().subset_of(krnl.ctn_mp.dom())) by { parent_uppers.to_set_ensures(); child_uppers.to_set_ensures(); seq_push_lemma::<RwLockContainerPtr>(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, parent_container_ptr); };
        assert(!child_uppers.to_set().contains(child_container_ptr)) by { child_uppers.to_set_ensures(); };
        owned_4k_page_not_in_2m_region(krnl, thread_page, container_head);
        owned_4k_page_not_in_2m_region(krnl, thread_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_4k_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_2m_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_1g_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_4k_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_2m_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_1g_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, scheduler_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, scheduler_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, cpu_set_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, cpu_set_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, process_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, process_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, pagetable_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, pagetable_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, l4_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, l4_page, pcid_allocator_head);
        assert(!moved_pages.contains(thread_page)) by { reveal(new_container_moved_pages); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_ptr2page_index(thread_page)); };
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
    }
    let (funded_global_pool, Tracked(container_perm), Tracked(pcid_allocator_perm)) = prepare_new_container_backing_pages(
        &mut krnl.pg_arr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page,
        cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_page_count, funding_page_head, Ghost(funding_pages),
        Ghost(funding_indices), child_allocator_4k_ptr, child_container_ptr, child_depth, Ghost(pre_krnl), Tracked(&mut *lctx),
        Tracked(funding_page_lock_perms), Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let allocator_4k_value = PageAllocator::new_with_global_pool(child_container_ptr, child_depth, funded_global_pool, allocator_quota_4k);
    let allocator_2m_value = PageAllocator::new_empty(child_container_ptr, child_depth);
    let allocator_1g_value = PageAllocator::new_empty(child_container_ptr, child_depth);
    let scheduler_value = Scheduler::new_empty(child_scheduler_ptr, child_container_ptr, child_depth);
    let mut pcid_allocator_value = PcidAllocator::new_empty(child_container_ptr, child_depth);
    pcid_allocator_value.alloc(root_pcid, child_process_ptr);
    let (Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm)) = publish_new_container_process_and_pagetable(
        krnl, child_container_ptr, child_process_ptr, child_pagetable_ptr, l4_page, root_pcid, child_depth, process_quota_4k,
        container_head, pcid_allocator_head, Tracked(&mut *lctx), Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(container_tail_lock_perms),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    publish_new_container_allocators(
        krnl, child_container_ptr, allocator_4k_page, allocator_2m_page, allocator_1g_page, allocator_4k_value, allocator_2m_value,
        allocator_1g_value, container_head, pcid_allocator_head, Tracked(&mut *lctx),
        Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm), Tracked(allocator_1g_page_lock_perm),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let Tracked(child_scheduler_lock_perm) = publish_new_container_scheduler(
        krnl, child_container_ptr, child_scheduler_ptr, scheduler_page, cpu_set_index, scheduler_value, container_head,
        pcid_allocator_head, Tracked(&mut *lctx), Tracked(scheduler_page_lock_perm), Tracked(container_tail_lock_perms),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    let cpu_set_value = CpuSet::new_empty(child_container_ptr, child_depth);
    let Tracked(child_cpu_set_lock_perm) = publish_new_container_cpu_set(
        krnl, child_container_ptr, child_cpu_set_ptr, cpu_set_page, cpu_set_value, container_head, pcid_allocator_head,
        Tracked(&mut *lctx), Tracked(cpu_set_page_lock_perm), Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let mut container_value = Container::new_staged(child_container_ptr, child_process_ptr, child_depth);
    container_value.owned_processes = Ghost(Set::empty().insert(child_process_ptr));
    container_value.owned_pages = Ghost(moved_pages);
    let container_rodata = ReadOnlyNode::new(
        ContainerRO {
            parent: Some(parent_container_ptr), depth: child_depth, scheduler: child_scheduler_ptr, pcid_allocator: child_pcid_allocator_ptr,
            cpu_set: child_cpu_set_ptr, allocator_ptr_4k: child_allocator_4k_ptr, allocator_ptr_2m: child_allocator_2m_ptr,
            allocator_ptr_1g: child_allocator_1g_ptr,
        },
        Ghost(child_container_ptr),
    );
    let container_ghost = ContainerGhost {
        uppertree_seq: Ghost(child_uppers), subtree_set: Ghost(Set::empty()), owned_threads: Ghost(Set::empty()),
        owned_indirect_threads: Ghost(Set::empty()),
    };
    let (Tracked(child_pcid_allocator_lock_perm), Tracked(child_container_lock_perm)) = publish_new_container_pcid_allocator_and_container(
        krnl, child_pcid_allocator_ptr, pcid_allocator_value, child_container_ptr, container_value, container_rodata, container_ghost,
        Tracked(&mut *lctx), Tracked(pcid_allocator_perm), Tracked(container_perm),
    );

    link_new_container_into_tree(
        &mut krnl.ctn_mp, krnl.rt_ctn, parent_container_ptr, child_container_ptr, child_process_ptr, child_scheduler_ptr,
        child_pcid_allocator_ptr, child_cpu_set_ptr, child_allocator_4k_ptr, child_allocator_2m_ptr, child_allocator_1g_ptr, child_depth,
        thread_page, Ghost(child_uppers), Ghost(moved_pages), Ghost(pre_krnl.ctn_mp), Ghost(pre_krnl.pg_arr), Tracked(&*lctx),
        Tracked(parent_container_lock_perm), Tracked(&child_container_lock_perm),
    );
    proof {
        let ghost consumed_4k_pages = bootstrap_pages.union(funding_pages.to_set());
        let ghost initial_cache = krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view();
        assert(initial_cache == consumed_4k_pages.insert(thread_page)) by { vstd::set::axiom_set_ext_equal(initial_cache, consumed_4k_pages.insert(thread_page)); };
        funding_pages.unique_seq_to_set();
        assert(bootstrap_pages.disjoint(funding_pages.to_set())) by { reveal(new_container_moved_pages); };
        vstd::set_lib::lemma_set_disjoint_lens(bootstrap_pages, funding_pages.to_set());
        vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page);
        assert(funding_page_count < krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8) by { thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); };
        let ghost initial_2m_cache = krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view();
        assert(initial_2m_cache =~= set![container_page, pcid_allocator_page]) by { vstd::set::axiom_set_ext_equal(initial_2m_cache, set![container_page, pcid_allocator_page]); };
    }
    thread_map_consume_new_container_staging(
        &mut krnl.thr_mp, current_thread_ptr, thread_page, funding_page_count,
        Ghost(bootstrap_pages.union(funding_pages.to_set())), Tracked(&*lctx), Tracked(current_thread_lock_perm),
    );
    proof {
        assert(publish_staged_container_root_kernel_state_framing(
            pre_krnl, *krnl, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        )) by {
            reveal(publish_staged_container_root_kernel_state_framing);
            old(krnl).thr_mp.typed_lock_map_aligned_write_at(old(lctx).thread_lock_map(), old(lctx).thread_id(), current_thread_ptr);
        };
    }
    (
        Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm),
        Tracked(child_pcid_allocator_lock_perm), Tracked(child_cpu_set_lock_perm),
    )
}

#[verifier::spinoff_prover]
pub fn publish_staged_container_root(
    krnl: &mut KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, allocator_quota_4k: usize,
    process_quota_4k: usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>, Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count <= old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        forall|page_ptr: PagePtr|
            #![trigger old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
            #![trigger funding_pages.to_set().contains(page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
                l4_page,
            ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
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
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        )),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        ).union(funding_pages.to_set()).subset_of(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view(),),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        !old(krnl).sched_mp.dom().contains(scheduler_page),
        !old(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        !old(krnl).prc_mp.dom().contains(process_page),
        !old(krnl).pt_mp.dom().contains(pagetable_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& funding_page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr),).view().view().owning_container == parent_container_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr),).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page),),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).inv(),
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).pcid_needflush == old(krnl).pcid_needflush,
        final(krnl).cpu_published == old(krnl).cpu_published,
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom().insert(allocator_4k_page),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom().insert(allocator_2m_page),
        final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom().insert(allocator_1g_page),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(allocator_4k_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::As4KAllocator,
        }),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(allocator_2m_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::As2MAllocator,
        }),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(allocator_1g_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::As1GAllocator,
        }),
        !final(krnl).ctn_mp.spec_index(container_page).being_killed(),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().scheduler == scheduler_page,
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_4k == allocator_4k_page,
        final(krnl).ctn_mp.spec_index(container_page).view().owned_processes.view() == set![process_page],
        !final(krnl).prc_mp.spec_index(process_page).being_killed(),
        !final(krnl).prc_mp.spec_index(process_page).view().zombie,
        final(krnl).prc_mp.spec_index(process_page).view_rodata().view().owning_container == container_page,
        final(krnl).prc_mp.spec_index(process_page).view_rodata().view().pagetable == pagetable_page,
        final(krnl).prc_mp.spec_index(process_page).view().quota_4k == process_quota_4k,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).owning_container == container_page,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().view() == funding_pages,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).total_free_pages.view() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).quota.view().view() == allocator_quota_4k,
        final(krnl).pt_mp.spec_index(pagetable_page).view().is_empty(),
        final(krnl).pt_mp.spec_index(pagetable_page).view().proc_ptr == process_page,
        final(krnl).prc_mp.spec_index(process_page).view().iommu_table is None,
        final(krnl).ctn_mp.spec_index(container_page).view_ghost().uppertree_seq.view() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq,
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().cpu_set == cpu_set_page,
        !final(krnl).sched_mp.spec_index(scheduler_page).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(current_thread_ptr).view(),),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            quota_4k: final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k,
            quota_2m: final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m,
            temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k,
            temp_alloc_cache_2m: final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m,
            ..old(krnl).thr_mp.spec_index(current_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8 - funding_page_count,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m - 2,
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx),),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx),),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx),),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr,
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes,
        !final(krnl).ctn_mp.spec_index(container_page).view().owned_pages.view().contains(thread_page),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ],),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ],),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(container_page),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger final(lctx).container_lock_map().spec_index(ptr)]
            #![trigger old(lctx).container_lock_map().get(ptr)]
            #![trigger old(lctx).container_lock_map().spec_index(ptr)]
            old(lctx).container_lock_map().dom().contains(ptr) && ptr != container_page ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            #![trigger final(lctx).process_lock_map().spec_index(ptr)]
            #![trigger old(lctx).process_lock_map().get(ptr)]
            #![trigger old(lctx).process_lock_map().spec_index(ptr)]
            old(lctx).process_lock_map().dom().contains(ptr) && ptr != process_page ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom().insert(scheduler_page),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(pcid_allocator_page),
        final(lctx).cpu_set_lock_map().dom() == old(lctx).cpu_set_lock_map().dom().insert(cpu_set_page),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger final(lctx).cpu_set_lock_map().spec_index(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().spec_index(ptr)]
            old(lctx).cpu_set_lock_map().dom().contains(ptr) && ptr != cpu_set_page ==> final(lctx).cpu_set_lock_map().get(ptr) == old(lctx).cpu_set_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            #![trigger final(lctx).pagetable_lock_map().spec_index(ptr)]
            #![trigger old(lctx).pagetable_lock_map().get(ptr)]
            #![trigger old(lctx).pagetable_lock_map().spec_index(ptr)]
            old(lctx).pagetable_lock_map().dom().contains(ptr) && ptr != pagetable_page ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        final(krnl).prc_mp.dom().contains(process_page),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        final(krnl).pt_mp.dom().contains(pagetable_page),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        final(krnl).sched_mp.dom().contains(scheduler_page),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_page, TypedLockMode::Write),
        final(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), cpu_set_page, TypedLockMode::Write),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(allocator_4k_page), state: FreePageAllocatorState::GlobalList,
                })
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr),).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr),).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(pcid_allocator_page),),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(process_page).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).sched_mp.spec_index(scheduler_page).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).cpu_set_mp.spec_index(cpu_set_page).locking_thread()->Write_lock_id,
{
    let ghost pre_krnl = *krnl;
    let ret = publish_staged_container_root_mutation(
        krnl, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_page_count,
        funding_page_head, Ghost(funding_pages), allocator_quota_4k, process_quota_4k, Tracked(&mut *lctx),
        Tracked(parent_container_lock_perm), Tracked(current_thread_lock_perm), Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm), Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm),
        Tracked(allocator_1g_page_lock_perm), Tracked(scheduler_page_lock_perm), Tracked(cpu_set_page_lock_perm),
        Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(funding_page_lock_perms),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        eof_publish_postconditions(
            pre_krnl, *krnl, *old(lctx), parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page,
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
            l4_page, thread_page, funding_pages, allocator_quota_4k, process_quota_4k,
            *parent_container_lock_perm, *current_thread_lock_perm, *lctx, *funding_page_lock_perms,
        );
        eof_inv(
            pre_krnl, *krnl, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        );
    }
    ret
}
}

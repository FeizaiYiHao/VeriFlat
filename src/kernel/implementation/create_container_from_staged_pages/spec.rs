use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::opaque]
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
    seq![
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page, cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ].to_set()
}

#[verifier::opaque]
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
    page_2m_all_ptrs(page_ptr2page_index(container_page)).union(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))).union(new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ))
}

pub open spec fn publish_staged_container_root_kernel_state_framing(
    pre: KernelK,
    post: KernelK,
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
    funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize,
    process_quota_4k: usize,
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
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page,
        cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ).union(funding_pages.to_set());
    let funding_indices = funding_pages.map_values(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
    ).to_set();
    let published_page_indices = set![
        container_head, pcid_allocator_head, allocator_4k_index, allocator_2m_index,
        allocator_1g_index, scheduler_index, cpu_set_index, process_index,
        pagetable_index, l4_index,
    ];
    &&& pre.ctn_mp.dom().contains(parent_container_ptr)
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
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page,
            cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).contains(page_ptr)]
        pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page
    &&& forall|page_ptr: PagePtr|
        #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
        pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page
    &&& moved_pages.subset_of(
        pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view(),
    )
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
        index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(container_head).contains(index) && !page_2m_tail_indices(pcid_allocator_head).contains(index) && !published_page_indices.contains(index) ==> post.pg_arr.spec_index(index).view().view().state == pre.pg_arr.spec_index(index).view().view().state
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index).view().view().owning_container]
        #![trigger pre.pg_arr.spec_index(index).view().view().owning_container]
        index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(container_head).contains(index) && !page_2m_tail_indices(pcid_allocator_head).contains(index) && !published_page_indices.contains(index) ==> post.pg_arr.spec_index(index).view().view().owning_container == pre.pg_arr.spec_index(index).view().view().owning_container
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index).view().view().free_list_node_storage]
        #![trigger pre.pg_arr.spec_index(index).view().view().free_list_node_storage]
        index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(container_head).contains(index) && !page_2m_tail_indices(pcid_allocator_head).contains(index) && !published_page_indices.contains(index) ==> post.pg_arr.spec_index(index).view().view().free_list_node_storage == pre.pg_arr.spec_index(index).view().view().free_list_node_storage
    &&& forall|index: PageIndex|
        #![trigger page_2m_tail_indices(container_head).contains(index)]
        page_2m_tail_indices(container_head).contains(index) ==> {
            &&& post.pg_arr.spec_index(index).view().view().state is Merged2m
            &&& post.pg_arr.spec_index(index).view().view().owning_container == container_page
        }
    &&& forall|index: PageIndex|
        #![trigger page_2m_tail_indices(pcid_allocator_head).contains(index)]
        page_2m_tail_indices(pcid_allocator_head).contains(index) ==> {
            &&& post.pg_arr.spec_index(index).view().view().state is Merged2m
            &&& post.pg_arr.spec_index(index).view().view().owning_container == container_page
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger funding_pages.to_set().contains(page_ptr)]
        funding_pages.to_set().contains(page_ptr) ==> {
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                allocator_ptr: Ghost(allocator_4k_page),
                state: FreePageAllocatorState::GlobalList,
            })
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_page
        }
    &&& staged_4k_page_chain(post.pg_arr, funding_pages)
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
    &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.map().dom().contains(
        post.ctn_mp.spec_index(container_page).view().parent_linkedlist_node.addr(),
    )
    &&& post.ctn_mp.spec_index(parent_container_ptr).view().children.map().spec_index(
        post.ctn_mp.spec_index(container_page).view().parent_linkedlist_node.addr(),
    ) == container_page
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
        funding_pages.to_set().contains(page_ptr) ==> {
            &&& page_ptr_valid(page_ptr)
            &&& page_ptr_valid(page_ptr) ==> {
                let node_addr = post.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().free_list_node_storage.addr();
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
        temp_alloc_cache_4k: Ghost(set![thread_page]),
        temp_alloc_cache_2m: Ghost(Set::empty()),
        quota_4k: (
            pre.thr_mp.spec_index(current_thread_ptr).view().quota_4k as int - 8 - funding_pages.len()
        ) as usize,
        quota_2m: (
            pre.thr_mp.spec_index(current_thread_ptr).view().quota_2m as int - 2
        ) as usize,
        ..pre.thr_mp.spec_index(current_thread_ptr).view()
    })
    &&& post.thr_mp.spec_index(current_thread_ptr).locking_thread() == pre.thr_mp.spec_index(current_thread_ptr).locking_thread()
    &&& post.thr_mp.spec_index(current_thread_ptr).locking_thread() is Write
    &&& post.thr_mp.spec_index(current_thread_ptr).being_killed() == pre.thr_mp.spec_index(current_thread_ptr).being_killed()
    &&& thread_quota_4k_fields_unchanged(pre.thr_mp, post.thr_mp)
    &&& thread_quota_2m_fields_unchanged(pre.thr_mp, post.thr_mp)
    &&& thread_quota_1g_fields_unchanged(pre.thr_mp, post.thr_mp)
}
}

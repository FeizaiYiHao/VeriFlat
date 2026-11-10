use vstd::prelude::*;
verus! {
use crate::*;

/// The scheduler-queue node of a thread: the last node slot of its page.
pub closed spec fn thread_sched_node_addr(thrd_ptr: RwLockThreadPtr) -> usize { (thrd_ptr + PAGE_SZ_4K_LESS_1_NODE_SLOT) as usize }
/// The process-list node of a thread: the second-to-last node slot of its page.
pub closed spec fn thread_proc_node_addr(thrd_ptr: RwLockThreadPtr) -> usize { (thrd_ptr + PAGE_SZ_4K_LESS_2_NODE_SLOTS) as usize }
/// The endpoint-queue node of a thread: the third-to-last node slot of its page.
pub closed spec fn thread_endpoint_node_addr(thrd_ptr: RwLockThreadPtr) -> usize { (thrd_ptr + PAGE_SZ_4K_LESS_3_NODE_SLOTS) as usize }
/// The parent's child-list node of a process: the last node slot of its page.
pub closed spec fn process_parent_node_addr(prc_ptr: RwLockProcessPtr) -> usize { (prc_ptr + PAGE_SZ_4K_LESS_1_NODE_SLOT) as usize }
/// The parent's child-list node of a container: the last node slot of its 2M page.
pub closed spec fn container_parent_node_addr(ctn_ptr: RwLockContainerPtr) -> usize { (ctn_ptr + PAGE_SZ_2M_LESS_1_NODE_SLOT) as usize }

/// Carve the scheduler, process-list and endpoint node slots off the tail of an owned thread page.
pub fn split_thread_page_node_slots(thrd_ptr: RwLockThreadPtr, Tracked(page_perm): Tracked<PagePerm4k>)
    -> (ret: (Tracked<ThreadRegionPerm>, ExternalNode<RwLockThreadPtr>, ExternalNode<RwLockThreadPtr>, ExternalNode<RwLockThreadPtr>))
    requires
        page_ptr_valid(thrd_ptr),
        page_perm.is_init(),
        page_perm.addr() == thrd_ptr,
    ensures
        ret.0.view().is_init(),
        ret.0.view().addr() == thrd_ptr,
        ret.1.is_init(),
        ret.1.addr() == thread_sched_node_addr(thrd_ptr),
        ret.2.is_init(),
        ret.2.addr() == thread_proc_node_addr(thrd_ptr),
        ret.3.is_init(),
        ret.3.addr() == thread_endpoint_node_addr(thrd_ptr),
{
    let (Tracked(region_2), sched_addr, sched_perm) = split_region_tail_into_node::<PAGE_SZ_4K, PAGE_SZ_4K_LESS_1_NODE_SLOT>(thrd_ptr, Tracked(page_perm));
    let (Tracked(region_1), proc_addr, proc_perm) = split_region_tail_into_node::<PAGE_SZ_4K_LESS_1_NODE_SLOT, PAGE_SZ_4K_LESS_2_NODE_SLOTS>(thrd_ptr, Tracked(region_2));
    let (region, endpoint_addr, endpoint_perm) = split_region_tail_into_node::<PAGE_SZ_4K_LESS_2_NODE_SLOTS, PAGE_SZ_4K_LESS_3_NODE_SLOTS>(thrd_ptr, Tracked(region_1));
    (region, ExternalNode::new_parked(sched_addr, sched_perm), ExternalNode::new_parked(proc_addr, proc_perm), ExternalNode::new_parked(endpoint_addr, endpoint_perm))
}

/// Carve the parent's child-list node slot off the tail of an owned process page.
pub fn split_process_page_node_slot(prc_ptr: RwLockProcessPtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (Tracked<ProcessRegionPerm>, ExternalNode<RwLockProcessPtr>))
    requires
        page_ptr_valid(prc_ptr),
        page_perm.is_init(),
        page_perm.addr() == prc_ptr,
    ensures
        ret.0.view().is_init(),
        ret.0.view().addr() == prc_ptr,
        ret.1.is_init(),
        ret.1.addr() == process_parent_node_addr(prc_ptr),
{
    let (region, node_addr, node_perm) = split_region_tail_into_node::<PAGE_SZ_4K, PAGE_SZ_4K_LESS_1_NODE_SLOT>(prc_ptr, Tracked(page_perm));
    (region, ExternalNode::new_parked(node_addr, node_perm))
}

/// Carve the parent's child-list node slot off the end of an owned container 2M page.
pub fn split_container_page_node_slot(ctn_ptr: RwLockContainerPtr, Tracked(page_perm): Tracked<PagePerm2m>) -> (ret: (Tracked<ContainerRegionPerm>, ExternalNode<RwLockContainerPtr>))
    requires
        page_ptr_2m_valid(ctn_ptr),
        page_perm.is_init(),
        page_perm.addr() == ctn_ptr,
    ensures
        ret.0.view().is_init(),
        ret.0.view().addr() == ctn_ptr,
        ret.1.is_init(),
        ret.1.addr() == container_parent_node_addr(ctn_ptr),
{
    let (region, node_addr, node_perm) = split_region_tail_into_node::<PAGE_SZ_2M, PAGE_SZ_2M_LESS_1_NODE_SLOT>(ctn_ptr, Tracked(page_perm));
    (region, ExternalNode::new_parked(node_addr, node_perm))
}
}

use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_pages(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& post.pg_arr == pre.pg_arr
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_containers(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& pre.ctn_mp.dom().contains(source_container)
    &&& pre.ctn_mp.dom().contains(target_container)
    &&& pre.ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set
    &&& pre.ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set
    &&& pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.rt_ctn == pre.rt_ctn
    &&& transferred ==> {
        let before = pre.cpu_arr.spec_index(transfer_cpu_id).view();
        let after = post.cpu_arr.spec_index(transfer_cpu_id).view();
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() is Write
        &&& after.locking_thread()->Write_thread_id == thread_id
        &&& after.view().view() == CpuView { owning_container: target_container, container_depth: pre.ctn_mp.spec_index(target_container).view_rodata().view().depth, ..before.view().view() }
    }
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_processes(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& post.prc_mp == pre.prc_mp
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_threads(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& pre.thr_mp.dom().contains(current_thread_ptr)
    &&& pre.thr_mp.dom().contains(peer_thread_ptr)
    &&& pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting()
    &&& pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& post.thr_mp.perms_wf()
    &&& forall|key: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(key)]
        #![trigger post.thr_mp.spec_index(key)]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_2m]
        #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_2m]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_1g]
        #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(key) ==> {
            let before = pre.thr_mp.spec_index(key);
            let after = post.thr_mp.spec_index(key);
            &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
            &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
            &&& !(key == peer_thread_ptr) ==> after == before
        }
    &&& {
        let before = pre.thr_mp.spec_index(peer_thread_ptr);
        let after = post.thr_mp.spec_index(peer_thread_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == Thread { state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, blocking_endpoint_index: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), endpoint_linkedlist_node: after.view().endpoint_linkedlist_node, scheduler_linkedlist_node: after.view().scheduler_linkedlist_node, ..before.view() }
        &&& after.view().endpoint_linkedlist_node.addr() == before.view().endpoint_linkedlist_node.addr()
        &&& after.view().scheduler_linkedlist_node.addr() == before.view().scheduler_linkedlist_node.addr()
        &&& after.view().endpoint_linkedlist_node.is_init()
        &&& !after.view().scheduler_linkedlist_node.is_init()
    }
    &&& {
        let before = pre.ep_mp.spec_index(endpoint_ptr);
        let after = post.ep_mp.spec_index(endpoint_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == Endpoint { queue: after.view().queue, ..before.view() }
        &&& after.view().queue.container_depth == before.view().queue.container_depth
        &&& after.view().queue.lock_minor() == before.view().queue.lock_minor()
        &&& after.view().queue.view() == before.view().queue.view().skip(1)
        &&& after.view().queue.length as int == before.view().queue.length as int - 1
        &&& after.view().queue.map() == before.view().queue.map().remove(pre.thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr())
        &&& after.view().queue.dom() == before.view().queue.dom().remove(pre.thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr())
    }
    &&& {
        let before = pre.sched_mp.spec_index(peer_scheduler_ptr);
        let after = post.sched_mp.spec_index(peer_scheduler_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() is Write
        &&& after.locking_thread()->Write_thread_id == thread_id
        &&& after.view() == Scheduler { queue: after.view().queue, ..before.view() }
        &&& after.view().queue.container_depth == before.view().queue.container_depth
        &&& after.view().queue.lock_minor() == before.view().queue.lock_minor()
        &&& after.view().queue.view() == before.view().queue.view().push(peer_thread_ptr)
        &&& after.view().queue.length as int == before.view().queue.length as int + 1
        &&& after.view().queue.map() == before.view().queue.map().insert(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr(), peer_thread_ptr)
        &&& after.view().queue.dom() == before.view().queue.dom().insert(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr())
        &&& !before.view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr())
    }
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_allocators(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_tables(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.dflt_pt == pre.dflt_pt
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_objects(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& pre.sched_mp.dom().contains(peer_scheduler_ptr)
    &&& pre.cpu_set_mp.dom().contains(source_cpu_set)
    &&& pre.cpu_set_mp.dom().contains(target_cpu_set)
    &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0
    &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr
    &&& transferred ==> {
        &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
        &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
        &&& !pre.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
        &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
        &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container
    }
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom()
    &&& post.cpu_set_mp.perms_wf()
    &&& forall|key: RwLockCpuSetPtr|
        #![trigger pre.cpu_set_mp.spec_index(key)]
        #![trigger post.cpu_set_mp.spec_index(key)]
        pre.cpu_set_mp.dom().contains(key) ==> {
            let before = pre.cpu_set_mp.spec_index(key);
            let after = post.cpu_set_mp.spec_index(key);
            &&& !(key == source_cpu_set || key == target_cpu_set) ==> after == before
            &&& (key == source_cpu_set || key == target_cpu_set) ==> {
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.locking_thread() is Write
                &&& after.locking_thread()->Write_thread_id == thread_id
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& !transferred ==> after.view().owned_cpus == before.view().owned_cpus
                &&& transferred ==> {
                    &&& after.view().owned_cpus.view() == if key == source_cpu_set { before.view().owned_cpus.view().remove(transfer_cpu_id) } else { before.view().owned_cpus.view().insert(transfer_cpu_id) }
                    &&& after.view().owned_cpus.closed_view() == if key == source_cpu_set { before.view().owned_cpus.closed_view().remove(transfer_cpu_id) } else { before.view().owned_cpus.closed_view().insert(transfer_cpu_id) }
                    &&& after.view().owned_cpus.data.view() == before.view().owned_cpus.data.view().update(transfer_cpu_id as int, key == target_cpu_set)
                    &&& after.view().owned_cpus.closed.view() == before.view().owned_cpus.closed.view().update(transfer_cpu_id as int, key == target_cpu_set)
                    &&& after.view().owned_cpus.len as int == before.view().owned_cpus.len as int + if key == source_cpu_set { -1int } else { 1int }
                }
            }
        }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& post.ep_mp.perms_wf()
    &&& forall|key: RwLockEndpointPtr|
        #![trigger pre.ep_mp.spec_index(key)]
        #![trigger post.ep_mp.spec_index(key)]
        pre.ep_mp.dom().contains(key) ==> {
            let before = pre.ep_mp.spec_index(key);
            let after = post.ep_mp.spec_index(key);
            &&& !(key == endpoint_ptr) ==> after == before
        }
    &&& post.sched_mp.dom() == pre.sched_mp.dom()
    &&& post.sched_mp.perms_wf()
    &&& forall|key: RwLockSchedulerPtr|
        #![trigger pre.sched_mp.spec_index(key)]
        #![trigger post.sched_mp.spec_index(key)]
        pre.sched_mp.dom().contains(key) ==> {
            let before = pre.sched_mp.spec_index(key);
            let after = post.sched_mp.spec_index(key);
            &&& !(key == peer_scheduler_ptr) ==> after == before
        }
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_cpus(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& post.irt == pre.irt
    &&& post.pcid_needflush == pre.pcid_needflush
    &&& post.cpu_published == pre.cpu_published
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& forall|cpu_i: CpuId|
        #![trigger pre.cpu_arr.spec_index(cpu_i)]
        #![trigger post.cpu_arr.spec_index(cpu_i)]
        index_valid(NUM_CPUS, cpu_i) && (!transferred || cpu_i != transfer_cpu_id)
            ==> post.cpu_arr.spec_index(cpu_i) == pre.cpu_arr.spec_index(cpu_i)
}

#[verifier::opaque]
pub open spec fn ipc_cpu_rendezvous_transition_inputs(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& pre.inv()
    &&& index_valid(NUM_CPUS, transfer_cpu_id)
    &&& current_thread_ptr != peer_thread_ptr
    &&& source_container != target_container
    &&& source_cpu_set != target_cpu_set
}

/// Dequeues and schedules the endpoint waiter and, on success, moves the Off
/// CPU between the source and target CPU sets, preserving PCID and published state.
pub open spec fn ipc_cpu_rendezvous_transition(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
    transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& ipc_cpu_rendezvous_transition_pages(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_containers(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_processes(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_threads(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_allocators(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_tables(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_objects(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_cpus(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
    &&& ipc_cpu_rendezvous_transition_inputs(
        pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container,
        source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id,
    )
}
}

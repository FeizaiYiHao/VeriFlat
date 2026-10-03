use vstd::prelude::*;
use veriflat_kernel_core::*;

verus! {
/// Container-tree domain closure, subtree/uppertree duality, ancestor transitivity, and a parent
/// being an ancestor.
#[verifier::opaque]
pub open spec fn kernel_u_container_tree_wf(u: KernelU) -> bool {
    &&& forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].subtree_set.contains(d)]
        u.container_map.dom().contains(c) && u.container_map[c].subtree_set.contains(d) ==> u.container_map.dom().contains(d)
    &&& forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].uppertree_seq.contains(d)]
        u.container_map.dom().contains(c) && u.container_map[c].uppertree_seq.contains(d) ==> u.container_map.dom().contains(d)
    &&& forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].subtree_set.contains(d)] #![trigger u.container_map[d].uppertree_seq.contains(c)]
        u.container_map.dom().contains(c) && u.container_map.dom().contains(d) ==> u.container_map[c].subtree_set.contains(d) == u.container_map[d].uppertree_seq.contains(c)
    &&& forall|c: RwLockContainerPtr, d: RwLockContainerPtr, e: RwLockContainerPtr|
        #![trigger u.container_map[e].uppertree_seq.contains(d), u.container_map[d].uppertree_seq.contains(c)]
        u.container_map.dom().contains(e) && u.container_map[e].uppertree_seq.contains(d) && u.container_map[d].uppertree_seq.contains(c)
        ==> u.container_map[e].uppertree_seq.contains(c)
    &&& forall|c: RwLockContainerPtr| #![trigger u.container_map[c].parent] u.container_map.dom().contains(c) && u.container_map[c].parent is Some
        ==> u.container_map.dom().contains(u.container_map[c].parent->Some_0) && u.container_map[c].uppertree_seq.contains(u.container_map[c].parent->Some_0)
}

/// Process-container membership and same-container process ancestry.
#[verifier::opaque]
pub open spec fn kernel_u_process_ownership_wf(u: KernelU) -> bool {
    &&& forall|p: RwLockProcessPtr| #![trigger u.process_map.dom().contains(p)] u.process_map.dom().contains(p) ==> {
        &&& u.container_map.dom().contains(u.process_map[p].owning_container)
        &&& u.container_map[u.process_map[p].owning_container].owned_processes.contains(p)
    }
    &&& forall|c: RwLockContainerPtr, p: RwLockProcessPtr| #![trigger u.container_map[c].owned_processes.contains(p)]
        u.container_map.dom().contains(c) && u.container_map[c].owned_processes.contains(p) ==> u.process_map.dom().contains(p) && u.process_map[p].owning_container == c
    &&& forall|p: RwLockProcessPtr, q: RwLockProcessPtr| #![trigger u.process_map[p].uppertree_seq.contains(q)]
        u.process_map.dom().contains(p) && u.process_map[p].uppertree_seq.contains(q)
        ==> u.process_map.dom().contains(q) && u.process_map[q].owning_container == u.process_map[p].owning_container
}

/// Thread-process-container membership and scheduler membership.
#[verifier::opaque]
pub open spec fn kernel_u_thread_ownership_wf(u: KernelU) -> bool {
    &&& forall|t: RwLockThreadPtr| #![trigger u.thread_map.dom().contains(t)] u.thread_map.dom().contains(t) ==> {
        &&& u.container_map.dom().contains(u.thread_map[t].owning_container)
        &&& u.container_map[u.thread_map[t].owning_container].owned_threads.contains(t)
        &&& u.process_map.dom().contains(u.thread_map[t].owning_proc)
        &&& u.process_map[u.thread_map[t].owning_proc].owning_container == u.thread_map[t].owning_container
        &&& u.process_map[u.thread_map[t].owning_proc].owned_threads.contains(t)
    }
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr| #![trigger u.container_map[c].owned_threads.contains(t)]
        u.container_map.dom().contains(c) && u.container_map[c].owned_threads.contains(t) ==> u.thread_map.dom().contains(t) && u.thread_map[t].owning_container == c
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr| #![trigger u.container_map[c].scheduler.contains(t)]
        u.container_map.dom().contains(c) && u.container_map[c].scheduler.contains(t) ==> u.thread_map.dom().contains(t) && u.thread_map[t].owning_container == c
}

/// Endpoint-container membership, descriptor references, and queue membership.
#[verifier::opaque]
pub open spec fn kernel_u_endpoint_ownership_wf(u: KernelU) -> bool {
    &&& forall|e: RwLockEndpointPtr| #![trigger u.endpoint_map.dom().contains(e)] u.endpoint_map.dom().contains(e) ==> {
        &&& u.container_map.dom().contains(u.endpoint_map[e].owning_container)
        &&& u.container_map[u.endpoint_map[e].owning_container].owned_endpoints.contains(e)
    }
    &&& forall|c: RwLockContainerPtr, e: RwLockEndpointPtr| #![trigger u.container_map[c].owned_endpoints.contains(e)]
        u.container_map.dom().contains(c) && u.container_map[c].owned_endpoints.contains(e) ==> u.endpoint_map.dom().contains(e) && u.endpoint_map[e].owning_container == c
    &&& forall|t: RwLockThreadPtr, i: EndpointIdx| #![trigger u.thread_map[t].endpoint_descriptors[i as int]]
        u.thread_map.dom().contains(t) && edp_idx_valid(i) && u.thread_map[t].endpoint_descriptors[i as int] is Some ==> {
            &&& u.endpoint_map.dom().contains(u.thread_map[t].endpoint_descriptors[i as int]->Some_0)
            &&& u.endpoint_map[u.thread_map[t].endpoint_descriptors[i as int]->Some_0].owning_threads.contains((t, i))
        }
    &&& forall|e: RwLockEndpointPtr, t: RwLockThreadPtr, i: EndpointIdx| #![trigger u.endpoint_map[e].owning_threads.contains((t, i))]
        u.endpoint_map.dom().contains(e) && u.endpoint_map[e].owning_threads.contains((t, i))
        ==> u.thread_map.dom().contains(t) && edp_idx_valid(i) && u.thread_map[t].endpoint_descriptors[i as int] == Some(e)
    &&& forall|e: RwLockEndpointPtr, j: int| #![trigger u.endpoint_map[e].queue[j]]
        u.endpoint_map.dom().contains(e) && 0 <= j < u.endpoint_map[e].queue.len() ==> u.endpoint_map[e].queue.contains(u.endpoint_map[e].queue[j])
    &&& forall|e: RwLockEndpointPtr, t: RwLockThreadPtr| #![trigger u.endpoint_map[e].queue.contains(t)]
        u.endpoint_map.dom().contains(e) && u.endpoint_map[e].queue.contains(t)
        ==> u.thread_map.dom().contains(t) && u.thread_map[t].state.is_endpoint_waiting() && u.thread_map[t].blocking_endpoint_ptr->Some_0 == e
}

/// Cpu ownership of its current thread and process, and the running thread of each cpu.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_ownership_wf(u: KernelU) -> bool {
    &&& u.cpu_array.len() == NUM_CPUS
    &&& forall|i: CpuId| #![trigger u.cpu_array[i as int]] index_valid(NUM_CPUS, i) ==> {
        &&& u.container_map.dom().contains(u.cpu_array[i as int].owning_container)
        &&& u.cpu_array[i as int].current_thread is Some ==> {
            &&& u.thread_map.dom().contains(u.cpu_array[i as int].current_thread->Some_0)
            &&& u.thread_map[u.cpu_array[i as int].current_thread->Some_0].owning_container == u.cpu_array[i as int].owning_container
        }
        &&& u.cpu_array[i as int].current_process is Some ==> {
            &&& u.process_map.dom().contains(u.cpu_array[i as int].current_process->Some_0)
            &&& u.process_map[u.cpu_array[i as int].current_process->Some_0].owning_container == u.cpu_array[i as int].owning_container
        }
        &&& u.cpu_array[i as int].state is Running ==> {
            &&& u.cpu_array[i as int].current_thread is Some
            &&& u.thread_map[u.cpu_array[i as int].current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: i })
            &&& u.cpu_array[i as int].current_process == Some(u.thread_map[u.cpu_array[i as int].current_thread->Some_0].owning_proc)
        }
    }
}

/// A cpu has a current process exactly when it has a current thread.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_current_pair_wf(u: KernelU) -> bool {
    forall|i: CpuId| #![trigger u.cpu_array[i as int]]
        index_valid(NUM_CPUS, i) ==> (u.cpu_array[i as int].current_process is Some) == (u.cpu_array[i as int].current_thread is Some)
}

/// Ownership, reference, and tree facts that hold in the user projection of every well-formed kernel.
pub open spec fn kernel_u_ownership_wf(u: KernelU) -> bool {
    &&& kernel_u_container_tree_wf(u)
    &&& kernel_u_process_ownership_wf(u)
    &&& kernel_u_thread_ownership_wf(u)
    &&& kernel_u_endpoint_ownership_wf(u)
    &&& kernel_u_cpu_ownership_wf(u)
}

/// The user projection of a well-formed kernel satisfies the user-level ownership facts.
pub proof fn kernel_wf_implies_u_ownership_wf(krnl: &KernelK)
    requires krnl.inv(),
    ensures kernel_u_ownership_wf(kernel_k_to_kernel_u(*krnl)), kernel_u_cpu_current_pair_wf(kernel_k_to_kernel_u(*krnl)),
{
    reveal(kernel_k_to_kernel_u);
    assert(kernel_u_container_tree_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_container_tree_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf);
        reveal(container_root_wf); reveal(container_children_parent_wf); reveal(container_children_depth_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf);
    };
    assert(kernel_u_process_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_process_ownership_wf); reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_uppertree_seq_wf);
    };
    assert(kernel_u_thread_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_thread_ownership_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
    };
    assert(kernel_u_endpoint_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_endpoint_ownership_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
    };
    assert(kernel_u_cpu_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_cpu_ownership_wf); reveal(cpu_array_wf); reveal(container_cpu_wf); reveal(thread_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf);
    };
    assert(kernel_u_cpu_current_pair_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_cpu_current_pair_wf); reveal(cpu_array_wf); };
}
} // verus!

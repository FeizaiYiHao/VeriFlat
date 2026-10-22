use vstd::prelude::*;
use veriflat_kernel_core::*;

verus! {
/// Container-tree domain closure, subtree/uppertree duality, ancestor transitivity, a parent being an
/// ancestor, and a child naming its parent.
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
    &&& forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].children.contains(d)]
        u.container_map.dom().contains(c) && u.container_map[c].children.contains(d) ==> u.container_map.dom().contains(d) && u.container_map[d].parent == Some(c)
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

/// Thread-process-container membership and scheduler membership. A killed or dangling thread may have left its process,
/// which may already be gone.
#[verifier::opaque]
pub open spec fn kernel_u_thread_ownership_wf(u: KernelU) -> bool {
    &&& forall|t: RwLockThreadPtr| #![trigger u.thread_map.dom().contains(t)] u.thread_map.dom().contains(t) ==> {
        &&& u.container_map.dom().contains(u.thread_map[t].owning_container)
        &&& u.container_map[u.thread_map[t].owning_container].owned_threads.contains(t)
        &&& u.thread_map[t].blocking_endpoint_ptr is Some ==> u.thread_map[t].state.is_endpoint_waiting()
    }
    &&& forall|t: RwLockThreadPtr| #![trigger u.thread_map.dom().contains(t)]
        u.thread_map.dom().contains(t) && !(u.thread_map[t].state is KILLED) && !(u.thread_map[t].state is DANGLING) ==> {
        &&& u.process_map.dom().contains(u.thread_map[t].owning_proc)
        &&& u.process_map[u.thread_map[t].owning_proc].owning_container == u.thread_map[t].owning_container
        &&& u.process_map[u.thread_map[t].owning_proc].owned_threads.contains(t)
    }
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr| #![trigger u.container_map[c].owned_threads.contains(t)]
        u.container_map.dom().contains(c) && u.container_map[c].owned_threads.contains(t) ==> u.thread_map.dom().contains(t) && u.thread_map[t].owning_container == c
    &&& forall|c: RwLockContainerPtr, i: CpuId, t: RwLockThreadPtr| #![trigger u.container_map[c].scheduler[i as int].contains(t)]
        u.container_map.dom().contains(c) && index_valid(NUM_CPUS, i) && u.container_map[c].scheduler[i as int].contains(t)
            ==> u.thread_map.dom().contains(t) && u.thread_map[t].owning_container == c
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
            &&& u.cpu_array[i as int].state is Running
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

/// A PCI function in a process's set has that process as its root-table owner, so no two processes share one.
#[verifier::opaque]
pub open spec fn kernel_u_pci_ownership_wf(u: KernelU) -> bool {
    forall|p: RwLockProcessPtr, bdf: PciBdf| #![trigger u.process_map[p].owned_pci_functions.contains(bdf)]
        u.process_map.dom().contains(p) && u.process_map[p].owned_pci_functions.contains(bdf) ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2) && u.iommu_root_table.owners[bdf.0 as int][bdf.1 as int][bdf.2 as int] == p
}

/// Every ancestor of a container is shallower than it, so no container is its own ancestor.
#[verifier::opaque]
pub open spec fn kernel_u_container_depth_wf(u: KernelU) -> bool {
    forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].uppertree_seq.contains(d)]
        u.container_map.dom().contains(c) && u.container_map[c].uppertree_seq.contains(d) ==> u.container_map[d].depth < u.container_map[c].depth
}

/// A container that owns processes owns its root process.
#[verifier::opaque]
pub open spec fn kernel_u_container_root_process_wf(u: KernelU) -> bool {
    forall|c: RwLockContainerPtr| #![trigger u.container_map[c].root_process]
        u.container_map.dom().contains(c) && !u.container_map[c].owned_processes.is_empty() ==> u.container_map[c].owned_processes.contains(u.container_map[c].root_process)
}

/// A child of a process belongs to the process's container.
#[verifier::opaque]
pub open spec fn kernel_u_process_children_wf(u: KernelU) -> bool {
    forall|p: RwLockProcessPtr, c: RwLockProcessPtr| #![trigger u.process_map[p].children.contains(c)]
        u.process_map.dom().contains(p) && u.process_map[p].children.contains(c) ==> u.process_map.dom().contains(c) && u.process_map[c].owning_container == u.process_map[p].owning_container
}

/// A thread a process owns belongs to the process's container.
#[verifier::opaque]
pub open spec fn kernel_u_process_threads_wf(u: KernelU) -> bool {
    forall|p: RwLockProcessPtr, t: RwLockThreadPtr| #![trigger u.process_map[p].owned_threads.contains(t)]
        u.process_map.dom().contains(p) && u.process_map[p].owned_threads.contains(t) ==> u.thread_map.dom().contains(t) && u.thread_map[t].owning_container == u.process_map[p].owning_container
}

/// A running thread is the current thread of the cpu its state names.
#[verifier::opaque]
pub open spec fn kernel_u_running_thread_cpu_wf(u: KernelU) -> bool {
    forall|t: RwLockThreadPtr| #![trigger u.thread_map[t].state] u.thread_map.dom().contains(t) && u.thread_map[t].state is RUNNING
        ==> index_valid(NUM_CPUS, u.thread_map[t].state->RUNNING_cpu_id) && u.cpu_array[u.thread_map[t].state->RUNNING_cpu_id as int].current_thread == Some(t)
}

/// A thread waiting on an endpoint waits in that endpoint's queue.
#[verifier::opaque]
pub open spec fn kernel_u_endpoint_wait_wf(u: KernelU) -> bool {
    forall|t: RwLockThreadPtr| #![trigger u.thread_map[t].blocking_endpoint_ptr]
        u.thread_map.dom().contains(t) && u.thread_map[t].state.is_endpoint_waiting() && u.thread_map[t].blocking_endpoint_ptr is Some
        ==> u.endpoint_map.dom().contains(u.thread_map[t].blocking_endpoint_ptr->Some_0) && u.endpoint_map[u.thread_map[t].blocking_endpoint_ptr->Some_0].queue.contains(t)
}

/// Every endpoint has a holder, and a held endpoint belongs to its holder's container or to an ancestor of it.
#[verifier::opaque]
pub open spec fn kernel_u_endpoint_holder_wf(u: KernelU) -> bool {
    &&& forall|e: RwLockEndpointPtr| #![trigger u.endpoint_map[e].owning_threads] u.endpoint_map.dom().contains(e) ==> u.endpoint_map[e].owning_threads.len() != 0
    &&& forall|t: RwLockThreadPtr, i: EndpointIdx| #![trigger u.thread_map[t].endpoint_descriptors[i as int]]
        u.thread_map.dom().contains(t) && edp_idx_valid(i) && u.thread_map[t].endpoint_descriptors[i as int] is Some ==> {
            let owner = u.endpoint_map[u.thread_map[t].endpoint_descriptors[i as int]->Some_0].owning_container;
            owner == u.thread_map[t].owning_container || u.container_map[owner].subtree_set.contains(u.thread_map[t].owning_container)
        }
}

/// A page a container owns that holds a thread or an endpoint holds one of that container's objects.
#[verifier::opaque]
pub open spec fn kernel_u_object_page_owner_wf(u: KernelU) -> bool {
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr| #![trigger u.container_map[c].owned_pages.contains(t), u.thread_map.dom().contains(t)]
        u.container_map.dom().contains(c) && u.container_map[c].owned_pages.contains(t) && u.thread_map.dom().contains(t) ==> u.thread_map[t].owning_container == c
    &&& forall|c: RwLockContainerPtr, e: RwLockEndpointPtr| #![trigger u.container_map[c].owned_pages.contains(e), u.endpoint_map.dom().contains(e)]
        u.container_map.dom().contains(c) && u.container_map[c].owned_pages.contains(e) && u.endpoint_map.dom().contains(e) ==> u.endpoint_map[e].owning_container == c
}

/// A thread and the caller it serves share a container.
#[verifier::opaque]
pub open spec fn kernel_u_thread_caller_wf(u: KernelU) -> bool {
    forall|t: RwLockThreadPtr| #![trigger u.thread_map[t].caller] u.thread_map.dom().contains(t) && u.thread_map[t].caller is Some
        ==> u.thread_map.dom().contains(u.thread_map[t].caller->Some_0) && u.thread_map[u.thread_map[t].caller->Some_0].owning_container == u.thread_map[t].owning_container
}

/// A thread in IPC transit has a live running partner whose rendezvous names it as its peer.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_transit_wf(u: KernelU) -> bool {
    forall|d: RwLockThreadPtr| #![trigger u.thread_map[d].state] u.thread_map.dom().contains(d) && u.thread_map[d].state is IPC_TRANSIT ==> {
        let partner = u.thread_map[d].state->IPC_TRANSIT_partner;
        &&& u.thread_map.dom().contains(partner)
        &&& u.thread_map[partner].state is RUNNING
        &&& progress_peer_of(u.thread_map[partner].syscall_progress) == Some(d)
    }
}

/// Ownership, reference, and tree facts that hold in the user projection of every well-formed kernel.
pub open spec fn kernel_u_ownership_wf(u: KernelU) -> bool {
    &&& kernel_u_container_tree_wf(u)
    &&& kernel_u_process_ownership_wf(u)
    &&& kernel_u_thread_ownership_wf(u)
    &&& kernel_u_endpoint_ownership_wf(u)
    &&& kernel_u_cpu_ownership_wf(u)
    &&& kernel_u_pci_ownership_wf(u)
    &&& kernel_u_container_depth_wf(u)
    &&& kernel_u_container_root_process_wf(u)
    &&& kernel_u_process_children_wf(u)
    &&& kernel_u_process_threads_wf(u)
    &&& kernel_u_running_thread_cpu_wf(u)
    &&& kernel_u_endpoint_wait_wf(u)
    &&& kernel_u_endpoint_holder_wf(u)
    &&& kernel_u_object_page_owner_wf(u)
    &&& kernel_u_thread_caller_wf(u)
    &&& kernel_u_ipc_transit_wf(u)
}

/// The user projection of a well-formed kernel satisfies the user-level ownership facts.
pub proof fn kernel_wf_implies_u_ownership_wf(krnl: &KernelK)
    requires krnl.inv(),
    ensures
        kernel_u_ownership_wf(kernel_k_to_kernel_u(*krnl)),
        kernel_u_cpu_current_pair_wf(kernel_k_to_kernel_u(*krnl)),
{
    reveal(kernel_k_to_kernel_u);
    assert(kernel_u_container_tree_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_container_tree_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf);
        reveal(container_root_wf); reveal(container_children_parent_wf); reveal(container_children_depth_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf);
    };
    assert(kernel_u_process_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_process_ownership_wf); reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_uppertree_seq_wf); };
    assert(kernel_u_thread_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_thread_ownership_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(thread_perms_wf);
        reveal(scheduler_shards_of);
    };
    assert(kernel_u_endpoint_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_endpoint_ownership_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); };
    assert(kernel_u_cpu_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_cpu_ownership_wf); reveal(cpu_array_wf); reveal(container_cpu_wf); reveal(thread_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); };
    assert(kernel_u_cpu_current_pair_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_cpu_current_pair_wf); reveal(cpu_array_wf); };
    assert(kernel_u_pci_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_pci_ownership_wf); reveal(process_pci_function_ownership_wf); reveal(IommuRootTable::user_view); };
    assert(kernel_u_container_depth_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_container_depth_wf); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf); reveal(container_perms_wf); };
    assert(kernel_u_container_root_process_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_container_root_process_wf); reveal(per_container_process_tree_wf); reveal(process_root_wf); };
    assert(kernel_u_process_children_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_process_children_wf); reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_children_parent_wf);
    };
    assert(kernel_u_process_threads_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_process_threads_wf); reveal(process_thread_wf); };
    assert(kernel_u_running_thread_cpu_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_running_thread_cpu_wf); reveal(thread_cpu_wf); reveal(cpu_array_wf); };
    assert(kernel_u_endpoint_wait_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_endpoint_wait_wf); reveal(thread_endpoint_queue_wf); };
    assert(kernel_u_endpoint_holder_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_endpoint_holder_wf); reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf);
        assert forall|e: RwLockEndpointPtr| #![trigger krnl.ep_mp.dom().contains(e)] krnl.ep_mp.dom().contains(e) implies krnl.ep_mp.spec_index(e).view().owning_threads.view().len() != 0 by {
            endpoint_perms_wf_at(krnl.ep_mp, e);
        };
    };
    assert(kernel_u_object_page_owner_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_object_page_owner_wf); reveal(container_page_owner_wf); reveal(thread_pages_wf); reveal(endpoint_pages_wf); reveal(page_object_owner_wf);
        reveal(container_thread_wf); reveal(container_endpoint_wf); page_ptr_roundtrip(); page_ptr_valid_imply_page_index_valid();
    };
    assert(kernel_u_thread_caller_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_thread_caller_wf); reveal(thread_caller_callee_wf); };
    assert(kernel_u_ipc_transit_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_ipc_transit_wf); reveal(thread_perms_wf); reveal(thread_ipc_transit_wf); };
}
} // verus!

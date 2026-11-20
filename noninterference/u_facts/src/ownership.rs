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

/// Cpu ownership of its current thread and process, which is live, and the running thread of each cpu.
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
            &&& u.process_map[u.cpu_array[i as int].current_process->Some_0].pagetable is Some
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

/// A PCI function in a live process's page-table function array is owned by that process in the root table, and an owned
/// function sits in its owner's array unless the owner is a zombie, so no two processes hold one.
#[verifier::opaque]
pub open spec fn kernel_u_pci_ownership_wf(u: KernelU) -> bool {
    &&& forall|p: RwLockProcessPtr, bdf: PciBdf| #![trigger u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(bdf)]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(bdf)
            ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2) && u.iommu_root_table.owners[bdf.0 as int][bdf.1 as int][bdf.2 as int] == Some(p)
    &&& forall|b: usize, d: usize, f: usize| #![trigger u.iommu_root_table.owners[b as int][d as int][f as int]]
        pci_bdf_valid(b, d, f) && u.iommu_root_table.owners[b as int][d as int][f as int] is Some ==> {
            let p = u.iommu_root_table.owners[b as int][d as int][f as int]->Some_0;
            &&& u.process_map.dom().contains(p)
            &&& u.process_map[p].pagetable is Some ==> u.process_map[p].pagetable->Some_0.pci_functions.dom().contains((b, d, f))
        }
}

/// Every live process's IO leaves map pages of BARs of functions in its page table's PCI function array (a 2M IO leaf maps a
/// 2M chunk of one BAR), and no RAM leaf of a page table or an IOMMU table covers a BAR page; the BAR table is well formed.
#[verifier::opaque]
pub open spec fn kernel_u_io_leaf_wf(u: KernelU) -> bool {
    &&& pci_bar_table_wf(u.pci_bars)
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(va) ==> {
            let e = u.process_map[p].pagetable->Some_0.mapping_4k[va];
            &&& e.is_io ==> pci_bar_function_of_page(u.pci_bars, e.addr) is Some
                && u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(pci_bar_function_of_page(u.pci_bars, e.addr)->0)
            &&& !e.is_io ==> page_ptr_valid(e.addr) && !pci_bar_page(u.pci_bars, e.addr)
        }
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_2m[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(va) ==> {
            let e = u.process_map[p].pagetable->Some_0.mapping_2m[va];
            &&& e.is_io ==> pci_bar_function_of_page(u.pci_bars, e.addr) is Some && pci_bar_2m_chunk(u.pci_bars, e.addr)
                && u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(pci_bar_function_of_page(u.pci_bars, e.addr)->0)
            &&& !e.is_io ==> page_ptr_2m_valid(e.addr) && forall|q: PAddr| #![trigger pci_bar_page(u.pci_bars, q)] e.addr <= q < e.addr + 0x200000 ==> !pci_bar_page(u.pci_bars, q)
        }
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_1g[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_1g.dom().contains(va) ==> {
            let e = u.process_map[p].pagetable->Some_0.mapping_1g[va];
            &&& page_ptr_1g_valid(e.addr)
            &&& forall|q: PAddr| #![trigger pci_bar_page(u.pci_bars, q)] e.addr <= q < e.addr + 0x4000_0000 ==> !pci_bar_page(u.pci_bars, q)
        }
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].iommu_table->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].iommu_table is Some && u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(va) ==> {
            let e = u.process_map[p].iommu_table->Some_0.mapping_4k[va];
            &&& page_ptr_valid(e.addr)
            &&& !pci_bar_page(u.pci_bars, e.addr)
        }
}

/// A container without a parent has every other container in its subtree: it is the root of the container tree.
#[verifier::opaque]
pub open spec fn kernel_u_container_root_wf(u: KernelU) -> bool {
    forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].parent, u.container_map[c].subtree_set.contains(d)]
        u.container_map.dom().contains(c) && u.container_map.dom().contains(d) && u.container_map[c].parent is None && c != d ==> u.container_map[c].subtree_set.contains(d)
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
    &&& kernel_u_io_leaf_wf(u)
    &&& kernel_u_container_root_wf(u)
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
        reveal(container_root_wf); reveal(container_children_parent_wf); reveal(container_uppertree_seq_parent_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf);
    };
    assert(kernel_u_process_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_process_ownership_wf); reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_uppertree_seq_wf); };
    assert(kernel_u_thread_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        reveal(kernel_u_thread_ownership_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(thread_perms_wf);
        reveal(scheduler_shards_of);
    };
    assert(kernel_u_endpoint_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_endpoint_ownership_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); };
    assert(kernel_u_cpu_ownership_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_cpu_ownership_wf); reveal(cpu_array_wf); reveal(container_cpu_wf); reveal(thread_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf);
        reveal(process_cpu_wf);
    };
    assert(kernel_u_cpu_current_pair_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_cpu_current_pair_wf); reveal(cpu_array_wf); };
    assert(kernel_u_pci_ownership_wf(kernel_k_to_kernel_u(*krnl))) by {
        let u = kernel_k_to_kernel_u(*krnl);
        reveal(kernel_u_pci_ownership_wf); reveal(IommuRootTable::user_view);
        assert forall|p: RwLockProcessPtr, bdf: PciBdf| #![trigger u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(bdf)]
            u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(bdf)
            implies pci_bdf_valid(bdf.0, bdf.1, bdf.2) && u.iommu_root_table.owners[bdf.0 as int][bdf.1 as int][bdf.2 as int] == Some(p) by {
            process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, p);
            pci_function_ownership_wf_pagetable_at(krnl.irt.view(), krnl.prc_mp, krnl.pt_mp, krnl.prc_mp.spec_index(p).view().pagetable, bdf);
        };
        assert forall|b: usize, d: usize, f: usize| #![trigger u.iommu_root_table.owners[b as int][d as int][f as int]]
            pci_bdf_valid(b, d, f) && u.iommu_root_table.owners[b as int][d as int][f as int] is Some implies {
                let p = u.iommu_root_table.owners[b as int][d as int][f as int]->Some_0;
                &&& u.process_map.dom().contains(p)
                &&& u.process_map[p].pagetable is Some ==> u.process_map[p].pagetable->Some_0.pci_functions.dom().contains((b, d, f))
            } by {
            pci_function_ownership_wf_function_at(krnl.irt.view(), krnl.prc_mp, krnl.pt_mp, b, d, f);
        };
    };
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
        reveal(kernel_u_object_page_owner_wf); reveal(container_owned_pages_wf); reveal(thread_pages_wf); reveal(endpoint_pages_wf); reveal(page_object_owner_wf);
        reveal(container_thread_wf); reveal(container_endpoint_wf); page_ptr_roundtrip(); page_ptr_valid_imply_page_index_valid();
    };
    assert(kernel_u_thread_caller_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_thread_caller_wf); reveal(thread_caller_callee_wf); };
    assert(kernel_u_ipc_transit_wf(kernel_k_to_kernel_u(*krnl))) by { reveal(kernel_u_ipc_transit_wf); reveal(thread_perms_wf); reveal(thread_ipc_transit_wf); };
    kernel_wf_implies_u_io_leaf_wf(krnl);
    assert(kernel_u_container_root_wf(kernel_k_to_kernel_u(*krnl))) by {
        let u = kernel_k_to_kernel_u(*krnl);
        reveal(kernel_u_container_root_wf); reveal(container_root_wf); reveal(container_uppertree_seq_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf);
        assert forall|c: RwLockContainerPtr, d: RwLockContainerPtr| #![trigger u.container_map[c].parent, u.container_map[c].subtree_set.contains(d)]
            u.container_map.dom().contains(c) && u.container_map.dom().contains(d) && u.container_map[c].parent is None && c != d implies u.container_map[c].subtree_set.contains(d) by {
            let upper = krnl.ctn_mp.spec_index(d).view().uppertree_seq.view();
            let r = upper[0];
            assert(c == krnl.rt_ctn);
            assert(upper.len() > 0);
            assert(upper.contains(r));
            assert(upper[krnl.ctn_mp.spec_index(r).view_rodata().view().depth as int] == r);
            assert(krnl.ctn_mp.spec_index(r).view_rodata().view().depth == 0);
        };
    };
}

/// The page `pg_idx`, not `Unavailable`, is no BAR page.
proof fn page_not_unavailable_implies_not_bar_page(krnl: &KernelK, pg_idx: PageIndex)
    requires krnl.inv(), index_valid(NUM_PAGES, pg_idx), !(krnl.pg_arr.spec_index(pg_idx).view().view().state is Unavailable),
    ensures !pci_bar_page(krnl.pci_bars.view(), page_index2page_ptr(pg_idx)),
{ pci_bar_pages_unavailable_wf_at(krnl.pci_bars.view(), krnl.pg_arr, pg_idx); }

/// A BAR page is 4K aligned.
pub proof fn bar_page_implies_aligned(bars: Seq<PciBarEntry>, q: PAddr)
    requires pci_bar_page(bars, q),
    ensures q % 0x1000 == 0,
{
    let i = pci_bar_entry_of_page(bars, q)->0;
    assert(bars[i].envelope_contains(q));
    assert(PAGE_SZ_4K == 0x1000) by (compute);
}

/// A page in the envelope of BAR entry `i` is a BAR page of entry `i`'s function.
pub proof fn bar_envelope_implies_function_of_page(bars: Seq<PciBarEntry>, i: int, p: PAddr)
    requires pci_bar_table_wf(bars), 0 <= i < bars.len(), bars[i].envelope_contains(p),
    ensures pci_bar_page(bars, p), pci_bar_function_of_page(bars, p) == Some(bars[i].bdf),
{
    let k = pci_bar_entry_of_page(bars, p)->0;
    assert(pci_bar_entry_of_page(bars, p) is Some && bars[k].bdf == bars[i].bdf) by { pci_bar_table_wf_pair_at(bars, i, k, p); };
}

/// A 4K-aligned page inside the 2M BAR chunk at `d` is a BAR page of the chunk's function.
pub proof fn bar_chunk_page_implies_function_of_chunk(bars: Seq<PciBarEntry>, d: PAddr, p: PAddr)
    requires pci_bar_table_wf(bars), pci_bar_2m_chunk(bars, d), p % 0x1000 == 0, d <= p < d + 0x200000,
    ensures pci_bar_page(bars, p), pci_bar_function_of_page(bars, p) == pci_bar_function_of_page(bars, d),
{
    let e = pci_bar_entry_of_page(bars, d)->0;
    assert(bars[e].envelope_contains(d));
    assert(PAGE_SZ_4K == 0x1000 && PAGE_SZ_2M == 0x200000) by (compute);
    assert(bars[e].envelope_contains(p));
    bar_envelope_implies_function_of_page(bars, e, p);
}

/// The region of `count` 4K pages headed by the page `head`, which is `Mapped2m` (`count` 512) or `Mapped1g` (`count` 262144),
/// holds no BAR page.
proof fn mapped_huge_page_implies_no_bar_page(krnl: &KernelK, head: PageIndex, count: int, q: PAddr)
    requires
        krnl.inv(),
        index_valid(NUM_PAGES, head),
        count == 512 && krnl.pg_arr.spec_index(head).view().view().state is Mapped2m && head % 512 == 0
            || count == 262144 && krnl.pg_arr.spec_index(head).view().view().state is Mapped1g && head % 262144 == 0,
        head as int * 4096 <= q < head as int * 4096 + count * 4096,
    ensures !pci_bar_page(krnl.pci_bars.view(), q),
{
    if pci_bar_page(krnl.pci_bars.view(), q) {
        bar_page_implies_aligned(krnl.pci_bars.view(), q);
        let j = (q / 4096) as usize;
        assert(j as int * 4096 == q && head <= j < head + count) by (nonlinear_arith)
            requires q % 0x1000 == 0, head as int * 4096 <= q < head as int * 4096 + count * 4096, j == q / 4096;
        assert(NUM_PAGES == 1024 * 1024);
        assert(j < NUM_PAGES) by (nonlinear_arith) requires head < 1024 * 1024, j < head + count, count == 512 && head % 512 == 0 || count == 262144 && head % 262144 == 0;
        if j != head {
            hugepage_2m_wf_tail_forward_at(krnl.pg_arr, head, j);
            hugepage_1g_wf_tail_forward_at(krnl.pg_arr, head, j);
        }
        page_not_unavailable_implies_not_bar_page(krnl, j);
    }
}

/// The user projection of a well-formed kernel satisfies `kernel_u_io_leaf_wf`.
proof fn kernel_wf_implies_u_io_leaf_wf(krnl: &KernelK)
    requires krnl.inv(),
    ensures kernel_u_io_leaf_wf(kernel_k_to_kernel_u(*krnl)),
{
    let u = kernel_k_to_kernel_u(*krnl);
    let bars = krnl.pci_bars.view();
    reveal(kernel_k_to_kernel_u); reveal(kernel_u_io_leaf_wf);
    page_ptr_roundtrip(); page_ptr_valid_imply_page_index_valid();
    assert forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(va) implies {
            let e = u.process_map[p].pagetable->Some_0.mapping_4k[va];
            &&& e.is_io ==> pci_bar_function_of_page(u.pci_bars, e.addr) is Some
                && u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(pci_bar_function_of_page(u.pci_bars, e.addr)->0)
            &&& !e.is_io ==> page_ptr_valid(e.addr) && !pci_bar_page(u.pci_bars, e.addr)
        } by {
        let pt = krnl.prc_mp.spec_index(p).view().pagetable;
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, p);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pt);
        pagetable_pci_mappings_wf_present_4k_at(bars, krnl.pt_mp, krnl.pt_lower.view(), pt, va);
        mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pt, va);
        let e = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).mapping_4k()[va];
        if !e.is_io { page_not_unavailable_implies_not_bar_page(krnl, page_ptr2page_index(e.addr)); }
    };
    assert forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_2m[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(va) implies {
            let e = u.process_map[p].pagetable->Some_0.mapping_2m[va];
            &&& e.is_io ==> pci_bar_function_of_page(u.pci_bars, e.addr) is Some && pci_bar_2m_chunk(u.pci_bars, e.addr)
                && u.process_map[p].pagetable->Some_0.pci_functions.dom().contains(pci_bar_function_of_page(u.pci_bars, e.addr)->0)
            &&& !e.is_io ==> page_ptr_2m_valid(e.addr) && forall|q: PAddr| #![trigger pci_bar_page(u.pci_bars, q)] e.addr <= q < e.addr + 0x200000 ==> !pci_bar_page(u.pci_bars, q)
        } by {
        let pt = krnl.prc_mp.spec_index(p).view().pagetable;
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt);
        let e = c.mapping_2m()[va];
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, p);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pt);
        pagetable_pci_mappings_wf_present_2m_at(bars, krnl.pt_mp, krnl.pt_lower.view(), pt, va);
        if e.is_io {
            let f = pci_bar_function_of_page(bars, e.addr)->0;
            pagetable_pci_mappings_wf_mapping_at(bars, krnl.pt_mp, krnl.pt_lower.view(), pt, f, (va, PageSize::SZ2m));
            spec_va_2m_valid_index_roundtrip(va);
            reveal(WholePageTable::wf_mapping_2m);
            assert(c.lower.mapping_2m.spec_index(spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0))) == e);
            c.spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        } else {
            reveal(mapped_2m_page_pagetable_wf);
            let head = page_ptr2page_index(e.addr);
            assert(head % 512 == 0 && head as int * 4096 == e.addr) by (nonlinear_arith) requires e.addr % 0x200000 == 0, head == e.addr / 4096;
            assert forall|q: PAddr| #![trigger pci_bar_page(u.pci_bars, q)] e.addr <= q < e.addr + 0x200000 implies !pci_bar_page(u.pci_bars, q) by {
                mapped_huge_page_implies_no_bar_page(krnl, head, 512, q);
            };
        }
    };
    assert forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_1g[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_1g.dom().contains(va) implies {
            let e = u.process_map[p].pagetable->Some_0.mapping_1g[va];
            &&& page_ptr_1g_valid(e.addr)
            &&& forall|q: PAddr| #![trigger pci_bar_page(u.pci_bars, q)] e.addr <= q < e.addr + 0x4000_0000 ==> !pci_bar_page(u.pci_bars, q)
        } by {
        let pt = krnl.prc_mp.spec_index(p).view().pagetable;
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt);
        let e = c.mapping_1g()[va];
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, p);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pt);
        reveal(mapped_1g_page_pagetable_wf);
        let head = page_ptr2page_index(e.addr);
        assert(head % 262144 == 0 && head as int * 4096 == e.addr) by (nonlinear_arith) requires e.addr % 0x40000000 == 0, head == e.addr / 4096;
        assert forall|q: PAddr| #![trigger pci_bar_page(u.pci_bars, q)] e.addr <= q < e.addr + 0x4000_0000 implies !pci_bar_page(u.pci_bars, q) by {
            mapped_huge_page_implies_no_bar_page(krnl, head, 262144, q);
        };
    };
    assert forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].iommu_table->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].iommu_table is Some && u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(va) implies {
            let e = u.process_map[p].iommu_table->Some_0.mapping_4k[va];
            &&& page_ptr_valid(e.addr)
            &&& !pci_bar_page(u.pci_bars, e.addr)
        } by {
        reveal(process_iommu_table_wf); reveal(page_iommu_table_wf);
        let it = krnl.prc_mp.spec_index(p).view().iommu_table->Some_0;
        iommu_table_perms_wf_at(krnl.it_mp, it);
        let e = krnl.it_mp.spec_index(it).view().mapping_4k()[va];
        page_not_unavailable_implies_not_bar_page(krnl, page_ptr2page_index(e.addr));
    };
}
} // verus!

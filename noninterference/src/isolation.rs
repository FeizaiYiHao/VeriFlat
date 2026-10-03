use vstd::prelude::*;
use crate::*;

verus! {
/// The container subtrees rooted at `a` and `b` share no container.
pub open spec fn domains_disjoint(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr) -> bool {
    &&& u.container_map.dom().contains(a)
    &&& u.container_map.dom().contains(b)
    &&& !in_domain(u, a, b)
    &&& !in_domain(u, b, a)
    &&& forall|c: RwLockContainerPtr| #![trigger u.container_map[a].subtree_set.contains(c)] #![trigger u.container_map[b].subtree_set.contains(c)]
        !(u.container_map[a].subtree_set.contains(c) && u.container_map[b].subtree_set.contains(c))
}

/// Processes of the domain map memory only through 4K page-table entries. No syscall creates 2M, 1G, or
/// IOMMU mappings, so `memory_iso` over 4K entries covers all memory the domain maps.
pub open spec fn domain_4k_only(u: KernelU, root: RwLockContainerPtr) -> bool {
    forall|p: RwLockProcessPtr| #![trigger u.process_map[p]]
        u.process_map.dom().contains(p) && in_domain(u, root, u.process_map[p].owning_container) ==> {
            &&& u.process_map[p].pagetable is Some ==> u.process_map[p].pagetable->Some_0.mapping_2m.dom().is_empty()
            &&& u.process_map[p].pagetable is Some ==> u.process_map[p].pagetable->Some_0.mapping_1g.dom().is_empty()
            &&& u.process_map[p].iommu_table is Some ==> u.process_map[p].iommu_table->Some_0.mapping_4k.dom().is_empty()
            &&& u.process_map[p].iommu_table is Some ==> u.process_map[p].iommu_table->Some_0.mapping_2m.dom().is_empty()
            &&& u.process_map[p].iommu_table is Some ==> u.process_map[p].iommu_table->Some_0.mapping_1g.dom().is_empty()
        }
}

/// No physical page is mapped both by a process of `a` and by a process of `b`.
pub open spec fn memory_iso(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr) -> bool {
    forall|p: RwLockProcessPtr, va: VAddr, q: RwLockProcessPtr, vb: VAddr|
        #![trigger u.process_map[p].pagetable->Some_0.mapping_4k[va], u.process_map[q].pagetable->Some_0.mapping_4k[vb]]
        u.process_map.dom().contains(p) && in_domain(u, a, u.process_map[p].owning_container) && u.process_map[p].pagetable is Some
        && u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(va)
        && u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
        && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(vb)
        ==> u.process_map[p].pagetable->Some_0.mapping_4k[va].addr != u.process_map[q].pagetable->Some_0.mapping_4k[vb].addr
}

/// No endpoint is held by threads of both domains, no endpoint held by a thread of one domain is owned
/// by the other domain, and no endpoint held by a thread of one domain queues a thread of the other.
pub open spec fn endpoint_iso(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr) -> bool {
    &&& forall|e: RwLockEndpointPtr, t1: RwLockThreadPtr, i1: EndpointIdx, t2: RwLockThreadPtr, i2: EndpointIdx|
        #![trigger u.endpoint_map[e].owning_threads.contains((t1, i1)), u.endpoint_map[e].owning_threads.contains((t2, i2))]
        u.endpoint_map.dom().contains(e) && u.endpoint_map[e].owning_threads.contains((t1, i1)) && u.endpoint_map[e].owning_threads.contains((t2, i2))
        && in_domain(u, a, u.thread_map[t1].owning_container) ==> !in_domain(u, b, u.thread_map[t2].owning_container)
    &&& forall|e: RwLockEndpointPtr, t: RwLockThreadPtr, i: EndpointIdx| #![trigger u.endpoint_map[e].owning_threads.contains((t, i))]
        u.endpoint_map.dom().contains(e) && u.endpoint_map[e].owning_threads.contains((t, i)) ==> {
            &&& in_domain(u, a, u.thread_map[t].owning_container) ==> !in_domain(u, b, u.endpoint_map[e].owning_container)
            &&& in_domain(u, b, u.thread_map[t].owning_container) ==> !in_domain(u, a, u.endpoint_map[e].owning_container)
        }
    &&& forall|e: RwLockEndpointPtr, t: RwLockThreadPtr, i: EndpointIdx, j: int|
        #![trigger u.endpoint_map[e].owning_threads.contains((t, i)), u.endpoint_map[e].queue[j]]
        u.endpoint_map.dom().contains(e) && u.endpoint_map[e].owning_threads.contains((t, i)) && 0 <= j < u.endpoint_map[e].queue.len() ==> {
            &&& in_domain(u, a, u.thread_map[t].owning_container) ==> !in_domain(u, b, u.thread_map[u.endpoint_map[e].queue[j]].owning_container)
            &&& in_domain(u, b, u.thread_map[t].owning_container) ==> !in_domain(u, a, u.thread_map[u.endpoint_map[e].queue[j]].owning_container)
        }
}

/// The peer of the IPC rendezvous that `progress` records in flight.
pub open spec fn progress_peer(progress: Option<SyscallProgress>) -> Option<RwLockThreadPtr> {
    match progress {
        Some(SyscallProgress::IpcPages { peer, .. }) => Some(peer),
        Some(SyscallProgress::IpcEndpoint { peer, .. }) => Some(peer),
        Some(SyscallProgress::Share4k { origin: Share4kOrigin::IpcPages { peer }, .. }) => Some(peer),
        _ => None,
    }
}

/// Every IPC rendezvous a thread of `x` has in flight is with a live peer outside `y`, and the channel that
/// peer waits on is a live endpoint that `y` neither owns nor holds.
pub open spec fn inflight_iso(u: KernelU, x: RwLockContainerPtr, y: RwLockContainerPtr) -> bool {
    forall|t: RwLockThreadPtr| #![trigger u.thread_map[t].syscall_progress]
        u.thread_map.dom().contains(t) && in_domain(u, x, u.thread_map[t].owning_container) && progress_peer(u.thread_map[t].syscall_progress) is Some ==> {
            let peer = progress_peer(u.thread_map[t].syscall_progress)->Some_0;
            let channel = u.thread_map[peer].blocking_endpoint_ptr->Some_0;
            &&& u.thread_map.dom().contains(peer)
            &&& !in_domain(u, y, u.thread_map[peer].owning_container)
            &&& u.thread_map[peer].blocking_endpoint_ptr is Some ==> u.endpoint_map.dom().contains(channel)
            &&& u.thread_map[peer].blocking_endpoint_ptr is Some ==> !in_domain(u, y, u.endpoint_map[channel].owning_container)
            &&& u.thread_map[peer].blocking_endpoint_ptr is Some ==> forall|h: RwLockThreadPtr, i: EndpointIdx|
                #![trigger u.endpoint_map[channel].owning_threads.contains((h, i))]
                u.endpoint_map[channel].owning_threads.contains((h, i)) ==> !in_domain(u, y, u.thread_map[h].owning_container)
        }
}

/// Isolation between the container subtrees rooted at `a` and `b`.
pub open spec fn isolated(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr) -> bool {
    &&& domains_disjoint(u, a, b)
    &&& domain_4k_only(u, a)
    &&& domain_4k_only(u, b)
    &&& memory_iso(u, a, b)
    &&& endpoint_iso(u, a, b)
    &&& inflight_iso(u, a, b)
    &&& inflight_iso(u, b, a)
}
} // verus!

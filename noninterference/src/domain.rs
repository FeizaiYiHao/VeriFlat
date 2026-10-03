use vstd::prelude::*;
use crate::*;

verus! {
/// Container `c` lies in the container subtree rooted at `root`.
pub open spec fn in_domain(u: KernelU, root: RwLockContainerPtr, c: RwLockContainerPtr) -> bool {
    c == root || u.container_map[root].subtree_set.contains(c)
}

/// What the domain rooted at `root` observes, including lock modes: its containers; every process,
/// thread, and endpoint one of its containers owns; every endpoint its threads hold, per descriptor;
/// its cpus; and the first kernel L4 index, which bounds every user range.
#[verifier::ext_equal]
pub ghost struct DomainView {
    pub containers: Map<RwLockContainerPtr, ContainerU>,
    pub processes: Map<RwLockProcessPtr, ProcessU>,
    pub threads: Map<RwLockThreadPtr, ThreadU>,
    pub endpoints: Map<RwLockEndpointPtr, EndpointU>,
    pub held_endpoints: Map<RwLockThreadPtr, Seq<Option<EndpointU>>>,
    pub cpus: Seq<Option<CpuU>>,
    pub kernel_l4_end: usize,
}

pub open spec fn domain_view(u: KernelU, root: RwLockContainerPtr) -> DomainView {
    let threads = u.thread_map.dom().filter(|t: RwLockThreadPtr| in_domain(u, root, u.thread_map[t].owning_container));
    DomainView {
        containers: Map::new(u.container_map.dom().filter(|c: RwLockContainerPtr| in_domain(u, root, c)), |c: RwLockContainerPtr| u.container_map[c]),
        processes: Map::new(u.process_map.dom().filter(|p: RwLockProcessPtr| in_domain(u, root, u.process_map[p].owning_container)),
            |p: RwLockProcessPtr| u.process_map[p]),
        threads: Map::new(threads, |t: RwLockThreadPtr| u.thread_map[t]),
        endpoints: Map::new(u.endpoint_map.dom().filter(|e: RwLockEndpointPtr| in_domain(u, root, u.endpoint_map[e].owning_container)),
            |e: RwLockEndpointPtr| u.endpoint_map[e]),
        held_endpoints: Map::new(threads, |t: RwLockThreadPtr| Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int|
            match u.thread_map[t].endpoint_descriptors[i] { Some(e) => Some(u.endpoint_map[e]), None => None })),
        cpus: Seq::new(NUM_CPUS as nat, |i: int| if in_domain(u, root, u.cpu_array[i].owning_container) { Some(u.cpu_array[i]) } else { None }),
        kernel_l4_end: u.kernel_l4_end,
    }
}

/// The cpu `cpu_id` belongs to the domain rooted at `root`, so its steps are steps of that domain.
pub open spec fn steps_in_domain(u: KernelU, cpu_id: CpuId, root: RwLockContainerPtr) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& in_domain(u, root, u.cpu_array[cpu_id as int].owning_container)
}
} // verus!

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

/// Processes of the domain map memory only through 4K and 2M page-table entries and 4K IOMMU-table entries. No syscall
/// creates 1G mappings or 2M IOMMU mappings, so `memory_iso` over those entries covers all memory the domain maps.
pub open spec fn domain_no_1g(u: KernelU, root: RwLockContainerPtr) -> bool {
    forall|p: RwLockProcessPtr| #![trigger u.process_map[p]] u.process_map.dom().contains(p) && in_domain(u, root, u.process_map[p].owning_container) ==> {
        &&& u.process_map[p].pagetable is Some ==> u.process_map[p].pagetable->Some_0.mapping_1g.dom().is_empty()
        &&& u.process_map[p].iommu_table is Some ==> u.process_map[p].iommu_table->Some_0.mapping_2m.dom().is_empty()
        &&& u.process_map[p].iommu_table is Some ==> u.process_map[p].iommu_table->Some_0.mapping_1g.dom().is_empty()
    }
}

/// The 2M frame starting at `base` contains the address `addr`.
#[verifier::opaque]
pub open spec fn in_2m_frame(base: usize, addr: usize) -> bool { base <= addr < base + 0x200000 }

/// The physical frames the processes of the domain rooted at `root` map, keyed by process and virtual address: the
/// addresses of their 4K and 2M page-table entries and of their 4K IOMMU-table entries. It reads only `process_map` and
/// the subtree of `root`.
#[verifier::ext_equal]
pub ghost struct MemoryView {
    pub pt_4k: IMap<(RwLockProcessPtr, VAddr), usize>,
    pub pt_2m: IMap<(RwLockProcessPtr, VAddr), usize>,
    pub iommu_4k: IMap<(RwLockProcessPtr, VAddr), usize>,
}

pub open spec fn memory_view(u: KernelU, root: RwLockContainerPtr) -> MemoryView {
    let procs = u.process_map;
    let subtree = u.container_map[root].subtree_set;
    MemoryView {
        pt_4k: IMap::new(|k: (RwLockProcessPtr, VAddr)| procs.dom().contains(k.0) && (procs[k.0].owning_container == root || subtree.contains(procs[k.0].owning_container))
            && procs[k.0].pagetable is Some && procs[k.0].pagetable->Some_0.mapping_4k.dom().contains(k.1), |k: (RwLockProcessPtr, VAddr)| procs[k.0].pagetable->Some_0.mapping_4k[k.1].addr),
        pt_2m: IMap::new(|k: (RwLockProcessPtr, VAddr)| procs.dom().contains(k.0) && (procs[k.0].owning_container == root || subtree.contains(procs[k.0].owning_container))
            && procs[k.0].pagetable is Some && procs[k.0].pagetable->Some_0.mapping_2m.dom().contains(k.1), |k: (RwLockProcessPtr, VAddr)| procs[k.0].pagetable->Some_0.mapping_2m[k.1].addr),
        iommu_4k: IMap::new(|k: (RwLockProcessPtr, VAddr)| procs.dom().contains(k.0) && (procs[k.0].owning_container == root || subtree.contains(procs[k.0].owning_container))
            && procs[k.0].iommu_table is Some && procs[k.0].iommu_table->Some_0.mapping_4k.dom().contains(k.1), |k: (RwLockProcessPtr, VAddr)| procs[k.0].iommu_table->Some_0.mapping_4k[k.1].addr),
    }
}

/// No physical page is mapped, through a 4K or 2M page-table entry or a 4K IOMMU-table entry, both by a process of `a`
/// and by a process of `b`. A 2M entry maps the 2M frame starting at its address (`in_2m_frame`).
pub open spec fn memory_iso(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr) -> bool {
    let va = memory_view(u, a);
    let vb = memory_view(u, b);
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.pt_4k[x], vb.pt_4k[y]]
        va.pt_4k.dom().contains(x) && vb.pt_4k.dom().contains(y) ==> va.pt_4k[x] != vb.pt_4k[y]
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.pt_4k[x], vb.iommu_4k[y]]
        va.pt_4k.dom().contains(x) && vb.iommu_4k.dom().contains(y) ==> va.pt_4k[x] != vb.iommu_4k[y]
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.iommu_4k[x], vb.pt_4k[y]]
        va.iommu_4k.dom().contains(x) && vb.pt_4k.dom().contains(y) ==> va.iommu_4k[x] != vb.pt_4k[y]
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.iommu_4k[x], vb.iommu_4k[y]]
        va.iommu_4k.dom().contains(x) && vb.iommu_4k.dom().contains(y) ==> va.iommu_4k[x] != vb.iommu_4k[y]
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.pt_2m[x], vb.pt_2m[y]]
        va.pt_2m.dom().contains(x) && vb.pt_2m.dom().contains(y) ==> va.pt_2m[x] != vb.pt_2m[y]
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.pt_2m[x], vb.pt_4k[y]]
        va.pt_2m.dom().contains(x) && vb.pt_4k.dom().contains(y) ==> !in_2m_frame(va.pt_2m[x], vb.pt_4k[y])
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.pt_4k[x], vb.pt_2m[y]]
        va.pt_4k.dom().contains(x) && vb.pt_2m.dom().contains(y) ==> !in_2m_frame(vb.pt_2m[y], va.pt_4k[x])
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.pt_2m[x], vb.iommu_4k[y]]
        va.pt_2m.dom().contains(x) && vb.iommu_4k.dom().contains(y) ==> !in_2m_frame(va.pt_2m[x], vb.iommu_4k[y])
    &&& forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger va.iommu_4k[x], vb.pt_2m[y]]
        va.iommu_4k.dom().contains(x) && vb.pt_2m.dom().contains(y) ==> !in_2m_frame(vb.pt_2m[y], va.iommu_4k[x])
}

/// A step that leaves the memory views of `a` and `b` unchanged preserves `memory_iso`.
pub proof fn memory_view_unchanged_implies_memory_iso_preserved(old_u: KernelU, new_u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires memory_view(new_u, a) == memory_view(old_u, a), memory_view(new_u, b) == memory_view(old_u, b), memory_iso(old_u, a, b),
    ensures memory_iso(new_u, a, b),
{}

/// A step that keeps every process and its owner, the subtree of `root`, and the page-table and IOMMU-table 4K and 2M
/// mappings of every process of `root` leaves the memory view of `root` unchanged.
pub proof fn process_mappings_unchanged_implies_memory_view_unchanged(old_u: KernelU, new_u: KernelU, root: RwLockContainerPtr)
    requires
        new_u.process_map.dom() =~= old_u.process_map.dom(),
        new_u.container_map[root].subtree_set =~= old_u.container_map[root].subtree_set,
        forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] old_u.process_map.dom().contains(p) ==> {
            &&& new_u.process_map[p].owning_container == old_u.process_map[p].owning_container
            &&& in_domain(old_u, root, old_u.process_map[p].owning_container) ==> {
                &&& (new_u.process_map[p].pagetable is Some) == (old_u.process_map[p].pagetable is Some)
                &&& new_u.process_map[p].pagetable->Some_0.mapping_4k == old_u.process_map[p].pagetable->Some_0.mapping_4k
                &&& new_u.process_map[p].pagetable->Some_0.mapping_2m == old_u.process_map[p].pagetable->Some_0.mapping_2m
                &&& (new_u.process_map[p].iommu_table is Some) == (old_u.process_map[p].iommu_table is Some)
                &&& new_u.process_map[p].iommu_table->Some_0.mapping_4k == old_u.process_map[p].iommu_table->Some_0.mapping_4k
            }
        },
    ensures memory_view(new_u, root) == memory_view(old_u, root),
{}

/// A step after which every entry of the memory view of `b` is an entry it had before, and every entry of the memory
/// view of `a` is an entry it had before or maps a frame that no entry of the old view of `b` shares or covers,
/// preserves `memory_iso`.
pub proof fn memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u: KernelU, new_u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        memory_iso(old_u, a, b),
        forall|y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, b).pt_4k.dom().contains(y)]
            memory_view(new_u, b).pt_4k.dom().contains(y) ==> memory_view(old_u, b).pt_4k.dom().contains(y) && memory_view(old_u, b).pt_4k[y] == memory_view(new_u, b).pt_4k[y],
        forall|y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, b).iommu_4k.dom().contains(y)]
            memory_view(new_u, b).iommu_4k.dom().contains(y) ==> memory_view(old_u, b).iommu_4k.dom().contains(y) && memory_view(old_u, b).iommu_4k[y] == memory_view(new_u, b).iommu_4k[y],
        forall|y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, b).pt_2m.dom().contains(y)]
            memory_view(new_u, b).pt_2m.dom().contains(y) ==> memory_view(old_u, b).pt_2m.dom().contains(y) && memory_view(old_u, b).pt_2m[y] == memory_view(new_u, b).pt_2m[y],
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).pt_4k[x], memory_view(old_u, b).pt_4k[y]]
            memory_view(new_u, a).pt_4k.dom().contains(x) && !(memory_view(old_u, a).pt_4k.dom().contains(x) && memory_view(old_u, a).pt_4k[x] == memory_view(new_u, a).pt_4k[x]) && memory_view(old_u, b).pt_4k.dom().contains(y)
                ==> memory_view(new_u, a).pt_4k[x] != memory_view(old_u, b).pt_4k[y],
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).pt_4k[x], memory_view(old_u, b).iommu_4k[y]]
            memory_view(new_u, a).pt_4k.dom().contains(x) && !(memory_view(old_u, a).pt_4k.dom().contains(x) && memory_view(old_u, a).pt_4k[x] == memory_view(new_u, a).pt_4k[x]) && memory_view(old_u, b).iommu_4k.dom().contains(y)
                ==> memory_view(new_u, a).pt_4k[x] != memory_view(old_u, b).iommu_4k[y],
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).pt_4k[x], memory_view(old_u, b).pt_2m[y]]
            memory_view(new_u, a).pt_4k.dom().contains(x) && !(memory_view(old_u, a).pt_4k.dom().contains(x) && memory_view(old_u, a).pt_4k[x] == memory_view(new_u, a).pt_4k[x]) && memory_view(old_u, b).pt_2m.dom().contains(y)
                ==> !in_2m_frame(memory_view(old_u, b).pt_2m[y], memory_view(new_u, a).pt_4k[x]),
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).iommu_4k[x], memory_view(old_u, b).pt_4k[y]]
            memory_view(new_u, a).iommu_4k.dom().contains(x) && !(memory_view(old_u, a).iommu_4k.dom().contains(x) && memory_view(old_u, a).iommu_4k[x] == memory_view(new_u, a).iommu_4k[x]) && memory_view(old_u, b).pt_4k.dom().contains(y)
                ==> memory_view(new_u, a).iommu_4k[x] != memory_view(old_u, b).pt_4k[y],
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).iommu_4k[x], memory_view(old_u, b).iommu_4k[y]]
            memory_view(new_u, a).iommu_4k.dom().contains(x) && !(memory_view(old_u, a).iommu_4k.dom().contains(x) && memory_view(old_u, a).iommu_4k[x] == memory_view(new_u, a).iommu_4k[x]) && memory_view(old_u, b).iommu_4k.dom().contains(y)
                ==> memory_view(new_u, a).iommu_4k[x] != memory_view(old_u, b).iommu_4k[y],
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).iommu_4k[x], memory_view(old_u, b).pt_2m[y]]
            memory_view(new_u, a).iommu_4k.dom().contains(x) && !(memory_view(old_u, a).iommu_4k.dom().contains(x) && memory_view(old_u, a).iommu_4k[x] == memory_view(new_u, a).iommu_4k[x]) && memory_view(old_u, b).pt_2m.dom().contains(y)
                ==> !in_2m_frame(memory_view(old_u, b).pt_2m[y], memory_view(new_u, a).iommu_4k[x]),
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).pt_2m[x], memory_view(old_u, b).pt_2m[y]]
            memory_view(new_u, a).pt_2m.dom().contains(x) && !(memory_view(old_u, a).pt_2m.dom().contains(x) && memory_view(old_u, a).pt_2m[x] == memory_view(new_u, a).pt_2m[x]) && memory_view(old_u, b).pt_2m.dom().contains(y)
                ==> memory_view(new_u, a).pt_2m[x] != memory_view(old_u, b).pt_2m[y],
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).pt_2m[x], memory_view(old_u, b).pt_4k[y]]
            memory_view(new_u, a).pt_2m.dom().contains(x) && !(memory_view(old_u, a).pt_2m.dom().contains(x) && memory_view(old_u, a).pt_2m[x] == memory_view(new_u, a).pt_2m[x]) && memory_view(old_u, b).pt_4k.dom().contains(y)
                ==> !in_2m_frame(memory_view(new_u, a).pt_2m[x], memory_view(old_u, b).pt_4k[y]),
        forall|x: (RwLockProcessPtr, VAddr), y: (RwLockProcessPtr, VAddr)| #![trigger memory_view(new_u, a).pt_2m[x], memory_view(old_u, b).iommu_4k[y]]
            memory_view(new_u, a).pt_2m.dom().contains(x) && !(memory_view(old_u, a).pt_2m.dom().contains(x) && memory_view(old_u, a).pt_2m[x] == memory_view(new_u, a).pt_2m[x]) && memory_view(old_u, b).iommu_4k.dom().contains(y)
                ==> !in_2m_frame(memory_view(new_u, a).pt_2m[x], memory_view(old_u, b).iommu_4k[y]),
    ensures memory_iso(new_u, a, b),
{}

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

/// Every thread in IPC transit whose live partner is a thread of `x` lies outside `y`.
pub open spec fn inflight_iso(u: KernelU, x: RwLockContainerPtr, y: RwLockContainerPtr) -> bool {
    forall|d: RwLockThreadPtr| #![trigger u.thread_map[d].state] u.thread_map.dom().contains(d) && u.thread_map[d].state is IPC_TRANSIT ==> {
        let partner = u.thread_map[d].state->IPC_TRANSIT_partner;
        u.thread_map.dom().contains(partner) && in_domain(u, x, u.thread_map[partner].owning_container) ==> !in_domain(u, y, u.thread_map[d].owning_container)
    }
}

/// Isolation between the container subtrees rooted at `a` and `b`.
pub open spec fn isolated(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr) -> bool {
    &&& domains_disjoint(u, a, b)
    &&& domain_no_1g(u, a)
    &&& domain_no_1g(u, b)
    &&& memory_iso(u, a, b)
    &&& endpoint_iso(u, a, b)
    &&& inflight_iso(u, a, b)
    &&& inflight_iso(u, b, a)
}
} // verus!

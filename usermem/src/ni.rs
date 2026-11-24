//! Noninterference over user memory: the memory view of a domain, the premises of one step, the byte-level isolation
//! lemmas, and the one-step, third-domain, trace, pairwise, and load theorems.
use vstd::prelude::*;
use crate::*;
use crate::invariant::*;
use crate::drain::*;
use veriflat_noninterference::*;
use veriflat_noninterference::ni_env::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_mmap_2m::syscall_mmap_2m::syscall_mmap_2m_spec::*;
use veriflat_syscall_mmap_1g::syscall_mmap_1g::syscall_mmap_1g_spec::*;

verus! {
/// The 4K, 2M, or 1G mappings of `t`.
pub open spec fn table_of_size(t: PageTableU, size: PageSize) -> Map<VAddr, MapEntry> {
    match size {
        PageSize::SZ4k => t.mapping_4k,
        PageSize::SZ2m => t.mapping_2m,
        PageSize::SZ1g => t.mapping_1g,
    }
}

/// The physical byte `a` lies in a frame that a process of the domain rooted at `root` maps through a 4K, 2M, or 1G
/// page-table leaf or a 4K IOMMU-table leaf (`memory_view`).
pub open spec fn domain_maps_byte(u: KernelU, root: RwLockContainerPtr, a: PAddr) -> bool {
    let v = memory_view(u, root);
    ||| exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_4k[k]] v.pt_4k.dom().contains(k) && v.pt_4k[k] <= a < v.pt_4k[k] + 0x1000
    ||| exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_2m[k]] v.pt_2m.dom().contains(k) && v.pt_2m[k] <= a < v.pt_2m[k] + 0x200000
    ||| exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_1g[k]] v.pt_1g.dom().contains(k) && v.pt_1g[k] <= a < v.pt_1g[k] + 0x40000000
    ||| exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.iommu_4k[k]] v.iommu_4k.dom().contains(k) && v.iommu_4k[k] <= a < v.iommu_4k[k] + 0x1000
}

/// What the domain rooted at `root` observes of the memory machine: its `domain_view`, the store buffer of each of its cpus,
/// and every physical byte it maps. TLBs are not in the view.
#[verifier::ext_equal]
pub ghost struct MemDomainView { pub base: DomainView, pub bufs: Seq<Option<Seq<PendingStore>>>, pub bytes: IMap<PAddr, u8> }

pub open spec fn mem_domain_view(st: MemState, root: RwLockContainerPtr) -> MemDomainView {
    MemDomainView {
        base: domain_view(st.u, root),
        bufs: Seq::new(NUM_CPUS as nat, |i: int| if in_domain(st.u, root, st.u.cpu_array[i].owning_container) { Some(st.bufs[i]) } else { None }),
        bytes: IMap::new(|a: PAddr| domain_maps_byte(st.u, root, a), |a: PAddr| st.mem[a]),
    }
}

/// The anchor B/D/F of `did` is owned by a live process of the domain rooted at `root`.
pub open spec fn did_in_domain(u: KernelU, did: VtdDomainId, root: RwLockContainerPtr) -> bool {
    let anchor = pci_bdf_of_did(did);
    let q = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int];
    q is Some && u.process_map.dom().contains(q->Some_0) && in_domain(u, root, u.process_map[q->Some_0].owning_container)
}

/// A translation of the current key of a cpu of `x`, at a VA where that cpu's current process has no leaf of that size, and a
/// 4K IOTLB translation of a DID of `x`, at an IOVA where the IOMMU table of the DID's anchor owner has no leaf, name no byte
/// that `y` maps. These are the hidden leaves of an unmap, kill, or exit not yet flushed.
pub open spec fn hidden_translations_outside(u: KernelU, x: RwLockContainerPtr, y: RwLockContainerPtr) -> bool {
    &&& forall|c: CpuId, size: PageSize, va: VAddr, a: PAddr|
        #![trigger tlb_of_size(u.cpu_tlb[(c, u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid)], size)[va], domain_maps_byte(u, y, a)]
        index_valid(NUM_CPUS, c) && in_domain(u, x, u.cpu_array[c as int].owning_container) && u.cpu_array[c as int].current_process is Some && ({
            let p = u.process_map[u.cpu_array[c as int].current_process->Some_0];
            let tlb = tlb_of_size(u.cpu_tlb[(c, p.pcid)], size);
            &&& tlb.dom().contains(va)
            &&& !(p.pagetable is Some && table_of_size(p.pagetable->Some_0, size).dom().contains(va))
            &&& tlb[va].addr <= a < tlb[va].addr + page_size_bytes(size)
        }) ==> !domain_maps_byte(u, y, a)
    &&& forall|did: VtdDomainId, iova: VAddr, a: PAddr| #![trigger u.iommu_tlb[did].tlb_4k[iova], domain_maps_byte(u, y, a)]
        u.iommu_tlb.dom().contains(did) && did_in_domain(u, did, x) && u.iommu_tlb[did].tlb_4k.dom().contains(iova) && ({
            let anchor = pci_bdf_of_did(did);
            let q = u.process_map[u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int]->Some_0];
            &&& !(q.iommu_table is Some && q.iommu_table->Some_0.mapping_4k.dom().contains(iova))
            &&& u.iommu_tlb[did].tlb_4k[iova].addr <= a < u.iommu_tlb[did].tlb_4k[iova].addr + 0x1000
        }) ==> !domain_maps_byte(u, y, a)
}

/// Every cpu other than `d` that the kernel step `l` of `d` drains, and that holds stores, is a cpu of `x`; proved for every
/// kernel label (`kernel_step_implies_remote_cpu_views_within_domain`, `remote_cpu_views_within_domain_implies_drains_within_domain`).
pub open spec fn drains_within_domain(old: MemState, new_u: KernelU, l: StepLabel, d: CpuId, x: RwLockContainerPtr) -> bool {
    forall|c: CpuId| #![trigger old.bufs[c as int]] index_valid(NUM_CPUS, c) && c != d && drained(l, old.u, new_u, d, c) && old.bufs[c as int].len() > 0
        ==> in_domain(old.u, x, old.u.cpu_array[c as int].owning_container)
}

/// The step `label` of cpu `c` from `st` is a step of the domain rooted at `root`: a fill of any domain, a device write of a
/// DID of `root`, or any other step of a cpu of `root`.
pub open spec fn mem_step_in_domain(label: MemLabel, st: MemState, c: CpuId, root: RwLockContainerPtr) -> bool {
    match label {
        MemLabel::Kernel { label: l } => l is CpuTlbFilled || l is IommuTlbFilled || l is IommuContextCacheFilled || steps_in_domain(st.u, c, root),
        MemLabel::DmaWritten { did, .. } => did_in_domain(st.u, did, root),
        _ => steps_in_domain(st.u, c, root),
    }
}

/// The honest-peer conditions of `trace_ni_at` for the step `l` of cpu `c` of `x` toward `y`: an endpoint received from a
/// peer outside `x` is neither held nor waited on by `y`, and a page shared from a source outside `x` is mapped and covered by
/// no leaf of `y`.
pub open spec fn ni_honest_peer(u: KernelU, l: StepLabel, c: CpuId, x: RwLockContainerPtr, y: RwLockContainerPtr) -> bool {
    let progress = u.thread_map[u.cpu_array[c as int].current_thread->Some_0].syscall_progress->Some_0;
    let peer = progress->IpcEndpoint_peer;
    let payload = u.thread_map[peer].endpoint_descriptors[u.thread_map[peer].ipc_payload->Endpoint_endpoint_index as int]->Some_0;
    let source = u.thread_map[share_4k_objects(u, c).source_thread].owning_proc;
    &&& l is IpcEndpointFinish && !progress->IpcEndpoint_caller_sends && !in_domain(u, x, u.thread_map[peer].owning_container) ==> {
        &&& forall|t: RwLockThreadPtr, j: EndpointIdx| #![trigger u.endpoint_map[payload].owning_threads.contains((t, j))]
            u.endpoint_map[payload].owning_threads.contains((t, j)) ==> !in_domain(u, y, u.thread_map[t].owning_container)
        &&& forall|j: int| #![trigger u.endpoint_map[payload].queue[j]]
            0 <= j < u.endpoint_map[payload].queue.len() ==> !in_domain(u, y, u.thread_map[u.endpoint_map[payload].queue[j]].owning_container)
    }
    &&& l is Share4kLeaf && !in_domain(u, x, u.process_map[source].owning_container) ==> {
        let shared = u.process_map[source].pagetable->Some_0.mapping_4k[progress->Share4k_source_range.view()[progress->Share4k_shared as int]].addr;
        &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
            u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> u.process_map[q].pagetable->Some_0.mapping_4k[v].addr != shared
        &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
            u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].iommu_table is Some && u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v)
                ==> u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr != shared
        &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_2m[v]]
            u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some && u.process_map[q].pagetable->Some_0.mapping_2m.dom().contains(v)
                ==> !(u.process_map[q].pagetable->Some_0.mapping_2m[v].addr <= shared < u.process_map[q].pagetable->Some_0.mapping_2m[v].addr + 0x200000)
        &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_1g[v]]
            u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some && u.process_map[q].pagetable->Some_0.mapping_1g.dom().contains(v)
                ==> !(u.process_map[q].pagetable->Some_0.mapping_1g[v].addr <= shared < u.process_map[q].pagetable->Some_0.mapping_1g[v].addr + 0x4000_0000)
    }
}

/// The premises of one step of cpu `c` of `x` from `old` to `new` with label `label`, toward `y`.
#[verifier::opaque]
pub open spec fn mem_ni_step(old: MemState, new: MemState, label: MemLabel, c: CpuId, x: RwLockContainerPtr, y: RwLockContainerPtr) -> bool {
    &&& kernel_u_ownership_wf(old.u) && kernel_u_ownership_wf(new.u)
    &&& kernel_u_current_tlb_matches_present_wf(old.u) && kernel_u_iotlb_matches_present_wf(old.u)
    &&& store_buffers_covered(old)
    &&& mem_step(old, new, label, c) && mem_step_in_domain(label, old, c, x)
    &&& hidden_translations_outside(old.u, x, y)
    &&& label matches MemLabel::Kernel { label: l } ==> ni_honest_peer(old.u, l, c, x, y)
}

/// No container lies in two isolated domains.
pub proof fn isolated_container_in_both_implies_false(u: KernelU, x: RwLockContainerPtr, y: RwLockContainerPtr, c: RwLockContainerPtr)
    requires isolated(u, x, y), in_domain(u, x, c), in_domain(u, y, c),
    ensures false,
{}

/// Two frames aligned to their sizes, each 4K, 2M, or 1G, the first no larger, that share a byte: the second contains the
/// first's base, and frames of equal size are equal.
pub proof fn aligned_frames_sharing_byte_implies_nested(fx: int, sx: int, fy: int, sy: int, a: int)
    requires
        sx == 0x1000 || sx == 0x200000 || sx == 0x40000000, sy == 0x1000 || sy == 0x200000 || sy == 0x40000000, sx <= sy, fx % sx == 0, fy % sy == 0, fx <= a < fx + sx,
        fy <= a < fy + sy,
    ensures fy <= fx < fy + sy, sx == sy ==> fx == fy,
{
    if sx == 0x1000 && sy == 0x200000 {
        assert(fy <= fx) by (nonlinear_arith) requires fx % 0x1000 == 0, fy % 0x200000 == 0, fx <= a < fx + 0x1000, fy <= a, {
            assert(fy % 0x1000 == 0) by (nonlinear_arith) requires fy % 0x200000 == 0, { assert(fy == 0x200000 * (fy / 0x200000)); assert(fy == 0x1000 * (0x200 * (fy / 0x200000))); };
        };
    } else if sx == 0x1000 && sy == 0x40000000 {
        assert(fy <= fx) by (nonlinear_arith) requires fx % 0x1000 == 0, fy % 0x40000000 == 0, fx <= a < fx + 0x1000, fy <= a, {
            assert(fy % 0x1000 == 0) by (nonlinear_arith) requires fy % 0x40000000 == 0, { assert(fy == 0x40000000 * (fy / 0x40000000)); assert(fy == 0x1000 * (0x40000 * (fy / 0x40000000))); };
        };
    } else if sx == 0x200000 && sy == 0x40000000 {
        assert(fy <= fx) by (nonlinear_arith) requires fx % 0x200000 == 0, fy % 0x40000000 == 0, fx <= a < fx + 0x200000, fy <= a, {
            assert(fy % 0x200000 == 0) by (nonlinear_arith) requires fy % 0x40000000 == 0, { assert(fy == 0x40000000 * (fy / 0x40000000)); assert(fy == 0x200000 * (0x200 * (fy / 0x40000000))); };
        };
    } else {
        assert(fx == fy) by (nonlinear_arith) requires fx % sx == 0, fy % sx == 0, sx > 0, fx <= a < fx + sx, fy <= a < fy + sx, {
            assert(fx == sx * (fx / sx)); assert(fy == sx * (fy / sx));
        };
    }
}

/// Entry `k` of the 4K page-table (`kind` 0), 4K IOMMU-table (1), 2M (2), or 1G (3) map of `v`: whether `v` holds it, its frame,
/// and the size of its frame.
pub open spec fn view_leaf(v: MemoryView, kind: int, k: (RwLockProcessPtr, VAddr)) -> (bool, int, int) {
    if kind == 0 { (v.pt_4k.dom().contains(k), v.pt_4k[k] as int, 0x1000) }
    else if kind == 1 { (v.iommu_4k.dom().contains(k), v.iommu_4k[k] as int, 0x1000) }
    else if kind == 2 { (v.pt_2m.dom().contains(k), v.pt_2m[k] as int, 0x200000) }
    else { (v.pt_1g.dom().contains(k), v.pt_1g[k] as int, 0x40000000) }
}

/// An entry of the memory view of `root` names an address aligned to its frame's size.
pub proof fn leaf_addr_aligned_wf_implies_view_leaf_aligned(u: KernelU, root: RwLockContainerPtr, kind: int, k: (RwLockProcessPtr, VAddr))
    requires kernel_u_leaf_addr_aligned_wf(u), 0 <= kind < 4, view_leaf(memory_view(u, root), kind, k).0,
    ensures view_leaf(memory_view(u, root), kind, k).1 % view_leaf(memory_view(u, root), kind, k).2 == 0,
{
    reveal(kernel_u_leaf_addr_aligned_wf);
    let v = memory_view(u, root);
    if kind == 0 { assert(v.pt_4k[k] == u.process_map[k.0].pagetable->Some_0.mapping_4k[k.1].addr); }
    else if kind == 1 { assert(v.iommu_4k[k] == u.process_map[k.0].iommu_table->Some_0.mapping_4k[k.1].addr); }
    else if kind == 2 { assert(v.pt_2m[k] == u.process_map[k.0].pagetable->Some_0.mapping_2m[k.1].addr); }
    else { assert(v.pt_1g[k] == u.process_map[k.0].pagetable->Some_0.mapping_1g[k.1].addr); }
}

/// A byte the domain rooted at `root` maps lies in the frame of some entry of its memory view, aligned to its size.
pub proof fn domain_maps_byte_implies_aligned_view_leaf(u: KernelU, root: RwLockContainerPtr, a: PAddr) -> (r: (int, (RwLockProcessPtr, VAddr)))
    requires domain_maps_byte(u, root, a), kernel_u_leaf_addr_aligned_wf(u),
    ensures
        ({
            let e = view_leaf(memory_view(u, root), r.0, r.1);
            &&& 0 <= r.0 < 4 && e.0 && e.1 <= a < e.1 + e.2 && e.1 % e.2 == 0
            &&& e.2 == 0x1000 || e.2 == 0x200000 || e.2 == 0x40000000
        }),
{
    let v = memory_view(u, root);
    let r = if exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_4k[k]] v.pt_4k.dom().contains(k) && v.pt_4k[k] <= a < v.pt_4k[k] + 0x1000 {
        let k = choose|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_4k[k]] v.pt_4k.dom().contains(k) && v.pt_4k[k] <= a < v.pt_4k[k] + 0x1000;
        (0, k)
    } else if exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.iommu_4k[k]] v.iommu_4k.dom().contains(k) && v.iommu_4k[k] <= a < v.iommu_4k[k] + 0x1000 {
        let k = choose|k: (RwLockProcessPtr, VAddr)| #![trigger v.iommu_4k[k]] v.iommu_4k.dom().contains(k) && v.iommu_4k[k] <= a < v.iommu_4k[k] + 0x1000;
        (1, k)
    } else if exists|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_2m[k]] v.pt_2m.dom().contains(k) && v.pt_2m[k] <= a < v.pt_2m[k] + 0x200000 {
        let k = choose|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_2m[k]] v.pt_2m.dom().contains(k) && v.pt_2m[k] <= a < v.pt_2m[k] + 0x200000;
        (2, k)
    } else {
        let k = choose|k: (RwLockProcessPtr, VAddr)| #![trigger v.pt_1g[k]] v.pt_1g.dom().contains(k) && v.pt_1g[k] <= a < v.pt_1g[k] + 0x40000000;
        (3, k)
    };
    leaf_addr_aligned_wf_implies_view_leaf_aligned(u, root, r.0, r.1);
    r
}

/// With leaves aligned to their sizes, `memory_iso` between `x` and `y` leaves no byte that both map.
pub proof fn memory_iso_implies_no_shared_byte(u: KernelU, x: RwLockContainerPtr, y: RwLockContainerPtr, a: PAddr)
    requires memory_iso(u, x, y), kernel_u_leaf_addr_aligned_wf(u), domain_maps_byte(u, x, a),
    ensures !domain_maps_byte(u, y, a),
{
    if domain_maps_byte(u, y, a) {
        reveal(in_2m_frame); reveal(in_1g_frame);
        let rx = domain_maps_byte_implies_aligned_view_leaf(u, x, a);
        let ry = domain_maps_byte_implies_aligned_view_leaf(u, y, a);
        let ex = view_leaf(memory_view(u, x), rx.0, rx.1);
        let ey = view_leaf(memory_view(u, y), ry.0, ry.1);
        if ex.2 <= ey.2 { aligned_frames_sharing_byte_implies_nested(ex.1, ex.2, ey.1, ey.2, a as int); } else { aligned_frames_sharing_byte_implies_nested(ey.1, ey.2, ex.1, ex.2, a as int); }
    }
}

/// Equal domain views of `root` give equal memory views.
pub proof fn domain_view_eq_implies_memory_view_eq(u: KernelU, u2: KernelU, root: RwLockContainerPtr)
    requires domain_view(u2, root) == domain_view(u, root), u.container_map.dom().contains(root),
    ensures memory_view(u2, root) == memory_view(u, root),
{
    assert(domain_view(u, root).containers.dom().contains(root) && domain_view(u2, root).containers.dom().contains(root));
    assert(domain_view(u2, root).containers[root] == u2.container_map[root] && domain_view(u, root).containers[root] == u.container_map[root]);
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map.dom().contains(p) && in_domain(u2, root, u2.process_map[p].owning_container)
        implies u.process_map.dom().contains(p) && u.process_map[p] == u2.process_map[p] by {
        assert(domain_view(u2, root).processes.dom().contains(p));
        assert(domain_view(u2, root).processes[p] == u2.process_map[p] && domain_view(u, root).processes[p] == u.process_map[p]);
    };
    assert forall|p: RwLockProcessPtr| #![trigger u.process_map[p]] u.process_map.dom().contains(p) && in_domain(u, root, u.process_map[p].owning_container)
        implies u2.process_map.dom().contains(p) && u2.process_map[p] == u.process_map[p] by { assert(domain_view(u, root).processes.dom().contains(p)); };
    assert(memory_view(u2, root) =~~= memory_view(u, root));
}

/// The byte view of `mem_domain_view` holds exactly the bytes the domain maps, with their values in memory.
pub proof fn mem_domain_view_implies_bytes_of_mapped_memory(st: MemState, root: RwLockContainerPtr, a: PAddr)
    ensures mem_domain_view(st, root).bytes.dom().contains(a) == domain_maps_byte(st.u, root, a), domain_maps_byte(st.u, root, a) ==> mem_domain_view(st, root).bytes[a] == st.mem[a],
{ assert(ISet::new(|a: PAddr| domain_maps_byte(st.u, root, a)).contains(a) == domain_maps_byte(st.u, root, a)); }

/// Two states whose memory views of `y` agree on which bytes `y` maps, and whose memories agree on those bytes, have equal byte
/// views of `y`.
pub proof fn mapped_bytes_kept_implies_bytes_view_eq(st: MemState, st2: MemState, y: RwLockContainerPtr)
    requires
        memory_view(st2.u, y) == memory_view(st.u, y),
        forall|a: PAddr| #![trigger st2.mem[a]] domain_maps_byte(st.u, y, a) ==> st2.mem[a] == st.mem[a],
    ensures mem_domain_view(st2, y).bytes =~= mem_domain_view(st, y).bytes,
{
    assert forall|a: PAddr| #![trigger mem_domain_view(st2, y).bytes.dom().contains(a)] mem_domain_view(st2, y).bytes.dom().contains(a) == mem_domain_view(st, y).bytes.dom().contains(a) by {
        mem_domain_view_implies_bytes_of_mapped_memory(st, y, a); mem_domain_view_implies_bytes_of_mapped_memory(st2, y, a);
    };
    assert forall|a: PAddr| #![trigger mem_domain_view(st2, y).bytes[a]] mem_domain_view(st2, y).bytes.dom().contains(a) implies mem_domain_view(st2, y).bytes[a] == mem_domain_view(st, y).bytes[a] by {
        mem_domain_view_implies_bytes_of_mapped_memory(st, y, a); mem_domain_view_implies_bytes_of_mapped_memory(st2, y, a); assert(st2.mem[a] == st.mem[a]);
    };
    assert(mem_domain_view(st2, y).bytes.dom() =~= mem_domain_view(st, y).bytes.dom());
}

/// A store covered on a cpu of `x` writes no byte that `y` maps: through a leaf its cpu's current process has at the
/// store's VA the frame is one `x` maps, which `memory_iso` keeps apart from `y`; through a hidden leaf premise 1 applies.
pub proof fn store_covered_in_domain_implies_bytes_outside(u: KernelU, c: CpuId, s: PendingStore, x: RwLockContainerPtr, y: RwLockContainerPtr, a: PAddr)
    requires
        kernel_u_ownership_wf(u), kernel_u_current_tlb_matches_present_wf(u), isolated(u, x, y), hidden_translations_outside(u, x, y), index_valid(NUM_CPUS, c),
        in_domain(u, x, u.cpu_array[c as int].owning_container), store_covered(u, c, s), store_covers(s, a),
    ensures !domain_maps_byte(u, y, a),
{
    reveal(kernel_u_cpu_ownership_wf);
    let p = u.cpu_array[c as int].current_process->Some_0;
    let table = u.process_map[p].pagetable->Some_0;
    let tlb = tlb_of_size(u.cpu_tlb[(c, s.pcid)], s.size);
    let e = tlb[s.base_va];
    assert(u.cpu_array[c as int].owning_container == u.cpu_array[c as int].owning_container);
    assert(e.addr <= a < e.addr + page_size_bytes(s.size));
    if table_of_size(table, s.size).dom().contains(s.base_va) {
        reveal(kernel_u_current_tlb_matches_present_wf);
        assert(u.cpu_array[c as int].current_process == u.cpu_array[c as int].current_process);
        kernel_u_io_leaf_wf_implies_leaf_addr_aligned_wf(u);
        let v = memory_view(u, x);
        match s.size {
            PageSize::SZ4k => { assert(u.cpu_tlb[(c, s.pcid)].tlb_4k[s.base_va] == e); assert(v.pt_4k[(p, s.base_va)] == e.addr); },
            PageSize::SZ2m => { assert(u.cpu_tlb[(c, s.pcid)].tlb_2m[s.base_va] == e); assert(v.pt_2m[(p, s.base_va)] == e.addr); },
            PageSize::SZ1g => { assert(u.cpu_tlb[(c, s.pcid)].tlb_1g[s.base_va] == e); assert(v.pt_1g[(p, s.base_va)] == e.addr); },
        }
        assert(domain_maps_byte(u, x, a));
        memory_iso_implies_no_shared_byte(u, x, y, a);
    } else { assert(tlb_of_size(u.cpu_tlb[(c, u.process_map[p].pcid)], s.size)[s.base_va] == e); }
}

/// A device write of a DID of `x` writes no byte that `y` maps: through a leaf of the anchor owner's IOMMU table the frame
/// is one `x` maps; through a hidden IOMMU leaf premise 1 applies.
pub proof fn dma_in_domain_implies_bytes_outside(u: KernelU, did: VtdDomainId, iova: VAddr, frame: PAddr, offset: nat, bytes: Seq<u8>, x: RwLockContainerPtr,
    y: RwLockContainerPtr, a: PAddr)
    requires
        kernel_u_ownership_wf(u), kernel_u_iotlb_matches_present_wf(u), isolated(u, x, y), hidden_translations_outside(u, x, y), dma_pre(u, did, iova, frame, offset, bytes),
        did_in_domain(u, did, x), frame + offset <= a < frame + offset + bytes.len(),
    ensures !domain_maps_byte(u, y, a),
{
    let anchor = pci_bdf_of_did(did);
    let q = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int]->Some_0;
    let t = u.process_map[q].iommu_table;
    assert(u.iommu_tlb[did].tlb_4k.dom().contains(iova) && u.iommu_tlb[did].tlb_4k[iova].addr == frame);
    if t is Some && t->Some_0.mapping_4k.dom().contains(iova) {
        reveal(kernel_u_iotlb_matches_present_wf);
        kernel_u_io_leaf_wf_implies_leaf_addr_aligned_wf(u);
        assert(memory_view(u, x).iommu_4k[(q, iova)] == frame);
        assert(domain_maps_byte(u, x, a));
        memory_iso_implies_no_shared_byte(u, x, y, a);
    }
}

/// The frame an mmap leaf step of a cpu of `x` installs holds no byte that `y` maps after the step, when `x` and `y` are
/// isolated after it: the new leaf is a leaf of `x`.
pub proof fn mmap_leaf_step_implies_zeroed_bytes_outside(old_u: KernelU, new_u: KernelU, l: StepLabel, d: CpuId, x: RwLockContainerPtr, y: RwLockContainerPtr, a: PAddr)
    requires
        labeled_step(l, old_u, new_u, d), kernel_u_ownership_wf(old_u), kernel_u_ownership_wf(new_u), steps_in_domain(old_u, d, x), isolated(new_u, x, y),
        mmap_leaf_frame(l, old_u, new_u, d) is Some, mmap_leaf_frame(l, old_u, new_u, d)->Some_0.0 <= a < mmap_leaf_frame(l, old_u, new_u, d)->Some_0.0 + mmap_leaf_frame(l, old_u, new_u, d)->Some_0.1,
    ensures !domain_maps_byte(new_u, y, a),
{
    reveal(kernel_u_cpu_ownership_wf);
    let thread = old_u.thread_map[old_u.cpu_array[d as int].current_thread->Some_0];
    let progress = thread.syscall_progress->Some_0;
    let p = thread.owning_proc;
    let v = memory_view(new_u, x);
    let frame = mmap_leaf_frame(l, old_u, new_u, d)->Some_0.0;
    kernel_u_io_leaf_wf_implies_leaf_addr_aligned_wf(new_u);
    match l {
        StepLabel::Mmap4kLeaf => {
            reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step);
            assert(v.pt_4k[(p, progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int])] == frame);
        },
        StepLabel::Mmap2mLeaf => {
            reveal(mmap_2m_leaf_step_pre); reveal(mmap_2m_leaf_step);
            assert(v.pt_2m[(p, progress->Mmap2m_range.view()[progress->Mmap2m_mapped as int])] == frame);
        },
        StepLabel::Mmap1gLeaf => {
            reveal(mmap_1g_leaf_step_pre); reveal(mmap_1g_leaf_step);
            assert(v.pt_1g[(p, progress->Mmap1g_range.view()[progress->Mmap1g_mapped as int])] == frame);
        },
        _ => {},
    }
    assert(domain_maps_byte(new_u, x, a));
    memory_iso_implies_no_shared_byte(new_u, x, y, a);
}

/// A kernel step of cpu `d` keeps the memory view of `y` and the isolation of `x` and `y`.
pub proof fn kernel_mem_step_implies_view_kept_and_isolated(old: MemState, new: MemState, l: StepLabel, d: CpuId, x: RwLockContainerPtr, y: RwLockContainerPtr)
    requires isolated(old.u, x, y), mem_ni_step(old, new, MemLabel::Kernel { label: l }, d, x, y),
    ensures isolated(new.u, x, y), mem_domain_view(new, y) =~~= mem_domain_view(old, y),
{
    reveal(mem_ni_step);
    let label = MemLabel::Kernel { label: l };
    let fill = l is CpuTlbFilled || l is IommuTlbFilled || l is IommuContextCacheFilled;
    match l {
        StepLabel::CpuTlbFilled { cpu_id: fc, pcid, added } => { cpu_tlb_filled_step_lr(old.u, new.u, fc, pcid, added, y); cpu_tlb_filled_step_iso(old.u, new.u, fc, pcid, added, x, y); },
        StepLabel::IommuTlbFilled { did, added } => { iommu_tlb_filled_step_lr(old.u, new.u, did, added, y); iommu_tlb_filled_step_iso(old.u, new.u, did, added, x, y); },
        StepLabel::IommuContextCacheFilled => { iommu_context_cache_filled_step_lr(old.u, new.u, y); iommu_context_cache_filled_step_iso(old.u, new.u, x, y); },
        _ => { trace_ni_at(seq![old.u, new.u], seq![l], seq![d], seq![x], x, y, 0, 1); },
    }
    assert(domain_view(new.u, y) =~~= domain_view(old.u, y));
    if !hardware_label(l) {
        kernel_step_implies_remote_cpu_views_within_domain(l, old.u, new.u, d, x);
        remote_cpu_views_within_domain_implies_drains_within_domain(old, new.u, l, d, x);
    }
    let (vn, vo) = (mem_domain_view(new, y), mem_domain_view(old, y));
    assert forall|i: int| #![trigger vn.bufs[i]] 0 <= i < NUM_CPUS implies vn.bufs[i] == vo.bufs[i] by {
        assert(domain_view(new.u, y).cpus[i] == domain_view(old.u, y).cpus[i]);
        let c = i as CpuId;
        if in_domain(old.u, y, old.u.cpu_array[i].owning_container) && drained(l, old.u, new.u, d, c) {
            if old.bufs[i].len() > 0 {
                if c == d { isolated_container_in_both_implies_false(old.u, x, y, old.u.cpu_array[i].owning_container); }
                else { assert(old.bufs[c as int].len() > 0); isolated_container_in_both_implies_false(old.u, x, y, old.u.cpu_array[i].owning_container); }
            }
            assert(old.bufs[i] =~= Seq::<PendingStore>::empty());
        }
    };
    assert(vn.bufs =~= vo.bufs);
    domain_view_eq_implies_memory_view_eq(old.u, new.u, y);
    assert forall|a: PAddr| #![trigger new.mem[a]] domain_maps_byte(old.u, y, a) implies new.mem[a] == old.mem[a] by {
        if new.mem[a] != old.mem[a] {
            mem_step_implies_byte_change_explained(old, new, label, d, a);
            if leaf_zeroed_byte(old, new, l, d, a) { mmap_leaf_step_implies_zeroed_bytes_outside(old.u, new.u, l, d, x, y, a); } else {
                let (w, j) = choose|w: CpuId, j: int| #![trigger old.bufs[w as int][j], drained(l, old.u, new.u, d, w)]
                    index_valid(NUM_CPUS, w) && drained(l, old.u, new.u, d, w) && 0 <= j < old.bufs[w as int].len() && store_covers(old.bufs[w as int][j], a)
                    && store_covered(old.u, w, old.bufs[w as int][j]);
                if w != d { assert(old.bufs[w as int].len() > 0); }
                store_covered_in_domain_implies_bytes_outside(old.u, w, old.bufs[w as int][j], x, y, a);
            }
        }
    };
    mapped_bytes_kept_implies_bytes_view_eq(old, new, y);
}

/// A user or device step keeps the memory view of `y`, and changes no kernel state.
pub proof fn user_mem_step_implies_view_kept(old: MemState, new: MemState, label: MemLabel, c: CpuId, x: RwLockContainerPtr, y: RwLockContainerPtr)
    requires isolated(old.u, x, y), mem_ni_step(old, new, label, c, x, y), !(label is Kernel),
    ensures new.u == old.u, mem_domain_view(new, y) =~~= mem_domain_view(old, y),
{
    reveal(mem_ni_step);
    let (vn, vo) = (mem_domain_view(new, y), mem_domain_view(old, y));
    assert forall|i: int| #![trigger vn.bufs[i]] 0 <= i < NUM_CPUS implies vn.bufs[i] == vo.bufs[i] by {
        if i == c as int && in_domain(old.u, y, old.u.cpu_array[i].owning_container) && !(label is DmaWritten) && !(label is Load) {
            isolated_container_in_both_implies_false(old.u, x, y, old.u.cpu_array[i].owning_container);
        }
    };
    assert(vn.bufs =~= vo.bufs);
    assert forall|a: PAddr| #![trigger new.mem[a]] domain_maps_byte(old.u, y, a) implies new.mem[a] == old.mem[a] by {
        if new.mem[a] != old.mem[a] {
            mem_step_implies_byte_change_explained(old, new, label, c, a);
            match label {
                MemLabel::StoreCommitted => { store_covered_in_domain_implies_bytes_outside(old.u, c, old.bufs[c as int][0], x, y, a); },
                MemLabel::DmaWritten { did, iova, frame, offset, bytes } => { dma_in_domain_implies_bytes_outside(old.u, did, iova, frame, offset, bytes, x, y, a); },
                _ => {},
            }
        }
    };
    mapped_bytes_kept_implies_bytes_view_eq(old, new, y);
}

/// One step of `x` toward `y` keeps `x` and `y` isolated and leaves the memory view of `y` unchanged.
pub proof fn mem_step_implies_view_kept_and_isolated(old: MemState, new: MemState, label: MemLabel, c: CpuId, x: RwLockContainerPtr, y: RwLockContainerPtr)
    requires isolated(old.u, x, y), mem_ni_step(old, new, label, c, x, y),
    ensures isolated(new.u, x, y), mem_domain_view(new, y) =~~= mem_domain_view(old, y),
{
    match label {
        MemLabel::Kernel { label: l } => { kernel_mem_step_implies_view_kept_and_isolated(old, new, l, c, x, y); },
        _ => { user_mem_step_implies_view_kept(old, new, label, c, x, y); },
    }
}

/// A step of a third domain `z`, isolated from `a` and `b`, keeps the three isolations and the memory views of `a` and `b`.
pub proof fn third_domain_mem_step_implies_views_kept_and_isolated(old: MemState, new: MemState, label: MemLabel, c: CpuId, z: RwLockContainerPtr, a: RwLockContainerPtr,
    b: RwLockContainerPtr)
    requires isolated(old.u, z, a), isolated(old.u, z, b), isolated(old.u, a, b), mem_ni_step(old, new, label, c, z, a), mem_ni_step(old, new, label, c, z, b),
    ensures
        isolated(new.u, a, b), isolated(new.u, z, a), isolated(new.u, z, b), mem_domain_view(new, a) =~~= mem_domain_view(old, a),
        mem_domain_view(new, b) =~~= mem_domain_view(old, b),
{
    reveal(mem_ni_step);
    mem_step_implies_view_kept_and_isolated(old, new, label, c, z, a);
    mem_step_implies_view_kept_and_isolated(old, new, label, c, z, b);
    domain_views_unchanged_implies_isolated_preserved(old.u, new.u, a, b);
}

/// Unwinding over a trace of the memory machine. `sts[i + 1]` follows `sts[i]` by the step `labels[i]` of cpu `cpus[i]` of
/// domain `steppers[i]`, which is `a` or `b`, under the premises of `mem_ni_step` toward the other domain. Then `sts[n]` is
/// isolated, and steps of `a` from `sts[m]` to `sts[n]` leave the memory view of `b` unchanged.
pub proof fn mem_trace_ni_at(sts: Seq<MemState>, labels: Seq<MemLabel>, cpus: Seq<CpuId>, steppers: Seq<RwLockContainerPtr>, a: RwLockContainerPtr, b: RwLockContainerPtr,
    m: int, n: int)
    requires
        sts.len() == labels.len() + 1, cpus.len() == labels.len(), steppers.len() == labels.len(), 0 <= n < sts.len(), isolated(sts[0].u, a, b), store_buffers_covered(sts[0]),
        forall|i: int| #![trigger steppers[i]] 0 <= i < labels.len() ==> {
            let x = steppers[i];
            let y = if x == a { b } else { a };
            &&& x == a || x == b
            &&& mem_ni_step(sts[i], sts[i + 1], labels[i], cpus[i], x, y)
        },
    ensures
        isolated(sts[n].u, a, b),
        0 <= m <= n && (forall|i: int| #![trigger steppers[i]] m <= i < n ==> steppers[i] == a) ==> mem_domain_view(sts[n], b) =~~= mem_domain_view(sts[m], b),
    decreases n,
{
    if n > 0 {
        let i = n - 1;
        let x = steppers[i];
        let y = if x == a { b } else { a };
        mem_trace_ni_at(sts, labels, cpus, steppers, a, b, m, i);
        assert(mem_ni_step(sts[i], sts[n], labels[i], cpus[i], x, y));
        if x != a { isolated_symmetric(sts[i].u, a, b); }
        mem_step_implies_view_kept_and_isolated(sts[i], sts[n], labels[i], cpus[i], x, y);
        if x != a { isolated_symmetric(sts[n].u, b, a); }
    }
}

/// Unwinding over a trace of any set `domains` of pairwise isolated domains. `sts[i + 1]` follows `sts[i]` by the step
/// `labels[i]` of cpu `cpus[i]` of domain `steppers[i]` in `domains`, under the premises of `mem_ni_step` toward every other
/// domain of the set. Then the domains stay pairwise isolated in `sts[n]`, and steps of domains other than `b` from `sts[m]`
/// to `sts[n]` leave the memory view of `b` unchanged.
pub proof fn pairwise_isolated_domains_mem_trace_implies_isolated_and_view_unchanged(sts: Seq<MemState>, labels: Seq<MemLabel>, cpus: Seq<CpuId>,
    steppers: Seq<RwLockContainerPtr>, domains: Set<RwLockContainerPtr>, b: RwLockContainerPtr, m: int, n: int)
    requires
        sts.len() == labels.len() + 1, cpus.len() == labels.len(), steppers.len() == labels.len(), 0 <= n < sts.len(), domains.contains(b),
        forall|x: RwLockContainerPtr, y: RwLockContainerPtr| #![trigger isolated(sts[0].u, x, y)] domains.contains(x) && domains.contains(y) && x != y ==> isolated(sts[0].u, x, y),
        forall|i: int| #![trigger steppers[i]] 0 <= i < labels.len() ==> {
            &&& domains.contains(steppers[i])
            &&& forall|y: RwLockContainerPtr| #![trigger domains.contains(y)] domains.contains(y) && y != steppers[i] ==> mem_ni_step(sts[i], sts[i + 1], labels[i], cpus[i], steppers[i], y)
        },
    ensures
        forall|x: RwLockContainerPtr, y: RwLockContainerPtr| #![trigger isolated(sts[n].u, x, y)] domains.contains(x) && domains.contains(y) && x != y ==> isolated(sts[n].u, x, y),
        0 <= m <= n && (forall|i: int| #![trigger steppers[i]] m <= i < n ==> steppers[i] != b) ==> mem_domain_view(sts[n], b) =~~= mem_domain_view(sts[m], b),
    decreases n,
{
    if n > 0 {
        let i = n - 1;
        let (old, new, x) = (sts[i], sts[n], steppers[i]);
        pairwise_isolated_domains_mem_trace_implies_isolated_and_view_unchanged(sts, labels, cpus, steppers, domains, b, m, i);
        assert(domains.contains(x));
        assert forall|y: RwLockContainerPtr, z: RwLockContainerPtr| #![trigger isolated(new.u, y, z)] domains.contains(y) && domains.contains(z) && y != z implies isolated(new.u, y, z) by {
            if y == x {
                assert(mem_ni_step(old, new, labels[i], cpus[i], x, z));
                mem_step_implies_view_kept_and_isolated(old, new, labels[i], cpus[i], x, z);
            } else if z == x {
                assert(mem_ni_step(old, new, labels[i], cpus[i], x, y));
                assert(isolated(old.u, x, y));
                mem_step_implies_view_kept_and_isolated(old, new, labels[i], cpus[i], x, y); isolated_symmetric(new.u, x, y);
            } else {
                assert(mem_ni_step(old, new, labels[i], cpus[i], x, y) && mem_ni_step(old, new, labels[i], cpus[i], x, z));
                assert(isolated(old.u, x, y) && isolated(old.u, x, z) && isolated(old.u, y, z));
                third_domain_mem_step_implies_views_kept_and_isolated(old, new, labels[i], cpus[i], x, y, z);
            }
        };
        if m < n && x != b {
            assert(mem_ni_step(old, new, labels[i], cpus[i], x, b));
            assert(isolated(old.u, x, b));
            mem_step_implies_view_kept_and_isolated(old, new, labels[i], cpus[i], x, b);
        }
    }
}

/// Two states with equal memory views of `root`, in which a cpu of `root` loads through a translation of a leaf its current
/// process has at `va`, load the same frame and see the same bytes. Loads through hidden translations are not covered.
pub proof fn equal_mem_views_implies_equal_load_value(st1: MemState, st2: MemState, root: RwLockContainerPtr, c: CpuId, size: PageSize, f1: PAddr, f2: PAddr, va: VAddr,
    offset: nat, len: nat)
    requires
        kernel_u_ownership_wf(st1.u), kernel_u_ownership_wf(st2.u), kernel_u_current_tlb_matches_present_wf(st1.u), kernel_u_current_tlb_matches_present_wf(st2.u),
        mem_domain_view(st1, root) == mem_domain_view(st2, root), steps_in_domain(st1.u, c, root), load_pre(st1.u, c, size, f1, va, offset, len),
        load_pre(st2.u, c, size, f2, va, offset, len),
        ({
            let p = st1.u.process_map[st1.u.cpu_array[c as int].current_process->Some_0];
            p.pcid != KERNEL_DEFAULT_PCID && table_of_size(p.pagetable->Some_0, size).dom().contains(va)
        }),
    ensures
        f1 == f2,
        forall|i: int| #![trigger st1.mem[(f1 + offset + i) as PAddr]] 0 <= i < len ==> forwarded_byte(st1.bufs[c as int], (f1 + offset + i) as PAddr, st1.mem[(f1 + offset + i) as PAddr])
            == forwarded_byte(st2.bufs[c as int], (f2 + offset + i) as PAddr, st2.mem[(f2 + offset + i) as PAddr]),
{
    reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_current_tlb_matches_present_wf);
    let (v1, v2) = (mem_domain_view(st1, root), mem_domain_view(st2, root));
    let pp = st1.u.cpu_array[c as int].current_process->Some_0;
    assert(v1.base.cpus[c as int] == v2.base.cpus[c as int]);
    assert(st2.u.cpu_array[c as int] == st1.u.cpu_array[c as int]);
    assert(v1.base.processes.dom().contains(pp));
    assert(v1.base.processes[pp] == v2.base.processes[pp]);
    let p = st1.u.process_map[pp];
    assert(st2.u.process_map[pp] == p);
    let entry = table_of_size(p.pagetable->Some_0, size)[va];
    assert(st1.u.cpu_array[c as int].current_process == st1.u.cpu_array[c as int].current_process);
    assert(st2.u.cpu_array[c as int].current_process == st2.u.cpu_array[c as int].current_process);
    let mv = memory_view(st1.u, root);
    kernel_u_io_leaf_wf_implies_leaf_addr_aligned_wf(st1.u);
    match size {
        PageSize::SZ4k => { assert(f1 == entry.addr && f2 == entry.addr); assert(mv.pt_4k[(pp, va)] == f1); leaf_addr_aligned_wf_implies_view_leaf_aligned(st1.u, root, 0, (pp, va)); },
        PageSize::SZ2m => { assert(f1 == entry.addr && f2 == entry.addr); assert(mv.pt_2m[(pp, va)] == f1); leaf_addr_aligned_wf_implies_view_leaf_aligned(st1.u, root, 2, (pp, va)); },
        PageSize::SZ1g => { assert(f1 == entry.addr && f2 == entry.addr); assert(mv.pt_1g[(pp, va)] == f1); leaf_addr_aligned_wf_implies_view_leaf_aligned(st1.u, root, 3, (pp, va)); },
    }
    assert(f1 + page_size_bytes(size) <= 0x1_0000_0000_0000_0000);
    assert(v1.bufs[c as int] == v2.bufs[c as int]);
    assert forall|i: int| #![trigger st1.mem[(f1 + offset + i) as PAddr]] 0 <= i < len implies forwarded_byte(st1.bufs[c as int], (f1 + offset + i) as PAddr, st1.mem[(f1 + offset + i) as PAddr])
        == forwarded_byte(st2.bufs[c as int], (f2 + offset + i) as PAddr, st2.mem[(f2 + offset + i) as PAddr]) by {
        let a = (f1 + offset + i) as PAddr;
        assert(domain_maps_byte(st1.u, root, a));
        mem_domain_view_implies_bytes_of_mapped_memory(st1, root, a); mem_domain_view_implies_bytes_of_mapped_memory(st2, root, a);
    };
}
} // verus!

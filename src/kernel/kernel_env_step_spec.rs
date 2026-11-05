use vstd::prelude::*;
use crate::*;

verus! {
// Hardware environment events: a CPU or a remapping unit caches what its walker may read at any time, also inside a
// kernel section. A walker reads only present leaves of the table it runs, so each event adds only such translations.

/// `pre` with the entries of `added` cached on top; an entry `added` names wins.
pub open spec fn single_tlb_union(pre: SingleTLB, added: SingleTLB) -> SingleTLB {
    SingleTLB { tlb_4k: pre.tlb_4k.union_prefer_right(added.tlb_4k), tlb_2m: pre.tlb_2m.union_prefer_right(added.tlb_2m), tlb_1g: pre.tlb_1g.union_prefer_right(added.tlb_1g) }
}

/// What CPU `cpu_id` may cache under `pcid` in state `k`: present leaves and present non-leaf entries of the table it runs
/// when `pcid` is its current PCID, nothing for another non-default PCID. The model does not track the default PCID.
pub open spec fn cpu_tlb_within_may_cache(k: KernelK, cpu_id: CpuId, pcid: Pcid, tlb: SingleTLB, cache: PagingStructureCache) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    if pcid == KERNEL_DEFAULT_PCID {
        true
    } else if cpu.current_pcid == pcid && cpu.current_pagetable is Some {
        let table = whole_pagetable(k.pt_mp, k.pt_lower.view(), cpu.current_pagetable->Some_0);
        single_cpu_single_pcid_tlb_subset_of_present_pagetable(tlb, table) && single_structure_cache_subset_of_present_pagetable(cache, table)
    } else {
        tlb.is_empty() && cache.is_empty()
    }
}

/// What the IOTLB may cache for domain `did` in state `k`: present leaves of the IOMMU table attached at the DID's
/// anchor B/D/F when the anchor carries `did`, nothing otherwise.
pub open spec fn iommu_tlb_within_may_cache(k: KernelK, did: VtdDomainId, tlb: SingleTLB) -> bool {
    let anchor = pci_bdf_of_did(did);
    let root_table = k.irt.view();
    if root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) {
        let iommu_table = k.it_mp.spec_index(k.prc_mp.spec_index(root_table.spec_index_owner(anchor.0, anchor.1, anchor.2)).view().iommu_table->Some_0);
        single_tlb_subset_of_present_pagetable(tlb, iommu_table.view())
    } else {
        tlb.is_empty()
    }
}

/// The context entry of `bdf` is present with exactly root `entry.0` and domain `entry.1`.
pub open spec fn iommu_context_cache_entry_present(k: KernelK, bdf: PciBdf, entry: (PageTableRoot, VtdDomainId)) -> bool {
    &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
    &&& k.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(entry.0)
    &&& k.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == Some(entry.1)
}

/// Every cached translation names a leaf of the user view `table`, which shows only present leaves.
pub open spec fn single_tlb_subset_of_pagetable_u(tlb: SingleTLB, table: PageTableU) -> bool {
    &&& forall|va: VAddr| #![trigger tlb.tlb_4k().dom().contains(va)] tlb.tlb_4k().dom().contains(va)
        ==> table.mapping_4k.dom().contains(va) && spec_tlb_entry_equal_to_map_entry(tlb.tlb_4k().spec_index(va), table.mapping_4k.spec_index(va))
    &&& forall|va: VAddr| #![trigger tlb.tlb_2m().dom().contains(va)] tlb.tlb_2m().dom().contains(va)
        ==> table.mapping_2m.dom().contains(va) && spec_tlb_entry_equal_to_map_entry(tlb.tlb_2m().spec_index(va), table.mapping_2m.spec_index(va))
    &&& forall|va: VAddr| #![trigger tlb.tlb_1g().dom().contains(va)] tlb.tlb_1g().dom().contains(va)
        ==> table.mapping_1g.dom().contains(va) && spec_tlb_entry_equal_to_map_entry(tlb.tlb_1g().spec_index(va), table.mapping_1g.spec_index(va))
}

/// U form of `cpu_tlb_within_may_cache`: the user view of the table of the process CPU `cpu_id` runs when `pcid` is
/// that process's PCID, nothing for another non-default PCID.
pub open spec fn cpu_tlb_within_may_cache_u(u: KernelU, cpu_id: CpuId, pcid: Pcid, tlb: SingleTLB) -> bool {
    let process = u.cpu_array[cpu_id as int].current_process;
    if pcid == KERNEL_DEFAULT_PCID {
        true
    } else if process is Some && u.process_map.dom().contains(process->Some_0) && u.process_map[process->Some_0].pcid == pcid && u.process_map[process->Some_0].pagetable is Some {
        single_tlb_subset_of_pagetable_u(tlb, u.process_map[process->Some_0].pagetable->Some_0)
    } else {
        tlb.is_empty()
    }
}

/// `entry` is the translation of the present 4K leaf at `va` of `table`: one entry of
/// `single_cpu_single_pcid_tlb_subset_of_present_pagetable`.
pub open spec fn tlb_4k_entry_present_in_pagetable(entry: TLBEntry, table: WholePageTable<PT_TYPE>, va: VAddr) -> bool {
    let held = table.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
    let leaf = table.spec_resolve_mapping_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
    &&& va_4k_valid(va)
    &&& table.kernel_l4_end() <= spec_v2l4index(va)
    &&& held is Some
    &&& spec_tlb_entry_equal_to_page_entry(entry, held->0)
    &&& leaf is Some
    &&& leaf->0.perm.present
}

/// `entry` is the translation of the present 2M leaf at `va` of `table`: one entry of
/// `single_cpu_single_pcid_tlb_subset_of_present_pagetable`.
pub open spec fn tlb_2m_entry_present_in_pagetable(entry: TLBEntry, table: WholePageTable<PT_TYPE>, va: VAddr) -> bool {
    let held = table.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    let leaf = table.spec_resolve_mapping_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    &&& va_2m_valid(va)
    &&& table.kernel_l4_end() <= spec_v2l4index(va)
    &&& held is Some
    &&& spec_tlb_entry_equal_to_page_entry(entry, held->0)
    &&& leaf is Some
    &&& leaf->0.perm.present
}

/// `entry` is the translation of the present 1G leaf at `va` of `table`: one entry of
/// `single_cpu_single_pcid_tlb_subset_of_present_pagetable`.
pub open spec fn tlb_1g_entry_present_in_pagetable(entry: TLBEntry, table: WholePageTable<PT_TYPE>, va: VAddr) -> bool {
    &&& table.mapping_1g().dom().contains(va)
    &&& spec_tlb_entry_equal_to_map_entry(entry, table.mapping_1g().spec_index(va))
    &&& table.mapping_1g().spec_index(va).present
}

/// Every translation `tlb` caches is one `old_tlb` caches alike that a per-address flush of `count` pages from `va` does
/// not drop, or a present leaf of `table`: the TLB of one `(cpu, pcid)` right after such a flush while it runs `table`.
pub open spec fn single_tlb_va_range_flushed_kept_or_present(old_tlb: SingleTLB, tlb: SingleTLB, table: WholePageTable<PT_TYPE>, va: VAddr, count: usize, stride_2m: bool) -> bool {
    &&& forall|x: VAddr| #![trigger tlb.tlb_4k().dom().contains(x)] #![trigger tlb.tlb_4k().spec_index(x)] tlb.tlb_4k().dom().contains(x)
        ==> (!va_range_flush_drops_4k(va, count, stride_2m, x) && old_tlb.tlb_4k().contains_pair(x, tlb.tlb_4k().spec_index(x))) || tlb_4k_entry_present_in_pagetable(tlb.tlb_4k().spec_index(x), table, x)
    &&& forall|x: VAddr| #![trigger tlb.tlb_2m().dom().contains(x)] #![trigger tlb.tlb_2m().spec_index(x)] tlb.tlb_2m().dom().contains(x)
        ==> (!va_range_flush_drops_2m(va, count, stride_2m, x) && old_tlb.tlb_2m().contains_pair(x, tlb.tlb_2m().spec_index(x))) || tlb_2m_entry_present_in_pagetable(tlb.tlb_2m().spec_index(x), table, x)
    &&& forall|x: VAddr| #![trigger tlb.tlb_1g().dom().contains(x)] #![trigger tlb.tlb_1g().spec_index(x)] tlb.tlb_1g().dom().contains(x)
        ==> (!va_range_flush_drops_1g(va, count, stride_2m, x) && old_tlb.tlb_1g().contains_pair(x, tlb.tlb_1g().spec_index(x))) || tlb_1g_entry_present_in_pagetable(tlb.tlb_1g().spec_index(x), table, x)
}

/// What CPU `cpu_id` may hold under `pcid` in state `k` right after a per-address flush of `count` pages from `va` that
/// found `old_tlb`: the translations of `old_tlb` the flush does not drop, plus present leaves and present directory
/// entries of the table it runs when `pcid` is its current PCID. The flush drops every directory entry of `pcid`.
pub open spec fn cpu_tlb_va_range_flushed(k: KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, old_tlb: SingleTLB, tlb: SingleTLB, cache: PagingStructureCache) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    if cpu.current_pcid == pcid && cpu.current_pagetable is Some {
        let table = whole_pagetable(k.pt_mp, k.pt_lower.view(), cpu.current_pagetable->Some_0);
        single_tlb_va_range_flushed_kept_or_present(old_tlb, tlb, table, va, count, stride_2m) && single_structure_cache_subset_of_present_pagetable(cache, table)
    } else {
        single_tlb_va_range_flushed_kept(old_tlb, tlb, va, count, stride_2m) && cache.is_empty()
    }
}

/// U form of `single_tlb_va_range_flushed_kept_or_present`: a translation the flush keeps, or a leaf of the user view `table`.
pub open spec fn single_tlb_va_range_flushed_kept_or_present_u(old_tlb: SingleTLB, tlb: SingleTLB, table: PageTableU, va: VAddr, count: usize, stride_2m: bool) -> bool {
    &&& forall|x: VAddr| #![trigger tlb.tlb_4k().dom().contains(x)] #![trigger tlb.tlb_4k().spec_index(x)] tlb.tlb_4k().dom().contains(x)
        ==> (!va_range_flush_drops_4k(va, count, stride_2m, x) && old_tlb.tlb_4k().contains_pair(x, tlb.tlb_4k().spec_index(x)))
            || (table.mapping_4k.dom().contains(x) && spec_tlb_entry_equal_to_map_entry(tlb.tlb_4k().spec_index(x), table.mapping_4k.spec_index(x)))
    &&& forall|x: VAddr| #![trigger tlb.tlb_2m().dom().contains(x)] #![trigger tlb.tlb_2m().spec_index(x)] tlb.tlb_2m().dom().contains(x)
        ==> (!va_range_flush_drops_2m(va, count, stride_2m, x) && old_tlb.tlb_2m().contains_pair(x, tlb.tlb_2m().spec_index(x)))
            || (table.mapping_2m.dom().contains(x) && spec_tlb_entry_equal_to_map_entry(tlb.tlb_2m().spec_index(x), table.mapping_2m.spec_index(x)))
    &&& forall|x: VAddr| #![trigger tlb.tlb_1g().dom().contains(x)] #![trigger tlb.tlb_1g().spec_index(x)] tlb.tlb_1g().dom().contains(x)
        ==> (!va_range_flush_drops_1g(va, count, stride_2m, x) && old_tlb.tlb_1g().contains_pair(x, tlb.tlb_1g().spec_index(x)))
            || (table.mapping_1g.dom().contains(x) && spec_tlb_entry_equal_to_map_entry(tlb.tlb_1g().spec_index(x), table.mapping_1g.spec_index(x)))
}

/// U form of `cpu_tlb_va_range_flushed`: the translations of `old_tlb` the flush keeps, plus leaves of the user view of the
/// table of the process CPU `cpu_id` runs when `pcid` is that process's PCID.
pub open spec fn cpu_tlb_va_range_flushed_u(u: KernelU, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, old_tlb: SingleTLB, tlb: SingleTLB) -> bool {
    let process = u.cpu_array[cpu_id as int].current_process;
    if process is Some && u.process_map.dom().contains(process->Some_0) && u.process_map[process->Some_0].pcid == pcid && u.process_map[process->Some_0].pagetable is Some {
        single_tlb_va_range_flushed_kept_or_present_u(old_tlb, tlb, u.process_map[process->Some_0].pagetable->Some_0, va, count, stride_2m)
    } else {
        single_tlb_va_range_flushed_kept(old_tlb, tlb, va, count, stride_2m)
    }
}

/// U form of `iommu_tlb_within_may_cache`: the user view of the IOMMU table of the owner of the DID's anchor B/D/F when
/// the anchor is attached and that table carries `did`, nothing otherwise.
pub open spec fn iommu_tlb_within_may_cache_u(u: KernelU, did: VtdDomainId, tlb: SingleTLB) -> bool {
    let anchor = pci_bdf_of_did(did);
    let owner = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int];
    if u.iommu_root_table.attached[anchor.0 as int][anchor.1 as int][anchor.2 as int] && u.process_map.dom().contains(owner) && u.process_map[owner].iommu_table is Some
        && u.process_map[owner].iommu_table->Some_0.did == Some(did) {
        single_tlb_subset_of_pagetable_u(tlb, u.process_map[owner].iommu_table->Some_0)
    } else {
        tlb.is_empty()
    }
}

/// CPU `cpu_id` caches translations `added` and paging-structure entries `added_cache` under `pcid`; nothing else changes.
pub open spec fn kernel_k_cpu_tlb_filled(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, added: SingleTLB, added_cache: PagingStructureCache) -> bool {
    let cache = pre.cpu_tlb.structure_cache((cpu_id, pcid));
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pcid_valid(pcid)
    &&& cpu_tlb_within_may_cache(pre, cpu_id, pcid, added, added_cache)
    &&& post == (KernelK { cpu_tlb: post.cpu_tlb, ..pre })
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), single_tlb_union(pre.cpu_tlb.spec_index((cpu_id, pcid)), added))
    &&& post.cpu_tlb.structure_caches.view() == pre.cpu_tlb.structure_caches.view().insert((cpu_id, pcid), PagingStructureCache {
        pml4e: cache.pml4e.union_prefer_right(added_cache.pml4e), pdpte: cache.pdpte.union_prefer_right(added_cache.pdpte), pde: cache.pde.union_prefer_right(added_cache.pde) })
    &&& forall|c: CpuId, p: Pcid|
        #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))] #![trigger post.cpu_tlb.structure_cache((c, p))] #![trigger pre.cpu_tlb.structure_cache((c, p))]
        (c, p) != (cpu_id, pcid) ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p)) && post.cpu_tlb.structure_cache((c, p)) == pre.cpu_tlb.structure_cache((c, p))
}

/// The IOTLB caches `added` for domain `did`; nothing else changes.
pub open spec fn kernel_k_iommu_tlb_filled(pre: KernelK, post: KernelK, did: VtdDomainId, added: SingleTLB) -> bool {
    &&& vtd_domain_id_valid(did)
    &&& iommu_tlb_within_may_cache(pre, did, added)
    &&& post == (KernelK { iommu_tlb: post.iommu_tlb, ..pre })
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, single_tlb_union(pre.iommu_tlb.spec_index(did), added))
    &&& forall|x: VtdDomainId| #![trigger post.iommu_tlb.spec_index(x)] #![trigger pre.iommu_tlb.spec_index(x)] x != did ==> post.iommu_tlb.spec_index(x) == pre.iommu_tlb.spec_index(x)
    &&& post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache()
}

/// The context cache caches the present context entry of `bdf`; nothing else changes.
pub open spec fn kernel_k_iommu_context_cache_filled(pre: KernelK, post: KernelK, bdf: PciBdf, entry: (PageTableRoot, VtdDomainId)) -> bool {
    &&& iommu_context_cache_entry_present(pre, bdf, entry)
    &&& post == (KernelK { iommu_tlb: post.iommu_tlb, ..pre })
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& forall|x: VtdDomainId| #![trigger post.iommu_tlb.spec_index(x)] #![trigger pre.iommu_tlb.spec_index(x)] post.iommu_tlb.spec_index(x) == pre.iommu_tlb.spec_index(x)
    &&& post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache().insert(bdf, entry)
}

/// Cpu `cpu_id` leaves user mode for its trap path at `syscall` or an interrupt gate; nothing else changes.
pub open spec fn kernel_k_trap_enter(pre: KernelK, post: KernelK, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_op.view().view()[cpu_id as int] is User
    &&& post == (KernelK { cpu_op: post.cpu_op, ..pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Trap)
}

/// Cpu `cpu_id` returns from its trap path to user mode at `sysretq` or `iretq`; nothing else changes.
pub open spec fn kernel_k_trap_return(pre: KernelK, post: KernelK, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_op.view().view()[cpu_id as int] is Trap
    &&& post == (KernelK { cpu_op: post.cpu_op, ..pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::User)
}

/// Cpu `cpu_id`, marked by a killer, leaves its trap path for its idle loop at `restore_frame`; nothing else changes.
pub open spec fn kernel_k_trap_divert(pre: KernelK, post: KernelK, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_op.view().view()[cpu_id as int] is Trap
    &&& pre.cpu_arr.spec_index(cpu_id).view().being_killed()
    &&& post == (KernelK { cpu_op: post.cpu_op, ..pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Idle)
}

/// U step of `kernel_k_cpu_tlb_filled`: CPU `cpu_id` caches `added` under `pcid`.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_tlb_filled_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, pcid: Pcid, added: SingleTLB) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pcid_valid(pcid)
    &&& cpu_tlb_within_may_cache_u(old_u, cpu_id, pcid, added)
    &&& new_u == (KernelU { cpu_tlb: old_u.cpu_tlb.insert((cpu_id, pcid), single_tlb_union(old_u.cpu_tlb[(cpu_id, pcid)], added)), ..old_u })
}

/// U step of `kernel_k_iommu_tlb_filled`: the IOTLB caches `added` for domain `did`.
#[verifier::opaque]
pub open spec fn kernel_u_iommu_tlb_filled_step(old_u: KernelU, new_u: KernelU, did: VtdDomainId, added: SingleTLB) -> bool {
    &&& vtd_domain_id_valid(did)
    &&& iommu_tlb_within_may_cache_u(old_u, did, added)
    &&& new_u == (KernelU { iommu_tlb: old_u.iommu_tlb.insert(did, single_tlb_union(old_u.iommu_tlb[did], added)), ..old_u })
}

/// U step of `kernel_k_iommu_context_cache_filled`: the context cache is not user-visible, so nothing changes.
#[verifier::opaque]
pub open spec fn kernel_u_iommu_context_cache_filled_step(old_u: KernelU, new_u: KernelU) -> bool { new_u == old_u }

pub proof fn kernel_k_cpu_tlb_filled_preserves_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, added: SingleTLB, added_cache: PagingStructureCache)
    requires
        pre.inv(),
        kernel_k_cpu_tlb_filled(pre, post, cpu_id, pcid, added, added_cache),
    ensures post.inv(),
{
    let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
    let filled = single_tlb_union(pre.cpu_tlb.spec_index((cpu_id, pcid)), added);
    let cache = pre.cpu_tlb.structure_cache((cpu_id, pcid));
    if pcid != KERNEL_DEFAULT_PCID && !(cpu.current_pcid == pcid && cpu.current_pagetable is Some) {
        assert(filled.tlb_4k =~= pre.cpu_tlb.spec_index((cpu_id, pcid)).tlb_4k);
        assert(filled.tlb_2m =~= pre.cpu_tlb.spec_index((cpu_id, pcid)).tlb_2m);
        assert(filled.tlb_1g =~= pre.cpu_tlb.spec_index((cpu_id, pcid)).tlb_1g);
        assert(cache.pml4e.union_prefer_right(added_cache.pml4e) =~= cache.pml4e && cache.pdpte.union_prefer_right(added_cache.pdpte) =~= cache.pdpte
            && cache.pde.union_prefer_right(added_cache.pde) =~= cache.pde);
    }
    assert(post.cpu_tlb.inv()) by { reveal(CpuTLB::inv); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
        reveal(cpu_dirty_map_covers_nonempty_tlb); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
        assert(filled.tlb_4k() == pre.cpu_tlb.spec_index((cpu_id, pcid)).tlb_4k().union_prefer_right(added.tlb_4k())
            && filled.tlb_2m() == pre.cpu_tlb.spec_index((cpu_id, pcid)).tlb_2m().union_prefer_right(added.tlb_2m()));
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
}

pub proof fn kernel_k_iommu_tlb_filled_preserves_inv(pre: KernelK, post: KernelK, did: VtdDomainId, added: SingleTLB)
    requires
        pre.inv(),
        kernel_k_iommu_tlb_filled(pre, post, did, added),
    ensures
        post.inv(),
        forall|it: RwLockPageTableRoot| #![trigger iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, it)]
            pre.it_mp.dom().contains(it) && iommu_table_tlb_entries_present(pre.iommu_tlb, pre.irt.view(), pre.it_mp, it) ==> iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, it),
{
    let anchor = pci_bdf_of_did(did);
    let filled = single_tlb_union(pre.iommu_tlb.spec_index(did), added);
    if pre.irt.view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) != Some(did) {
        assert(filled.tlb_4k =~= pre.iommu_tlb.spec_index(did).tlb_4k);
        assert(filled.tlb_2m =~= pre.iommu_tlb.spec_index(did).tlb_2m);
        assert(filled.tlb_1g =~= pre.iommu_tlb.spec_index(did).tlb_1g);
    }
    assert(post.iommu_tlb.inv()) by { reveal(IommuTLB::inv); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(IommuTLB::inv); reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    reveal(iommu_table_tlb_entries_present); reveal(iommu_root_table_process_wf); reveal(process_iommu_table_wf);
}

pub proof fn kernel_k_iommu_context_cache_filled_preserves_inv(pre: KernelK, post: KernelK, bdf: PciBdf, entry: (PageTableRoot, VtdDomainId))
    requires
        pre.inv(),
        kernel_k_iommu_context_cache_filled(pre, post, bdf, entry),
    ensures post.inv(),
{
    assert(post.iommu_tlb.inv()) by { reveal(IommuTLB::inv); reveal(iommu_root_table_process_wf); pre.irt.view().wf_context_entry_at(bdf.0, bdf.1, bdf.2); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(IommuTLB::inv); reveal(iommu_tlb_wf); };
}

pub proof fn kernel_k_trap_enter_preserves_inv(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_enter(pre, post, cpu_id),
    ensures post.inv(),
{
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(cpu_op_wf(post.cpu_op.view().view(), post.cpu_arr)) by { reveal(cpu_op_wf); };
}

pub proof fn kernel_k_trap_return_preserves_inv(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_return(pre, post, cpu_id),
    ensures post.inv(),
{
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(cpu_op_wf(post.cpu_op.view().view(), post.cpu_arr)) by { reveal(cpu_op_wf); };
}

pub proof fn kernel_k_trap_divert_preserves_inv(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_divert(pre, post, cpu_id),
    ensures post.inv(),
{
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(cpu_op_wf(post.cpu_op.view().view(), post.cpu_arr)) by { reveal(cpu_op_wf); };
}

// Each environment event below happens while a thread is between two of its kernel sections. Its `respects_boundary`
// lemma shows that the event stays within the step boundary's trusted framing of that thread, given the thread's local
// context `lctx` aligned with the pre-state; alignment keeps every remote cpu the thread holds outside a kernel step.

/// A trap entry on another cpu stays within the step-boundary framing of a thread between its sections.
pub proof fn kernel_k_trap_enter_respects_boundary(pre: KernelK, post: KernelK, cpu_id: CpuId, lctx: LocalContext)
    requires
        pre.inv(),
        kernel_k_trap_enter(pre, post, cpu_id),
        typed_lock_maps_aligned(&pre, &lctx),
        cpu_id != lctx.cpu_id(),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    assert(post.inv()) by { kernel_k_trap_enter_preserves_inv(pre, post, cpu_id); };
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}

/// A trap return on another cpu stays within the step-boundary framing of a thread between its sections.
pub proof fn kernel_k_trap_return_respects_boundary(pre: KernelK, post: KernelK, cpu_id: CpuId, lctx: LocalContext)
    requires
        pre.inv(),
        kernel_k_trap_return(pre, post, cpu_id),
        typed_lock_maps_aligned(&pre, &lctx),
        cpu_id != lctx.cpu_id(),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    assert(post.inv()) by { kernel_k_trap_return_preserves_inv(pre, post, cpu_id); };
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}

/// A trap diversion of another, marked cpu to its idle loop stays within the step-boundary framing of a thread between
/// its sections.
pub proof fn kernel_k_trap_divert_respects_boundary(pre: KernelK, post: KernelK, cpu_id: CpuId, lctx: LocalContext)
    requires
        pre.inv(),
        kernel_k_trap_divert(pre, post, cpu_id),
        typed_lock_maps_aligned(&pre, &lctx),
        cpu_id != lctx.cpu_id(),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    assert(post.inv()) by { kernel_k_trap_divert_preserves_inv(pre, post, cpu_id); };
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}

/// A CPU TLB fill stays within the step-boundary framing of a thread between its sections.
pub proof fn kernel_k_cpu_tlb_filled_respects_boundary(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, added: SingleTLB, added_cache: PagingStructureCache, lctx: LocalContext)
    requires
        pre.inv(),
        kernel_k_cpu_tlb_filled(pre, post, cpu_id, pcid, added, added_cache),
        typed_lock_maps_aligned(&pre, &lctx),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    assert(post.inv()) by { kernel_k_cpu_tlb_filled_preserves_inv(pre, post, cpu_id, pcid, added, added_cache); };
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}

/// An IOTLB fill stays within the step-boundary framing of a thread between its sections: the domain of a write-held
/// IOMMU table gains only present leaves of that table.
pub proof fn kernel_k_iommu_tlb_filled_respects_boundary(pre: KernelK, post: KernelK, did: VtdDomainId, added: SingleTLB, lctx: LocalContext)
    requires
        pre.inv(),
        kernel_k_iommu_tlb_filled(pre, post, did, added),
        typed_lock_maps_aligned(&pre, &lctx),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    kernel_k_iommu_tlb_filled_preserves_inv(pre, post, did, added);
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}

/// A context-cache fill stays within the step-boundary framing of a thread between its sections.
pub proof fn kernel_k_iommu_context_cache_filled_respects_boundary(pre: KernelK, post: KernelK, bdf: PciBdf, entry: (PageTableRoot, VtdDomainId), lctx: LocalContext)
    requires
        pre.inv(),
        kernel_k_iommu_context_cache_filled(pre, post, bdf, entry),
        typed_lock_maps_aligned(&pre, &lctx),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    assert(post.inv()) by { kernel_k_iommu_context_cache_filled_preserves_inv(pre, post, bdf, entry); };
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
    reveal(iommu_table_tlb_entries_present);
}

/// The running-to-idle IPI of `CpuOpArray::ipi_running_to_idle`, with the writes `CpuLockedArray::ipi_remote_running_to_idle`
/// makes to the target cpu object and hardware cr3/pcid word, stays within the step-boundary framing of a thread between
/// its sections that does not hold the target. The IPI runs inside the sender's section, so the invariant after it is
/// assumed.
pub proof fn cpu_op_ipi_running_to_idle_respects_boundary(pre: KernelK, post: KernelK, cpu_id: CpuId, default_cr3: PageTableRoot, lctx: LocalContext)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        post == (KernelK { cpu_op: post.cpu_op, cpu_arr: post.cpu_arr, cpu_hw_cr3_pcid: post.cpu_hw_cr3_pcid, ..pre }),
        post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Idle),
        post.cpu_arr.inv(),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().is_init(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.cpu_arr.spec_index(cpu_id).view().locking_thread() == pre.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        post.cpu_arr.spec_index(cpu_id).view().killer_info() == pre.cpu_arr.spec_index(cpu_id).view().killer_info(),
        post.cpu_arr.spec_index(cpu_id).view().view_rodata() == pre.cpu_arr.spec_index(cpu_id).view().view_rodata(),
        post.cpu_arr.spec_index(cpu_id).view().view_ghost() == pre.cpu_arr.spec_index(cpu_id).view().view_ghost(),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == (CpuView { state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None,
            current_cr3: default_cr3, current_pcid: KERNEL_DEFAULT_PCID, ..pre.cpu_arr.spec_index(cpu_id).view().view().view() }),
        post.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() == pre.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm(),
        post.cpu_hw_cr3_pcid[cpu_id as int].inv(),
        post.cpu_hw_cr3_pcid[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID),
        post.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == pre.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu(),
        forall|c: CpuId| #![trigger post.cpu_hw_cr3_pcid[c as int]] #![trigger pre.cpu_hw_cr3_pcid[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_hw_cr3_pcid[c as int] == pre.cpu_hw_cr3_pcid[c as int],
        typed_lock_maps_aligned(&pre, &lctx),
        post.inv(),
        !lctx.cpu_lock_map().dom().contains(cpu_id),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned);
    reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}

/// The wake-up IPI of `CpuOpArray::mark_idle_after_wake` stays within the step-boundary framing of a thread between its sections that
/// does not run on the target. The IPI runs inside the waker's section, so the invariant after it is assumed.
pub proof fn cpu_op_woken_respects_boundary(pre: KernelK, post: KernelK, cpu_id: CpuId, lctx: LocalContext)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        post == (KernelK { cpu_op: post.cpu_op, ..pre }),
        post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Idle),
        typed_lock_maps_aligned(&pre, &lctx),
        post.inv(),
        cpu_id != lctx.cpu_id(),
    ensures kernel_step_boundary_framing(pre, post, lctx),
{
    held_kernel_objects_unchanged_reflexive(&pre, &lctx);
    assert(held_owner_rodata_unchanged(pre, post, lctx)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(container_process_wf); reveal(container_owned_pages_wf); };
    reveal(cpu_op_wf); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
}
}

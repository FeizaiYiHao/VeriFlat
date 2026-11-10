use vstd::prelude::*;
use vstd::assert_maps_equal;
use crate::*;

verus! {
/// Under the kernel invariant, what CPU `cpu_id` may cache under `pcid` in K it may also cache in the user projection.
pub proof fn kernel_cpu_tlb_within_may_cache_projection(krnl: &KernelK, cpu_id: CpuId, pcid: Pcid, tlb: SingleTLB, cache: PagingStructureCache)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_tlb_within_may_cache(*krnl, cpu_id, pcid, tlb, cache),
    ensures
        cpu_tlb_within_may_cache_u(kernel_k_user_projection(*krnl), cpu_id, pcid, tlb),
        cpu_tlb_within_may_cache_u(kernel_k_to_kernel_u(*krnl), cpu_id, pcid, tlb),
{
    let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_user_projection_at(krnl, cpu_id);
    if pcid != KERNEL_DEFAULT_PCID && cpu.current_pcid == pcid && cpu.current_pagetable is Some {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, cpu.current_process->Some_0); kernel_process_user_projection_at(krnl, cpu.current_process->Some_0);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), cpu.current_pagetable->Some_0); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_mapping_1g);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}

/// Under the kernel invariant, what the IOTLB may cache for domain `did` in K it may also cache in the user projection; a
/// zombie anchor owner's emptied IOMMU table backs no translation.
pub proof fn kernel_iommu_tlb_within_may_cache_projection(krnl: &KernelK, did: VtdDomainId, tlb: SingleTLB)
    requires
        krnl.inv(),
        vtd_domain_id_valid(did),
        iommu_tlb_within_may_cache(*krnl, did, tlb),
    ensures
        iommu_tlb_within_may_cache_u(kernel_k_user_projection(*krnl), did, tlb),
        iommu_tlb_within_may_cache_u(kernel_k_to_kernel_u(*krnl), did, tlb),
{
    let anchor = pci_bdf_of_did(did);
    let root_table = krnl.irt.view();
    kernel_u_user_domains_projection(krnl); root_table.user_view_eq_owners_and_attached();
    if root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) {
        let owner = root_table.spec_index_owner(anchor.0, anchor.1, anchor.2);
        let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
        assert({
            &&& krnl.prc_mp.dom().contains(owner)
            &&& root_table.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) is Some
            &&& krnl.prc_mp.spec_index(owner).view().iommu_table is Some
            &&& krnl.it_mp.dom().contains(it)
            &&& krnl.it_mp.spec_index(it).view().did == Some(did)
        }) by { reveal(iommu_root_table_process_wf); root_table.wf_context_entry_at(anchor.0, anchor.1, anchor.2); };
        process_perms_wf_at(krnl.prc_mp, owner); kernel_process_user_projection_at(krnl, owner);
        process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, owner); iommu_table_no_huge_leaf_wf_at(krnl.it_mp, it);
        if krnl.prc_mp.spec_index(owner).view().zombie {
            assert(tlb.tlb_4k().dom() =~= Set::<VAddr>::empty() && tlb.tlb_2m().dom() =~= Set::<VAddr>::empty() && tlb.tlb_1g().dom() =~= Set::<VAddr>::empty());
        }
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}

/// A register change on cpu `cpu_id` projects to its U step: the registers of the live thread the cpu runs become `regs`.
pub proof fn kernel_k_regs_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers)
    requires
        pre.inv(),
        kernel_k_regs_changed(*pre, *post, cpu_id, regs),
    ensures
        kernel_u_regs_changed_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_regs_changed_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, regs),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let t = pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(pre.thrd_mp, pre.cpu_arr, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert(kernel_u_regs_changed_step_pre(pre_u, cpu_id)) by { reveal(kernel_u_regs_changed_step_pre); };
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(t, ThreadU { regs, ..pre_u.thread_map[t] }), x => {
        if pre.thrd_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); thread_cpu_wf_thread_at(pre.thrd_mp, pre.cpu_arr, x); }
    });
    assert(kernel_u_regs_changed_step(pre_u, post_u, cpu_id, regs)) by { reveal(kernel_u_regs_changed_step); reveal(kernel_k_to_kernel_u); };
}

/// Writing the return values on cpu `cpu_id` projects to its U step: `rax`, `rdx` and `rsi` of the live thread the cpu runs
/// take them.
pub proof fn kernel_k_trap_return_values_written_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, rax: u64, rdx: u64, rsi: u64)
    requires
        pre.inv(),
        kernel_k_trap_return_values_written(*pre, *post, cpu_id, rax, rdx, rsi),
    ensures
        kernel_u_trap_return_values_written_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_return_values_written_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, rax, rdx, rsi),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let t = pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    let thread = pre_u.thread_map[t];
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(pre.thrd_mp, pre.cpu_arr, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert(kernel_u_trap_return_values_written_step_pre(pre_u, cpu_id)) by { reveal(kernel_u_trap_return_values_written_step_pre); };
    kernel_thread_projection_at(pre, t);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(t, ThreadU { regs: Registers { rax, rdx, rsi, ..thread.regs }, ..thread }), x => {
        let c = pre.thrd_mp.spec_index(x).view().state->RUNNING_cpu_id;
        if pre.thrd_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); thread_cpu_wf_thread_at(pre.thrd_mp, pre.cpu_arr, x); }
        if c != cpu_id { vstd::map::axiom_map_remove_different(pre.cpu_trap_frame.view().view(), c, cpu_id); vstd::map::axiom_map_remove_different(post.cpu_trap_frame.view().view(), c, cpu_id); }
    });
    assert(kernel_u_trap_return_values_written_step(pre_u, post_u, cpu_id, rax, rdx, rsi)) by { reveal(kernel_u_trap_return_values_written_step); reveal(kernel_k_to_kernel_u); };
}
}

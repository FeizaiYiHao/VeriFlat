use vstd::prelude::*;
use vstd::assert_maps_equal;
use crate::*;

verus! {
/// Under the kernel invariant, what CPU `cpu_id` may cache under `pcid` in K it may also cache in the user projection.
pub proof fn cpu_tlb_within_may_cache_implies_cpu_tlb_within_may_cache_u(krnl: &KernelK, cpu_id: CpuId, pcid: Pcid, tlb: SingleTLB, cache: PagingStructureCache)
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
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip,
            WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_nonempty_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_nonempty_2m_l2_eq;
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}

/// Under the kernel invariant, what the IOTLB may cache for domain `did` in K it may also cache in the user projection; a
/// zombie anchor owner's emptied IOMMU table backs no translation.
pub proof fn iommu_tlb_within_may_cache_implies_iommu_tlb_within_may_cache_u(krnl: &KernelK, did: VtdDomainId, tlb: SingleTLB)
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
    assert(pci_bdf_valid(anchor.0, anchor.1, anchor.2) && pci_bdf_did(anchor.0, anchor.1, anchor.2) == did) by (nonlinear_arith) requires vtd_domain_id_valid(did), anchor == pci_bdf_of_did(did);
    kernel_k_user_projection_implies_domains_and_scalars_from_k(krnl); root_table.user_view_eq_owners_and_attached();
    if root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) {
        let owner = root_table.spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0;
        let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
        assert({
            &&& root_table.spec_index_owner(anchor.0, anchor.1, anchor.2) is Some
            &&& krnl.prc_mp.dom().contains(owner)
            &&& root_table.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) is Some
            &&& krnl.prc_mp.spec_index(owner).view().iommu_table is Some
            &&& krnl.it_mp.dom().contains(it)
            &&& krnl.it_mp.spec_index(it).view().did == Some(did)
        }) by { reveal(iommu_root_table_process_wf); root_table.wf_context_entry_at(anchor.0, anchor.1, anchor.2); };
        process_perms_wf_at(krnl.prc_mp, owner); kernel_process_user_projection_at(krnl, owner);
        process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, owner);
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
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post);
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
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post);
    assert(kernel_u_trap_return_values_written_step_pre(pre_u, cpu_id)) by { reveal(kernel_u_trap_return_values_written_step_pre); };
    kernel_thread_projection_at(pre, t);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(t, ThreadU { regs: Registers { rax, rdx, rsi, ..thread.regs }, ..thread }), x => {
        let c = pre.thrd_mp.spec_index(x).view().state->RUNNING_cpu_id;
        if pre.thrd_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); thread_cpu_wf_thread_at(pre.thrd_mp, pre.cpu_arr, x); }
        if c != cpu_id { vstd::map::axiom_map_remove_different(pre.cpu_trap_frame.view().view(), c, cpu_id); vstd::map::axiom_map_remove_different(post.cpu_trap_frame.view().view(), c, cpu_id); }
    });
    assert(kernel_u_trap_return_values_written_step(pre_u, post_u, cpu_id, rax, rdx, rsi)) by { reveal(kernel_u_trap_return_values_written_step); reveal(kernel_k_to_kernel_u); };
}

/// A CPU TLB fill under the kernel invariant is the matching user TLB fill in the projection.
pub proof fn kernel_k_cpu_tlb_filled_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, pcid: Pcid, added: SingleTLB, added_cache: PagingStructureCache)
    requires
        pre.inv(),
        kernel_k_cpu_tlb_filled(*pre, *post, cpu_id, pcid, added, added_cache),
    ensures kernel_u_cpu_tlb_filled_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, pcid, added),
{
    reveal(kernel_u_cpu_tlb_filled_step); reveal(kernel_k_to_kernel_u);
    cpu_tlb_within_may_cache_implies_cpu_tlb_within_may_cache_u(pre, cpu_id, pcid, added, added_cache);
}

/// An IOTLB fill under the kernel invariant is the matching user IOTLB fill in the projection.
pub proof fn kernel_k_iommu_tlb_filled_implies_u_step(pre: &KernelK, post: &KernelK, did: VtdDomainId, added: SingleTLB, added_cache: PagingStructureCache)
    requires
        pre.inv(),
        kernel_k_iommu_tlb_filled(*pre, *post, did, added, added_cache),
    ensures kernel_u_iommu_tlb_filled_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), did, added),
{
    reveal(kernel_u_iommu_tlb_filled_step); reveal(kernel_k_to_kernel_u);
    iommu_tlb_within_may_cache_implies_iommu_tlb_within_may_cache_u(pre, did, added);
}

/// A context-cache fill changes neither projection.
pub proof fn kernel_k_iommu_context_cache_filled_implies_u_step(pre: &KernelK, post: &KernelK, bdf: PciBdf, entry: (PageTableRoot, VtdDomainId))
    requires
        pre.inv(),
        kernel_k_iommu_context_cache_filled(*pre, *post, bdf, entry),
    ensures kernel_u_iommu_context_cache_filled_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post)),
{ reveal(kernel_u_iommu_context_cache_filled_step); reveal(kernel_k_to_kernel_u); }

/// A user store issued on cpu `cpu_id` changes no projection: store buffers are not user-visible.
pub proof fn kernel_k_user_store_issued_implies_u_unchanged(pre: &KernelK, post: &KernelK, cpu_id: CpuId, s: PendingStore)
    requires kernel_k_user_store_issued(*pre, *post, cpu_id, s),
    ensures kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{ reveal(kernel_k_to_kernel_u); }

/// A user store committed from cpu `cpu_id`'s store buffer changes no projection.
pub proof fn kernel_k_user_store_committed_implies_u_unchanged(pre: &KernelK, post: &KernelK, cpu_id: CpuId, s: PendingStore)
    requires kernel_k_user_store_committed(*pre, *post, cpu_id, s),
    ensures kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{ reveal(kernel_k_to_kernel_u); }

/// A DMA request issued by the device at `bdf` changes no projection: pending DMA is not user-visible.
pub proof fn kernel_k_dma_issued_implies_u_unchanged(pre: &KernelK, post: &KernelK, bdf: PciBdf, r: PendingDma)
    requires kernel_k_dma_issued(*pre, *post, bdf, r),
    ensures kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{ reveal(kernel_k_to_kernel_u); }

/// A completed DMA request changes no projection.
pub proof fn kernel_k_dma_completed_implies_u_unchanged(pre: &KernelK, post: &KernelK, r: PendingDma)
    requires kernel_k_dma_completed(*pre, *post, r),
    ensures kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{ reveal(kernel_k_to_kernel_u); }

/// A trap entry on cpu `cpu_id` projects to the user trap entry: the frame of its trap-frame slot takes the registers the
/// running thread had in user mode, so no thread's registers change.
pub proof fn kernel_k_trap_enter_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, kernel_regs: Registers)
    requires
        pre.inv(),
        kernel_k_trap_enter(*pre, *post, cpu_id, kernel_regs),
    ensures
        kernel_u_trap_enter_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_enter_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post);
    assert(kernel_u_trap_enter_step_pre(pre_u, cpu_id)) by { reveal(kernel_u_trap_enter_step_pre); };
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, x => {
        let c = pre.thrd_mp.spec_index(x).view().state->RUNNING_cpu_id;
        if pre.thrd_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); thread_cpu_wf_thread_at(pre.thrd_mp, pre.cpu_arr, x); }
        if c != cpu_id { vstd::map::axiom_map_remove_different(pre.cpu_trap_frame.view().view(), c, cpu_id); vstd::map::axiom_map_remove_different(post.cpu_trap_frame.view().view(), c, cpu_id); }
    });
    assert(kernel_u_trap_enter_step(pre_u, post_u, cpu_id)) by {
        reveal(kernel_u_trap_enter_step); reveal(kernel_k_to_kernel_u);
        assert(post_u.cpu_array =~= pre_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::Trap, ..pre_u.cpu_array[cpu_id as int] }));
    };
}

/// A trap return on cpu `cpu_id` projects to the user trap return: the cpu loads the frame of its trap-frame slot, so no
/// thread's registers change.
pub proof fn kernel_k_trap_return_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_return(*pre, *post, cpu_id),
    ensures
        kernel_u_trap_return_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_return_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post);
    assert(kernel_u_trap_return_step_pre(pre_u, cpu_id)) by { reveal(kernel_u_trap_return_step_pre); };
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, x => {
        if pre.thrd_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); }
    });
    assert(kernel_u_trap_return_step(pre_u, post_u, cpu_id)) by {
        reveal(kernel_u_trap_return_step); reveal(kernel_k_to_kernel_u);
        assert(post_u.cpu_array =~= pre_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::User, ..pre_u.cpu_array[cpu_id as int] }));
    };
}

/// A trap divert on cpu `cpu_id` projects to the user trap divert: the cpu stays off user mode, so no thread's registers
/// change.
pub proof fn kernel_k_trap_divert_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_divert(*pre, *post, cpu_id),
    ensures
        kernel_u_trap_divert_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_divert_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post);
    assert(kernel_u_trap_divert_step_pre(pre_u, cpu_id)) by { reveal(kernel_u_trap_divert_step_pre); };
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, x => {
        if pre.thrd_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); }
    });
    assert(kernel_u_trap_divert_step(pre_u, post_u, cpu_id)) by {
        reveal(kernel_u_trap_divert_step); reveal(kernel_k_to_kernel_u);
        assert(post_u.cpu_array =~= pre_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::Idle, ..pre_u.cpu_array[cpu_id as int] }));
    };
}
}

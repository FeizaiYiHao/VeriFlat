use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_pci_bar::syscall_pci_bar::syscall_pci_bar_spec::*;

verus! {
/// The 4K page `page_index` of BAR table slot `slot` is a BAR page of the slot's function.
pub proof fn bar_slot_page_implies_function_of_page(bars: Seq<PciBarEntry>, slot: usize, page_index: usize)
    requires pci_bar_table_wf(bars), slot < bars.len(), bars[slot as int].spec_page_4k(page_index) is Some,
    ensures
        bars[slot as int].spec_page_4k(page_index)->0 % 0x1000 == 0,
        pci_bar_page(bars, bars[slot as int].spec_page_4k(page_index)->0),
        pci_bar_function_of_page(bars, bars[slot as int].spec_page_4k(page_index)->0) == Some(bars[slot as int].bdf),
{
    let e = bars[slot as int];
    let p = e.spec_page_4k(page_index)->0;
    pci_bar_table_wf_at(bars, slot as int);
    assert(PAGE_SZ_4K == 0x1000 && MEM_4K_MASK == 0x0000_ffff_ffff_f000) by (compute);
    assert(p as int == e.base as int / 4096 * 4096 + page_index as int * 4096 && p % 4096 == 0 && e.base as int / 4096 * 4096 <= p) by (nonlinear_arith)
        requires p as int == e.base as int / 4096 * 4096 + page_index as int * 4096, p as int == e.base as int / PAGE_SZ_4K as int * PAGE_SZ_4K as int + page_index as int * PAGE_SZ_4K as int,
            PAGE_SZ_4K == 0x1000, e.base as int / 4096 * 4096 + page_index as int * 4096 < e.base as int + e.size as int, e.base as int + e.size as int <= 0x0001_0000_0000_0000;
    assert(e.envelope_contains(p));
    bar_envelope_implies_function_of_page(bars, slot as int, p);
}

/// Every 4K-aligned page inside the 2M chunk `index` of BAR table slot `slot`, the chunk's first page included, is a BAR page of the
/// slot's function.
pub proof fn bar_slot_chunk_page_implies_function_of_page(bars: Seq<PciBarEntry>, slot: usize, index: usize, p: PAddr)
    requires
        pci_bar_table_wf(bars), slot < bars.len(), bars[slot as int].spec_chunk_2m(index) is Some,
        p % 0x1000 == 0 || p == bars[slot as int].spec_chunk_2m(index)->0,
        bars[slot as int].spec_chunk_2m(index)->0 <= p < bars[slot as int].spec_chunk_2m(index)->0 + 0x200000,
    ensures
        bars[slot as int].spec_chunk_2m(index)->0 % 0x200000 == 0,
        pci_bar_page(bars, p),
        pci_bar_function_of_page(bars, p) == Some(bars[slot as int].bdf),
{
    let e = bars[slot as int];
    let c = e.spec_chunk_2m(index)->0;
    pci_bar_table_wf_at(bars, slot as int);
    assert(PAGE_SZ_4K == 0x1000 && PAGE_SZ_2M == 0x200000 && MEM_4K_MASK == 0x0000_ffff_ffff_f000) by (compute);
    assert(c % 0x200000 == 0 && e.base <= c && e.base as int / 4096 * 4096 <= e.base) by (nonlinear_arith)
        requires c as int == (e.base as int + 0x200000 - 1) / 0x200000 * 0x200000 + index as int * 0x200000, c as int + 0x200000 <= e.base as int + e.size as int,
            e.base as int + e.size as int <= 0x0001_0000_0000_0000;
    assert(p % 0x1000 == 0) by (nonlinear_arith) requires p % 0x1000 == 0 || p == c, c % 0x200000 == 0;
    assert(e.envelope_contains(p));
    bar_envelope_implies_function_of_page(bars, slot as int, p);
}

/// Entering a 4K BAR map on a cpu of `a` locks only objects of `a`.
pub proof fn map_pci_bar_4k_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_4k_enter_step_pre(old_u, cpu_id, slot, page_index, va),
        map_pci_bar_4k_enter_step(old_u, new_u, cpu_id, va),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_4k_enter_step_pre); reveal(map_pci_bar_4k_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `map_pci_bar_4k_enter_step_lr` preserves isolation.
pub proof fn map_pci_bar_4k_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_4k_enter_step_pre(old_u, cpu_id, slot, page_index, va),
        map_pci_bar_4k_enter_step(old_u, new_u, cpu_id, va),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_4k_enter_step_pre); reveal(map_pci_bar_4k_enter_step);
    assert(new_u.thread_map.dom() =~= old_u.thread_map.dom());
    assert(forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]] old_u.thread_map.dom().contains(t)
        ==> new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container && new_u.thread_map[t].state == old_u.thread_map[t].state);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Entering a 2M BAR map on a cpu of `a` locks only objects of `a`.
pub proof fn map_pci_bar_2m_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, slot: usize, index: usize, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_enter_step_pre(old_u, cpu_id, slot, index, va),
        map_pci_bar_2m_enter_step(old_u, new_u, cpu_id, va),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_2m_enter_step_pre); reveal(map_pci_bar_2m_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `map_pci_bar_2m_enter_step_lr` preserves isolation.
pub proof fn map_pci_bar_2m_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, slot: usize, index: usize, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_enter_step_pre(old_u, cpu_id, slot, index, va),
        map_pci_bar_2m_enter_step(old_u, new_u, cpu_id, va),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_2m_enter_step_pre); reveal(map_pci_bar_2m_enter_step);
    assert(new_u.thread_map.dom() =~= old_u.thread_map.dom());
    assert(forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]] old_u.thread_map.dom().contains(t)
        ==> new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container && new_u.thread_map[t].state == old_u.thread_map[t].state);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A 4K BAR map directory step on a cpu of `a` changes only its running thread and that thread's process.
pub proof fn map_pci_bar_4k_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_4k_directory_step_pre(old_u, cpu_id),
        map_pci_bar_4k_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_4k_directory_step_pre); reveal(map_pci_bar_4k_directory_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `map_pci_bar_4k_directory_step_lr` preserves isolation.
pub proof fn map_pci_bar_4k_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_4k_directory_step_pre(old_u, cpu_id),
        map_pci_bar_4k_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_4k_directory_step_pre); reveal(map_pci_bar_4k_directory_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A 2M BAR map directory step on a cpu of `a` changes only its running thread and that thread's process.
pub proof fn map_pci_bar_2m_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_directory_step_pre(old_u, cpu_id),
        map_pci_bar_2m_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_2m_directory_step_pre); reveal(map_pci_bar_2m_directory_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `map_pci_bar_2m_directory_step_lr` preserves isolation.
pub proof fn map_pci_bar_2m_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_directory_step_pre(old_u, cpu_id),
        map_pci_bar_2m_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_2m_directory_step_pre); reveal(map_pci_bar_2m_directory_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A 2M BAR map TLB flush of the hidden empty L1 page on a cpu of `a` read-locks the cpu set of a container of `a` and changes only
/// cpu TLBs, which no domain view contains.
pub proof fn map_pci_bar_2m_flush_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_l1_step_pre(old_u, cpu_id, false),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_2m_l1_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `map_pci_bar_2m_flush_step_lr` preserves isolation.
pub proof fn map_pci_bar_2m_flush_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_l1_step_pre(old_u, cpu_id, false),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_2m_l1_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Recording the flush of the hidden empty L1 page on a cpu of `a` changes only its running thread and the cpu set lock of its
/// container, a container of `a`.
pub proof fn map_pci_bar_2m_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_l1_step_pre(old_u, cpu_id, false),
        map_pci_bar_2m_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_2m_l1_step_pre); reveal(map_pci_bar_2m_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `map_pci_bar_2m_flushed_step_lr` preserves isolation.
pub proof fn map_pci_bar_2m_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_l1_step_pre(old_u, cpu_id, false),
        map_pci_bar_2m_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_2m_l1_step_pre); reveal(map_pci_bar_2m_flushed_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Crediting the reclaimed L1 page's 4K quota on a cpu of `a` changes only the quota of the running thread's container, a container
/// of `a`.
pub proof fn map_pci_bar_2m_l1_reclaim_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_l1_step_pre(old_u, cpu_id, true),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_2m_l1_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `map_pci_bar_2m_l1_reclaim_step_lr` preserves isolation.
pub proof fn map_pci_bar_2m_l1_reclaim_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_l1_step_pre(old_u, cpu_id, true),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures isolated(new_u, a, b),
{
    reveal(map_pci_bar_2m_l1_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The exit of a 4K BAR map on a cpu of `a` maps a page of a BAR of a function its process owns into that process of `a` and
/// counts it for the function.
pub proof fn map_pci_bar_4k_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, f: PciBdf, entry: MapEntry, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_4k_exit_step_pre(old_u, cpu_id, va),
        map_pci_bar_4k_exit_step(old_u, new_u, cpu_id, va, f, entry),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_4k_exit_step_pre); reveal(map_pci_bar_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `map_pci_bar_4k_exit_step_lr`, mapping the page `page_index` of BAR table slot `slot`, preserves isolation: the page
/// is a BAR page of a function owned by the mapping process of `a`, so no process of `b` maps it as an IO leaf or covers it with a
/// RAM leaf.
pub proof fn map_pci_bar_4k_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, slot: usize, page_index: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        ({
            let thread = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0];
            let va = thread.syscall_progress->Some_0->MapPciBar4k_va;
            &&& map_pci_bar_4k_exit_step_pre(old_u, cpu_id, va)
            &&& slot < old_u.pci_bars.len()
            &&& old_u.pci_bars[slot as int].spec_page_4k(page_index) is Some
            &&& map_pci_bar_4k_exit_step(old_u, new_u, cpu_id, va, old_u.pci_bars[slot as int].bdf, map_pci_bar_io_entry(map_pci_bar_4k_page(old_u, slot, page_index), thread.owning_container))
        }),
    ensures isolated(new_u, a, b),
{
    let pa = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_proc;
    assert(old_u.process_map.dom().contains(pa) && in_domain(old_u, a, old_u.process_map[pa].owning_container) && old_u.process_map[pa].pagetable is Some
        && old_u.process_map[pa].pagetable->Some_0.pci_functions.dom().contains(old_u.pci_bars[slot as int].bdf)) by {
        reveal(map_pci_bar_4k_exit_step_pre); reveal(map_pci_bar_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    };
    owned_bar_page_implies_outside_domain_leaves(old_u, pa, slot, page_index, b);
    reveal(map_pci_bar_4k_exit_step_pre); reveal(map_pci_bar_4k_exit_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b); memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u, new_u, a, b);
}

/// The page `page_index` of BAR table slot `slot`, whose function the page table of process `pa`, outside `b`, holds, is mapped by
/// no 4K, 2M, or 1G page-table leaf or 4K IOMMU leaf of a process of `b`: an IO leaf of such a process maps a BAR page of a function
/// that process owns, and no RAM leaf covers a BAR page.
pub proof fn owned_bar_page_implies_outside_domain_leaves(u: KernelU, pa: RwLockProcessPtr, slot: usize, page_index: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u),
        u.process_map.dom().contains(pa),
        !in_domain(u, b, u.process_map[pa].owning_container),
        u.process_map[pa].pagetable is Some,
        slot < u.pci_bars.len(),
        u.pci_bars[slot as int].spec_page_4k(page_index) is Some,
        u.process_map[pa].pagetable->Some_0.pci_functions.dom().contains(u.pci_bars[slot as int].bdf),
    ensures
        ({
            let pg = map_pci_bar_4k_page(u, slot, page_index);
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                    && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v) ==> u.process_map[q].pagetable->Some_0.mapping_4k[v].addr != pg
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].iommu_table is Some
                    && u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v) ==> u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr != pg
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_2m[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                    && u.process_map[q].pagetable->Some_0.mapping_2m.dom().contains(v) ==> !in_2m_frame(u.process_map[q].pagetable->Some_0.mapping_2m[v].addr, pg)
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_1g[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                    && u.process_map[q].pagetable->Some_0.mapping_1g.dom().contains(v) ==> !in_1g_frame(u.process_map[q].pagetable->Some_0.mapping_1g[v].addr, pg)
        }),
{
    let bars = u.pci_bars;
    let f = bars[slot as int].bdf;
    let pg = map_pci_bar_4k_page(u, slot, page_index);
    reveal(kernel_u_io_leaf_wf); reveal(kernel_u_pci_ownership_wf); reveal(in_2m_frame); reveal(in_1g_frame);
    bar_slot_page_implies_function_of_page(bars, slot, page_index);
    assert(u.iommu_root_table.owners[f.0 as int][f.1 as int][f.2 as int] == Some(pa));
    assert forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
        u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
            && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v) implies u.process_map[q].pagetable->Some_0.mapping_4k[v].addr != pg by {
        let e = u.process_map[q].pagetable->Some_0.mapping_4k[v];
        if e.is_io && e.addr == pg { assert(u.iommu_root_table.owners[f.0 as int][f.1 as int][f.2 as int] == Some(q)); }
    };
    assert forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_2m[v]]
        u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
            && u.process_map[q].pagetable->Some_0.mapping_2m.dom().contains(v) implies !in_2m_frame(u.process_map[q].pagetable->Some_0.mapping_2m[v].addr, pg) by {
        let e = u.process_map[q].pagetable->Some_0.mapping_2m[v];
        if e.is_io && e.addr <= pg < e.addr + 0x200000 {
            bar_chunk_page_implies_function_of_chunk(bars, e.addr, pg);
            assert(u.iommu_root_table.owners[f.0 as int][f.1 as int][f.2 as int] == Some(q));
        }
    };
}

/// The exit of a 2M BAR map on a cpu of `a` maps a 2M chunk of a BAR of a function its process owns into that process of `a` and
/// counts it for the function.
pub proof fn map_pci_bar_2m_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, f: PciBdf, entry: MapEntry, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        map_pci_bar_2m_exit_step_pre(old_u, cpu_id, va),
        map_pci_bar_2m_exit_step(old_u, new_u, cpu_id, va, f, entry),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(map_pci_bar_2m_exit_step_pre); reveal(map_pci_bar_2m_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `map_pci_bar_2m_exit_step_lr`, mapping the 2M chunk `index` of BAR table slot `slot`, preserves isolation: every
/// page of the chunk is a BAR page of a function owned by the mapping process of `a`, so no process of `b` maps one as an IO leaf or
/// covers one with a RAM leaf.
pub proof fn map_pci_bar_2m_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, slot: usize, index: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        ({
            let thread = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0];
            let va = thread.syscall_progress->Some_0->MapPciBar2m_va;
            &&& map_pci_bar_2m_exit_step_pre(old_u, cpu_id, va)
            &&& slot < old_u.pci_bars.len()
            &&& old_u.pci_bars[slot as int].spec_chunk_2m(index) is Some
            &&& map_pci_bar_2m_exit_step(old_u, new_u, cpu_id, va, old_u.pci_bars[slot as int].bdf, map_pci_bar_io_entry(map_pci_bar_2m_chunk(old_u, slot, index), thread.owning_container))
        }),
    ensures isolated(new_u, a, b),
{
    let pa = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_proc;
    assert(old_u.process_map.dom().contains(pa) && in_domain(old_u, a, old_u.process_map[pa].owning_container) && old_u.process_map[pa].pagetable is Some
        && old_u.process_map[pa].pagetable->Some_0.pci_functions.dom().contains(old_u.pci_bars[slot as int].bdf)) by {
        reveal(map_pci_bar_2m_exit_step_pre); reveal(map_pci_bar_2m_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    };
    owned_bar_chunk_implies_outside_domain_leaves(old_u, pa, slot, index, b);
    reveal(map_pci_bar_2m_exit_step_pre); reveal(map_pci_bar_2m_exit_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b); memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u, new_u, a, b);
}

/// Every page of the 2M chunk `index` of BAR table slot `slot`, whose function the page table of process `pa`, outside `b`, holds,
/// is mapped by no 4K, 2M, or 1G page-table leaf or 4K IOMMU leaf of a process of `b`.
pub proof fn owned_bar_chunk_implies_outside_domain_leaves(u: KernelU, pa: RwLockProcessPtr, slot: usize, index: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u),
        u.process_map.dom().contains(pa),
        !in_domain(u, b, u.process_map[pa].owning_container),
        u.process_map[pa].pagetable is Some,
        slot < u.pci_bars.len(),
        u.pci_bars[slot as int].spec_chunk_2m(index) is Some,
        u.process_map[pa].pagetable->Some_0.pci_functions.dom().contains(u.pci_bars[slot as int].bdf),
    ensures
        ({
            let c = map_pci_bar_2m_chunk(u, slot, index);
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                    && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v) ==> !in_2m_frame(c, u.process_map[q].pagetable->Some_0.mapping_4k[v].addr)
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].iommu_table is Some
                    && u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v) ==> !in_2m_frame(c, u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr)
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_2m[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                    && u.process_map[q].pagetable->Some_0.mapping_2m.dom().contains(v) ==> u.process_map[q].pagetable->Some_0.mapping_2m[v].addr != c
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_1g[v]]
                u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                    && u.process_map[q].pagetable->Some_0.mapping_1g.dom().contains(v) ==> !in_1g_frame(u.process_map[q].pagetable->Some_0.mapping_1g[v].addr, c)
        }),
{
    let bars = u.pci_bars;
    let f = bars[slot as int].bdf;
    let c = map_pci_bar_2m_chunk(u, slot, index);
    reveal(kernel_u_io_leaf_wf); reveal(kernel_u_pci_ownership_wf); reveal(in_2m_frame); reveal(in_1g_frame);
    bar_slot_chunk_page_implies_function_of_page(bars, slot, index, c);
    assert(u.iommu_root_table.owners[f.0 as int][f.1 as int][f.2 as int] == Some(pa));
    assert forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
        u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
            && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v) implies !in_2m_frame(c, u.process_map[q].pagetable->Some_0.mapping_4k[v].addr) by {
        let e = u.process_map[q].pagetable->Some_0.mapping_4k[v];
        if c <= e.addr < c + 0x200000 {
            if e.is_io { bar_page_implies_aligned(bars, e.addr); }
            bar_slot_chunk_page_implies_function_of_page(bars, slot, index, e.addr);
            if e.is_io { assert(u.iommu_root_table.owners[f.0 as int][f.1 as int][f.2 as int] == Some(q)); }
        }
    };
    assert forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
        u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].iommu_table is Some
            && u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v) implies !in_2m_frame(c, u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr) by {
        let e = u.process_map[q].iommu_table->Some_0.mapping_4k[v];
        if c <= e.addr < c + 0x200000 { assert(e.addr % 0x1000 == 0); bar_slot_chunk_page_implies_function_of_page(bars, slot, index, e.addr); }
    };
    assert forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_2m[v]]
        u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
            && u.process_map[q].pagetable->Some_0.mapping_2m.dom().contains(v) implies u.process_map[q].pagetable->Some_0.mapping_2m[v].addr != c by {
        let e = u.process_map[q].pagetable->Some_0.mapping_2m[v];
        if e.addr == c && e.is_io { assert(u.iommu_root_table.owners[f.0 as int][f.1 as int][f.2 as int] == Some(q)); }
        if e.addr == c && !e.is_io { assert(e.addr <= c < e.addr + 0x200000); }
    };
    assert forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_1g[v]]
        u.process_map.dom().contains(q) && in_domain(u, b, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
            && u.process_map[q].pagetable->Some_0.mapping_1g.dom().contains(v) implies !in_1g_frame(u.process_map[q].pagetable->Some_0.mapping_1g[v].addr, c) by {
        let e = u.process_map[q].pagetable->Some_0.mapping_1g[v];
        if e.addr <= c < e.addr + 0x4000_0000 { assert(!pci_bar_page(bars, c)); }
    };
}

/// Hiding a 4K BAR leaf on a cpu of `a` locks objects of `a` and removes a mapping of a process of `a`.
pub proof fn unmap_pci_bar_4k_hide_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_hide_step_pre(old_u, cpu_id, va),
        unmap_pci_bar_4k_hide_step(old_u, new_u, cpu_id, va),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_4k_hide_step_pre); reveal(unmap_pci_bar_4k_hide_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_pci_bar_4k_hide_step_lr` preserves isolation: the process's mappings only shrink.
pub proof fn unmap_pci_bar_4k_hide_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_hide_step_pre(old_u, cpu_id, va),
        unmap_pci_bar_4k_hide_step(old_u, new_u, cpu_id, va),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_4k_hide_step_pre); reveal(unmap_pci_bar_4k_hide_step); reveal(kernel_u_cpu_ownership_wf);
    assert(new_u.thread_map.dom() =~= old_u.thread_map.dom());
    assert(forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]] old_u.thread_map.dom().contains(t)
        ==> new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container && new_u.thread_map[t].state == old_u.thread_map[t].state);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b); memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u, new_u, a, b);
}

/// Hiding a 2M BAR leaf on a cpu of `a` locks objects of `a` and removes a mapping of a process of `a`.
pub proof fn unmap_pci_bar_2m_hide_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_2m_hide_step_pre(old_u, cpu_id, va),
        unmap_pci_bar_2m_hide_step(old_u, new_u, cpu_id, va),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_2m_hide_step_pre); reveal(unmap_pci_bar_2m_hide_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_pci_bar_2m_hide_step_lr` preserves isolation: the process's mappings only shrink.
pub proof fn unmap_pci_bar_2m_hide_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_2m_hide_step_pre(old_u, cpu_id, va),
        unmap_pci_bar_2m_hide_step(old_u, new_u, cpu_id, va),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_2m_hide_step_pre); reveal(unmap_pci_bar_2m_hide_step); reveal(kernel_u_cpu_ownership_wf);
    assert(new_u.thread_map.dom() =~= old_u.thread_map.dom());
    assert(forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]] old_u.thread_map.dom().contains(t)
        ==> new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container && new_u.thread_map[t].state == old_u.thread_map[t].state);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b); memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u, new_u, a, b);
}

/// A BAR unmap TLB flush on a cpu of `a` read-locks the cpu set of a container of `a` and changes only cpu TLBs, which no domain
/// view contains.
pub proof fn unmap_pci_bar_4k_flush_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_flush_step_pre(old_u, cpu_id) || unmap_pci_bar_2m_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_4k_flush_step_pre); reveal(unmap_pci_bar_2m_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_pci_bar_4k_flush_step_lr` preserves isolation.
pub proof fn unmap_pci_bar_4k_flush_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_flush_step_pre(old_u, cpu_id) || unmap_pci_bar_2m_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_4k_flush_step_pre); reveal(unmap_pci_bar_2m_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Recording the 4K BAR unmap flush on a cpu of `a` changes only its running thread and the cpu set lock of its container.
pub proof fn unmap_pci_bar_4k_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_flush_step_pre(old_u, cpu_id),
        unmap_pci_bar_4k_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_4k_flush_step_pre); reveal(unmap_pci_bar_4k_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_pci_bar_4k_flushed_step_lr` preserves isolation.
pub proof fn unmap_pci_bar_4k_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_flush_step_pre(old_u, cpu_id),
        unmap_pci_bar_4k_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_4k_flush_step_pre); reveal(unmap_pci_bar_4k_flushed_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Recording the 2M BAR unmap flush on a cpu of `a` changes only its running thread and the cpu set lock of its container.
pub proof fn unmap_pci_bar_2m_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_2m_flush_step_pre(old_u, cpu_id),
        unmap_pci_bar_2m_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_2m_flush_step_pre); reveal(unmap_pci_bar_2m_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_pci_bar_2m_flushed_step_lr` preserves isolation.
pub proof fn unmap_pci_bar_2m_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_2m_flush_step_pre(old_u, cpu_id),
        unmap_pci_bar_2m_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_2m_flush_step_pre); reveal(unmap_pci_bar_2m_flushed_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The exit of a 4K BAR unmap on a cpu of `a` lowers a mapping count of its process, a process of `a`, and unlocks objects of `a`.
pub proof fn unmap_pci_bar_4k_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, f: PciBdf, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_flushed_step_pre(old_u, cpu_id),
        unmap_pci_bar_4k_exit_step(old_u, new_u, cpu_id, f),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_4k_flushed_step_pre); reveal(unmap_pci_bar_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `unmap_pci_bar_4k_exit_step_lr` preserves isolation.
pub proof fn unmap_pci_bar_4k_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, f: PciBdf, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_4k_flushed_step_pre(old_u, cpu_id),
        unmap_pci_bar_4k_exit_step(old_u, new_u, cpu_id, f),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_4k_flushed_step_pre); reveal(unmap_pci_bar_4k_exit_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The exit of a 2M BAR unmap on a cpu of `a` lowers a mapping count of its process, a process of `a`, and unlocks objects of `a`.
pub proof fn unmap_pci_bar_2m_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, f: PciBdf, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_2m_flushed_step_pre(old_u, cpu_id),
        unmap_pci_bar_2m_exit_step(old_u, new_u, cpu_id, f),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_pci_bar_2m_flushed_step_pre); reveal(unmap_pci_bar_2m_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `unmap_pci_bar_2m_exit_step_lr` preserves isolation.
pub proof fn unmap_pci_bar_2m_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, f: PciBdf, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_pci_bar_2m_flushed_step_pre(old_u, cpu_id),
        unmap_pci_bar_2m_exit_step(old_u, new_u, cpu_id, f),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_pci_bar_2m_flushed_step_pre); reveal(unmap_pci_bar_2m_exit_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The 4K and 2M BAR map and unmap results of a running cpu of `b` read only the view of `b`, which includes the BAR table.
pub proof fn pci_bar_syscall_results_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, slot: usize, index: usize, va: VAddr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures
        map_pci_bar_4k_syscall_result(u1, cpu_id, slot, index, va) == map_pci_bar_4k_syscall_result(u2, cpu_id, slot, index, va),
        map_pci_bar_2m_syscall_result(u1, cpu_id, slot, index, va) == map_pci_bar_2m_syscall_result(u2, cpu_id, slot, index, va),
        unmap_pci_bar_4k_syscall_result(u1, cpu_id, va) == unmap_pci_bar_4k_syscall_result(u2, cpu_id, va),
        unmap_pci_bar_2m_syscall_result(u1, cpu_id, va) == unmap_pci_bar_2m_syscall_result(u2, cpu_id, va),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread = u1.thread_map[cpu.current_thread->Some_0];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        &&& v1.processes.dom().contains(thread.owning_proc) && v1.processes[thread.owning_proc] == v2.processes[thread.owning_proc]
        &&& v1.pci_bars == v2.pci_bars
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!

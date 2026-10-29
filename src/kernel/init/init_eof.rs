use vstd::prelude::*;

verus! {
use crate::*;
use super::*;
use super::boot_eof_pages::*;

pub(super) proof fn boot_subsystems_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.subsystems_inv(),
{
    assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
    assert(pagetable_lower_wf(krnl.pt_mp, krnl.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(krnl.pt_mp, krnl.pt_lower.view())) by {
        reveal(pagetable_window_holders_hold_pagetable); reveal(PageTableC::wf_window_locks); reveal(PageTableC::wf_l3); reveal(PageTableHigher::wf_l4);
    };
    assert(pagetable_hidden_leaves_only_when_locked(krnl.pt_mp, krnl.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(krnl.pt_mp, krnl.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_lower_backup_wf(krnl.pt_mp, krnl.pt_lower.view()));
    assert(iommu_table_perms_wf(krnl.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
    assert(page_array_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
    assert(cpu_array_wf(krnl.cpu_arr, krnl.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(cpu_hw_cr3_pcid_wf(krnl.cpu_hw_cr3_pcid, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(cpu_hw_cr3_pcid_wf); reveal(PageTable::table_pages_wf); };
    assert(cpu_offline_flags_wf(krnl.cpu_offline_mp, krnl.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(cpu_op_wf(krnl.cpu_op.view().view(), krnl.cpu_arr)) by { reveal(cpu_op_wf); };
    assert(container_perms_wf(krnl.ctn_mp)) by { reveal(container_perms_wf); assert(container_tree_fields_wf(krnl.ctn_mp)) by { reveal(container_tree_fields_wf); }; };
    assert(process_perms_wf(krnl.prc_mp)) by { reveal(process_perms_wf); };
    assert(thread_perms_wf(krnl.thr_mp)) by {
        reveal(thread_perms_wf);
        assert(thread_free_quota_pending_empty_unless_wlocked(krnl.thr_mp)) by { reveal(thread_free_quota_pending_empty_unless_wlocked); };
        assert(thread_temp_alloc_empty_unless_wlocked(krnl.thr_mp)) by { reveal(thread_temp_alloc_empty_unless_wlocked); };
        assert(thread_syscall_progress_only_when_wlocked(krnl.thr_mp)) by { reveal(thread_syscall_progress_only_when_wlocked); };
        assert(thread_exited_only_when_wlocked(krnl.thr_mp)) by { reveal(thread_exited_only_when_wlocked); };
        assert(thread_ipc_transit_wf(krnl.thr_mp)) by { reveal(thread_ipc_transit_wf); };
    };
    assert(scheduler_perms_wf(krnl.sched_mp)) by { reveal(scheduler_perms_wf); };
    assert(cpu_set_perms_wf(krnl.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
    assert(pcid_allocator_perms_wf(krnl.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); };
    assert(allocator_perms_wf(krnl.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(krnl.allc_2m_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(krnl.allc_1g_mp)) by { reveal(allocator_perms_wf); };
}

#[verifier::spinoff_prover]
proof fn boot_memory_management_inv_eof_allocator_pages(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp),
{
    assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_allocator_free_pages(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.allocator_free_pages_wf(),
{
    assert(boot_free_4k_pool_wf(page_array, layout, free_4k_pool) && boot_free_2m_pool_wf(page_array, layout, free_2m_pool) && boot_free_1g_pool_wf(page_array, layout, free_1g_pool)) by { reveal(boot_page_array_ready); };
    assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
}

proof fn boot_memory_management_inv_eof_free_4k(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr),
{
    assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_free_2m(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr),
{
    assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_free_1g(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr),
{
    assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_object_pages(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_pages_wf(krnl.pg_arr, krnl.ctn_mp),
        process_pages_wf(krnl.pg_arr, krnl.prc_mp),
        pagetable_pages_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        thread_pages_wf(krnl.thr_mp, krnl.pg_arr),
        scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr),
        cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr),
        pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp),
        thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr),
        endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr),
{
    boot_memory_management_inv_eof_container_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_process_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_pagetable_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_thread_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_scheduler_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_cpu_set_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_pcid_allocator_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_thread_staged_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_endpoint_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
}

proof fn boot_memory_management_inv_eof_mappings(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        hugepage_2m_wf(krnl.pg_arr),
        hugepage_1g_wf(krnl.pg_arr),
        page_pagetable_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr),
        page_iommu_table_wf(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr),
{
    assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
    assert(hugepage_1g_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
    assert(page_pagetable_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(boot_page_array_ready); };
    assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(boot_page_array_ready); };
    assert(page_iommu_table_wf(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr)) by { reveal(page_iommu_table_wf); reveal(boot_page_array_ready); };
}

pub(super) proof fn boot_memory_management_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.memory_management_inv(),
{
    boot_memory_management_inv_eof_allocator_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_allocator_free_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_free_4k(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_free_2m(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_free_1g(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_object_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_mappings(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    prove_boot_container_page_owner_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages);
    prove_boot_iommu_table_pages_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool);
    assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { reveal(process_iommu_table_match); };
    assert(pagetable_no_huge_leaf_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp)) by { reveal(process_emptied_tables_wf); };
    prove_boot_process_kernel_pages_owner_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool);
    prove_boot_page_object_owner_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool);
    prove_boot_container_process_allocator_quota_4k_wf(krnl, layout);
    prove_boot_container_process_allocator_quota_2m_wf(krnl, layout);
    prove_boot_container_process_allocator_quota_1g_wf(krnl, layout);
    assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
}

pub(super) proof fn boot_process_management_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.process_management_inv(),
{
    assert(container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)) by {
        reveal(container_root_wf);
        reveal(container_children_parent_wf);
        reveal(containers_linkedlist_wf);
        reveal(container_children_depth_wf);
        reveal(container_subtree_set_wf);
        reveal(container_uppertree_seq_wf);
        reveal(container_subtree_set_exclusive);
    };
    assert(container_process_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by {
        reveal(process_root_wf);
        reveal(process_children_parent_wf);
        reveal(process_linkedlist_wf);
        reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_subtree_set_exclusive);
        reveal(per_container_process_tree_wf);
    };
    assert(process_kill_mark_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_state_lock_wf(krnl.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr)) by { reveal(container_cpu_wf); };
    assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
    assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); };
    assert(container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(krnl.ctn_mp, krnl.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(krnl.ctn_mp, krnl.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(krnl.ctn_mp, krnl.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    prove_boot_container_thread_scheduler_wf(krnl, layout, scheduler_node_addr);
    assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(container_thread_wf); };
    assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { reveal(process_cpu_wf); };
    prove_boot_process_thread_wf(krnl, layout, process_node_addr);
    assert(process_emptied_threads_wf(krnl.prc_mp, krnl.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_cpu_wf); };
    assert(thread_dangling_chain_end_wf(krnl.thr_mp)) by { reveal(thread_dangling_chain_end_wf); };
}

pub(super) proof fn boot_kernel_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_hw_cr3_pcid_ready(cpu_hw_cr3_pcid, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
        krnl.subsystems_inv(),
        krnl.memory_management_inv(),
        krnl.process_management_inv(),
    ensures
        krnl.inv(),
{
    assert(iommu_root_table_process_wf(krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(krnl.irt.view(), krnl.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(krnl.iommu_tlb, krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes);
        reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.pt_lower.view(), krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}

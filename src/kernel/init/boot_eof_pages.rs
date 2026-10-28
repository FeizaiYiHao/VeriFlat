use vstd::prelude::*;

verus! {
use crate::*;
use super::*;

pub(super) proof fn boot_memory_management_inv_eof_container_pages(
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
    ensures container_pages_wf(krnl.pg_arr, krnl.ctn_mp),
{
    hide(Seq::no_duplicates);
    reveal(container_pages_wf); reveal(boot_page_array_ready);
    page_ptr_2m_valid_imply_page_index_2m_valid(layout.root_container); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip();
}

pub(super) proof fn boot_memory_management_inv_eof_process_pages(
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
    ensures process_pages_wf(krnl.pg_arr, krnl.prc_mp),
{
    hide(Seq::no_duplicates);
    reveal(process_pages_wf); reveal(boot_page_array_ready);
}

pub(super) proof fn boot_memory_management_inv_eof_pagetable_pages(
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
    ensures pagetable_pages_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
{
    hide(Seq::no_duplicates);
    reveal(pagetable_pages_wf); reveal(boot_page_array_ready); reveal(PageTableC::table_pages_wf);
}

pub(super) proof fn boot_memory_management_inv_eof_thread_pages(
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
    ensures thread_pages_wf(krnl.thr_mp, krnl.pg_arr),
{
    hide(Seq::no_duplicates);
    reveal(thread_pages_wf); reveal(boot_page_array_ready);
}

pub(super) proof fn boot_memory_management_inv_eof_scheduler_pages(
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
    ensures scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr),
{
    hide(Seq::no_duplicates);
    reveal(scheduler_pages_wf); reveal(boot_page_array_ready);
}

pub(super) proof fn boot_memory_management_inv_eof_cpu_set_pages(
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
    ensures cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr),
{
    hide(Seq::no_duplicates);
    reveal(cpu_set_pages_wf); reveal(boot_page_array_ready);
}

pub(super) proof fn boot_memory_management_inv_eof_pcid_allocator_pages(
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
    ensures pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp),
{
    hide(Seq::no_duplicates);
    reveal(pcid_allocator_pages_wf); reveal(boot_page_array_ready);
}

pub(super) proof fn boot_memory_management_inv_eof_thread_staged_pages(
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
    ensures thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr),
{
    hide(Seq::no_duplicates);
    reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf); reveal(boot_page_array_ready);
}

pub(super) proof fn boot_memory_management_inv_eof_endpoint_pages(
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
    ensures endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr),
{
    hide(Seq::no_duplicates);
    reveal(endpoint_pages_wf); reveal(boot_page_array_ready);
}
}

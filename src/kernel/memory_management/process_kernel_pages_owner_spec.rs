use vstd::prelude::*;
use crate::*;

verus! {
    /// A page that makes up a process: its object page, a page-table or IOMMU-table root page, or one of their table pages.
    pub open spec fn page_state_is_process_kernel_page(state: PageState) -> bool {
        &&& state is Allocated4k
        &&& state->Allocated4k_state is AsProcess || state->Allocated4k_state is AsPageTableRoot || state->Allocated4k_state is PageTable
    }

    /// Pages that make up a process belong to the process's container.
    #[verifier::opaque]
    pub open spec fn process_kernel_pages_owner_wf(page_array: PageLockedArray, process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, iommu_table_map: IommuTableLockedMap) -> bool {
        forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = page_array.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                let state = page.state->Allocated4k_state;
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }) ==> page.owning_container == process_map.spec_index(ptr).view_rodata().view().owning_container
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }) ==> page.owning_container == process_map.spec_index(pagetable_map.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }) ==> page.owning_container == process_map.spec_index(iommu_table_map.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
                &&& page.state is Allocated4k && state is PageTable && state->PageTable_table_type == PT_TYPE ==> page.owning_container == process_map.spec_index(pagetable_map.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
                &&& page.state is Allocated4k && state is PageTable && state->PageTable_table_type == IOMMU_TYPE ==> page.owning_container == process_map.spec_index(iommu_table_map.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            }
    }

    pub proof fn process_kernel_pages_owner_wf_at(page_array: PageLockedArray, process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, iommu_table_map: IommuTableLockedMap, page_index: PageIndex)
        requires
            process_kernel_pages_owner_wf(page_array, process_map, pagetable_map, iommu_table_map),
            index_valid(NUM_PAGES, page_index),
        ensures
            ({
                let page = page_array.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                let state = page.state->Allocated4k_state;
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }) ==> page.owning_container == process_map.spec_index(ptr).view_rodata().view().owning_container
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }) ==> page.owning_container == process_map.spec_index(pagetable_map.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }) ==> page.owning_container == process_map.spec_index(iommu_table_map.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
                &&& page.state is Allocated4k && state is PageTable && state->PageTable_table_type == PT_TYPE ==> page.owning_container == process_map.spec_index(pagetable_map.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
                &&& page.state is Allocated4k && state is PageTable && state->PageTable_table_type == IOMMU_TYPE ==> page.owning_container == process_map.spec_index(iommu_table_map.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            }),
    { reveal(process_kernel_pages_owner_wf); }
}

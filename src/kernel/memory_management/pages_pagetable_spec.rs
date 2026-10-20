use vstd::prelude::*;
use crate::*;

verus! {
    pub open spec fn pagetable_root_page_forward_wf(pagetable_map: PageTableLockedMap, page_array: PageLockedArray) -> bool {
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            #![trigger pagetable_map.dom().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && page_array.spec_index(page_index).view().view().state == (PageState::Allocated4k{state: Allocated4KPageState::AsPageTableRoot{table_type: PT_TYPE}})
                ==> pagetable_map.dom().contains(page_index2page_ptr(page_index))
    }

    pub open spec fn pagetable_closure_page_forward_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            #![trigger pagetable_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)]
            #![trigger pagetable_c(pagetable_map, pt_lower, page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).page_closure().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::PageTable { .. }})
                && page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE
                ==> pagetable_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)
                && pagetable_c(pagetable_map, pt_lower, page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).page_closure().contains(page_index2page_ptr(page_index))
    }

    pub open spec fn pagetable_root_page_backward_wf(pagetable_map: PageTableLockedMap, page_array: PageLockedArray) -> bool {
        forall|pt_ptr:RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt_ptr)]
            pagetable_map.dom().contains(pt_ptr)
                ==> page_ptr_valid(pt_ptr)
                && page_array.spec_index(page_ptr2page_index(pt_ptr)).view().view().state is Allocated4k
                && page_array.spec_index(page_ptr2page_index(pt_ptr)).view().view().state->Allocated4k_state is AsPageTableRoot
                && page_array.spec_index(page_ptr2page_index(pt_ptr)).view().view().state->Allocated4k_state->AsPageTableRoot_table_type == PT_TYPE
    }

    pub open spec fn pagetable_closure_page_backward_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        forall|pt_ptr:RwLockPageTableRoot, pt_p_ptr:PagePtr|
            #![trigger pagetable_c(pagetable_map, pt_lower, pt_ptr).page_closure().contains(pt_p_ptr)]
            pagetable_map.dom().contains(pt_ptr) && pagetable_c(pagetable_map, pt_lower, pt_ptr).page_closure().contains(pt_p_ptr)
                ==> page_ptr_valid(pt_p_ptr)
                && page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state is Allocated4k
                && page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state->Allocated4k_state is PageTable
                && page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == pt_ptr
                && page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE
    }

    /// CPU page tables (`pt_mp`): root pages and table-walk pages are tagged with the table type and the owning root.
    // Proof dependency (confirmed for free-page state updates): page_array_wf.
    #[verifier::opaque]
    pub open spec fn pagetable_pages_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        &&& pagetable_root_page_forward_wf(pagetable_map, page_array)
        &&& pagetable_closure_page_forward_wf(pagetable_map, pt_lower, page_array)
        &&& pagetable_root_page_backward_wf(pagetable_map, page_array)
        &&& pagetable_closure_page_backward_wf(pagetable_map, pt_lower, page_array)
    }

    pub proof fn pagetable_pages_wf_closure_entry_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, pagetable_ptr: RwLockPageTableRoot, page_ptr: PagePtr)
        requires
            pagetable_pages_wf(pagetable_map, pt_lower, page_array),
            pagetable_map.dom().contains(pagetable_ptr),
            pagetable_c(pagetable_map, pt_lower, pagetable_ptr).page_closure().contains(page_ptr),
        ensures
            page_ptr_valid(page_ptr),
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Allocated4k,
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Allocated4k_state is PageTable,
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == pagetable_ptr,
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE,
    { reveal(pagetable_pages_wf); }

    pub proof fn pagetable_pages_wf_root_entry_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_pages_wf(pagetable_map, pt_lower, page_array),
            pagetable_map.dom().contains(pagetable_ptr),
        ensures
            page_ptr_valid(pagetable_ptr),
            page_array.spec_index(page_ptr2page_index(pagetable_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }),
    { reveal(pagetable_pages_wf); }

    /// IOMMU tables (`it_mp`): root pages and table-walk pages are tagged with the table type and the owning root.
    // Proof dependency (confirmed for free-page state updates): page_array_wf.
    #[verifier::opaque]
    pub open spec fn iommu_table_pages_wf(iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray) -> bool {
        &&& forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            #![trigger iommu_table_map.dom().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && page_array.spec_index(page_index).view().view().state == (PageState::Allocated4k{state: Allocated4KPageState::AsPageTableRoot{table_type: IOMMU_TYPE}})
                ==> iommu_table_map.dom().contains(page_index2page_ptr(page_index))
        &&& forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            #![trigger iommu_table_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)]
            #![trigger iommu_table_map.spec_index(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::PageTable { .. }})
                && page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE
                ==> iommu_table_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)
                && iommu_table_map.spec_index(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))
        &&& forall|it_ptr:RwLockPageTableRoot|
            #![trigger iommu_table_map.dom().contains(it_ptr)]
            iommu_table_map.dom().contains(it_ptr)
                ==> page_ptr_valid(it_ptr)
                && page_array.spec_index(page_ptr2page_index(it_ptr)).view().view().state is Allocated4k
                && page_array.spec_index(page_ptr2page_index(it_ptr)).view().view().state->Allocated4k_state is AsPageTableRoot
                && page_array.spec_index(page_ptr2page_index(it_ptr)).view().view().state->Allocated4k_state->AsPageTableRoot_table_type == IOMMU_TYPE
        &&& forall|it_ptr:RwLockPageTableRoot, it_p_ptr:PagePtr|
            #![trigger iommu_table_map.spec_index(it_ptr).view().page_closure().contains(it_p_ptr)]
            iommu_table_map.dom().contains(it_ptr) && iommu_table_map.spec_index(it_ptr).view().page_closure().contains(it_p_ptr)
                ==> page_ptr_valid(it_p_ptr)
                && page_array.spec_index(page_ptr2page_index(it_p_ptr)).view().view().state is Allocated4k
                && page_array.spec_index(page_ptr2page_index(it_p_ptr)).view().view().state->Allocated4k_state is PageTable
                && page_array.spec_index(page_ptr2page_index(it_p_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == it_ptr
                && page_array.spec_index(page_ptr2page_index(it_p_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE
    }

    pub proof fn iommu_table_pages_wf_closure_entry_at(iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray, iommu_table_ptr: RwLockPageTableRoot, page_ptr: PagePtr)
        requires
            iommu_table_pages_wf(iommu_table_map, page_array),
            iommu_table_map.dom().contains(iommu_table_ptr),
            iommu_table_map.spec_index(iommu_table_ptr).view().page_closure().contains(page_ptr),
        ensures
            page_ptr_valid(page_ptr),
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Allocated4k,
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Allocated4k_state is PageTable,
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == iommu_table_ptr,
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE,
    { reveal(iommu_table_pages_wf); }

    pub proof fn iommu_table_pages_wf_root_entry_at(iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray, iommu_table_ptr: RwLockPageTableRoot)
        requires
            iommu_table_pages_wf(iommu_table_map, page_array),
            iommu_table_map.dom().contains(iommu_table_ptr),
        ensures
            page_ptr_valid(iommu_table_ptr),
            page_array.spec_index(page_ptr2page_index(iommu_table_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }),
    { reveal(iommu_table_pages_wf); }
}

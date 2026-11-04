use vstd::prelude::*;
use crate::*;

verus! {
/// Page -> table: a page in state AsPageTableRoot { PT_TYPE } is a CPU page table root.
pub open spec fn pagetable_root_page_forward_wf(pt_mp: PageTableLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger pt_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } })
            ==>
            pt_mp.dom().contains(page_index2page_ptr(p_i))
}

/// Page -> table: a PT_TYPE page-table page is in the page closure of the root it names.
pub open spec fn pagetable_closure_page_forward_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger pt_mp.dom().contains(pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root)]
        #![trigger whole_pagetable(pt_mp, pt_lower, pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root).page_closure().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::PageTable { .. } })
            && pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE
            ==>
            pt_mp.dom().contains(pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root)
            && whole_pagetable(pt_mp, pt_lower, pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root).page_closure().contains(page_index2page_ptr(p_i))
}

/// Table -> page: every CPU page table root is a valid page in state AsPageTableRoot { PT_TYPE }.
pub open spec fn pagetable_root_page_backward_wf(pt_mp: PageTableLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.dom().contains(pt)]
        pt_mp.dom().contains(pt)
            ==>
            page_ptr_valid(pt)
            && pg_arr.spec_index(page_ptr2page_index(pt)).view().view().state is Allocated4k
            && pg_arr.spec_index(page_ptr2page_index(pt)).view().view().state->Allocated4k_state is AsPageTableRoot
            && pg_arr.spec_index(page_ptr2page_index(pt)).view().view().state->Allocated4k_state->AsPageTableRoot_table_type == PT_TYPE
}

/// Table -> page: every page in a CPU page table's closure is a valid PT_TYPE page-table page naming that root.
pub open spec fn pagetable_closure_page_backward_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    forall|pt: RwLockPageTableRoot, p: PagePtr|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).page_closure().contains(p)]
        pt_mp.dom().contains(pt)
            && whole_pagetable(pt_mp, pt_lower, pt).page_closure().contains(p)
            ==>
            page_ptr_valid(p)
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state is Allocated4k
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state->Allocated4k_state is PageTable
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state->Allocated4k_state->PageTable_pagetable_root == pt
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE
}

/// CPU page tables (`pt_mp`): root pages and table-walk pages are tagged with the table type and the owning root.
// Proof dependency (confirmed for free-page state updates): page_array_wf.
#[verifier::opaque]
pub open spec fn pagetable_pages_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    &&& pagetable_root_page_forward_wf(pt_mp, pg_arr)
    &&& pagetable_closure_page_forward_wf(pt_mp, pt_lower, pg_arr)
    &&& pagetable_root_page_backward_wf(pt_mp, pg_arr)
    &&& pagetable_closure_page_backward_wf(pt_mp, pt_lower, pg_arr)
}

pub proof fn pagetable_pages_wf_closure_page_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pt_ptr: RwLockPageTableRoot, pg_ptr: PagePtr)
    requires
        pagetable_pages_wf(pt_mp, pt_lower, pg_arr),
        pt_mp.dom().contains(pt_ptr),
        whole_pagetable(pt_mp, pt_lower, pt_ptr).page_closure().contains(pg_ptr),
    ensures
        page_ptr_valid(pg_ptr),
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Allocated4k,
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state->Allocated4k_state is PageTable,
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == pt_ptr,
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE,
{ reveal(pagetable_pages_wf); }

pub proof fn pagetable_pages_wf_root_page_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_pages_wf(pt_mp, pt_lower, pg_arr),
        pt_mp.dom().contains(pt_ptr),
    ensures
        page_ptr_valid(pt_ptr),
        pg_arr.spec_index(page_ptr2page_index(pt_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }),
{ reveal(pagetable_pages_wf); }

/// IOMMU tables (`it_mp`): root pages and table-walk pages are tagged with the table type and the owning root.
// Proof dependency (confirmed for free-page state updates): page_array_wf.
#[verifier::opaque]
pub open spec fn iommu_table_pages_wf(it_mp: IommuTableLockedMap, pg_arr: PageLockedArray) -> bool {
    // Page -> table: a page in state AsPageTableRoot { IOMMU_TYPE } is an IOMMU table root.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger it_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
            ==>
            it_mp.dom().contains(page_index2page_ptr(p_i))
    // Page -> table: an IOMMU_TYPE page-table page is in the page closure of the root it names.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger it_mp.dom().contains(pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root)]
        #![trigger it_mp.spec_index(pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::PageTable { .. } })
            && pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE
            ==>
            it_mp.dom().contains(pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root)
            && it_mp.spec_index(pg_arr.spec_index(p_i).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(p_i))
    // Table -> page: every IOMMU table root is a valid page in state AsPageTableRoot { IOMMU_TYPE }.
    &&& forall|it: RwLockPageTableRoot|
        #![trigger it_mp.dom().contains(it)]
        it_mp.dom().contains(it)
            ==>
            page_ptr_valid(it)
            && pg_arr.spec_index(page_ptr2page_index(it)).view().view().state is Allocated4k
            && pg_arr.spec_index(page_ptr2page_index(it)).view().view().state->Allocated4k_state is AsPageTableRoot
            && pg_arr.spec_index(page_ptr2page_index(it)).view().view().state->Allocated4k_state->AsPageTableRoot_table_type == IOMMU_TYPE
    // Table -> page: every page in an IOMMU table's closure is a valid IOMMU_TYPE page-table page naming that root.
    &&& forall|it: RwLockPageTableRoot, p: PagePtr|
        #![trigger it_mp.spec_index(it).view().page_closure().contains(p)]
        it_mp.dom().contains(it)
            && it_mp.spec_index(it).view().page_closure().contains(p)
            ==>
            page_ptr_valid(p)
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state is Allocated4k
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state->Allocated4k_state is PageTable
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state->Allocated4k_state->PageTable_pagetable_root == it
            && pg_arr.spec_index(page_ptr2page_index(p)).view().view().state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE
}

pub proof fn iommu_table_pages_wf_closure_page_at(it_mp: IommuTableLockedMap, pg_arr: PageLockedArray, it_ptr: RwLockPageTableRoot, pg_ptr: PagePtr)
    requires
        iommu_table_pages_wf(it_mp, pg_arr),
        it_mp.dom().contains(it_ptr),
        it_mp.spec_index(it_ptr).view().page_closure().contains(pg_ptr),
    ensures
        page_ptr_valid(pg_ptr),
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Allocated4k,
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state->Allocated4k_state is PageTable,
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == it_ptr,
        pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE,
{ reveal(iommu_table_pages_wf); }

pub proof fn iommu_table_pages_wf_root_page_at(it_mp: IommuTableLockedMap, pg_arr: PageLockedArray, it_ptr: RwLockPageTableRoot)
    requires
        iommu_table_pages_wf(it_mp, pg_arr),
        it_mp.dom().contains(it_ptr),
    ensures
        page_ptr_valid(it_ptr),
        pg_arr.spec_index(page_ptr2page_index(it_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }),
{ reveal(iommu_table_pages_wf); }
}

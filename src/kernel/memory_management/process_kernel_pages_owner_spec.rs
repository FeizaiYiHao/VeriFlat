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
pub open spec fn process_object_pages_owner_wf(prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, it_mp: IommuTableLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().owning_container]
        index_valid(NUM_PAGES, p_i) ==> {
            let page = pg_arr.spec_index(p_i).view().view();
            let pg_ptr = page_index2page_ptr(p_i);
            let alloc_state = page.state->Allocated4k_state;
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
                ==> page.owning_container == prc_mp.spec_index(pg_ptr).view_rodata().view().owning_container
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } })
                ==> page.owning_container == prc_mp.spec_index(pt_mp.spec_index(pg_ptr).view().proc_ptr).view_rodata().view().owning_container
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
                ==> page.owning_container == prc_mp.spec_index(it_mp.spec_index(pg_ptr).view().proc_ptr).view_rodata().view().owning_container
            &&& page.state is Allocated4k
                && alloc_state is PageTable
                && alloc_state->PageTable_table_type == PT_TYPE
                ==> page.owning_container == prc_mp.spec_index(pt_mp.spec_index(alloc_state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            &&& page.state is Allocated4k
                && alloc_state is PageTable
                && alloc_state->PageTable_table_type == IOMMU_TYPE
                ==> page.owning_container == prc_mp.spec_index(it_mp.spec_index(alloc_state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
        }
}

pub proof fn process_object_pages_owner_wf_at(prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, it_mp: IommuTableLockedMap, pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        process_object_pages_owner_wf(prc_mp, pt_mp, it_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let pg_ptr = page_index2page_ptr(pg_idx);
            let alloc_state = page.state->Allocated4k_state;
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
                ==> page.owning_container == prc_mp.spec_index(pg_ptr).view_rodata().view().owning_container
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } })
                ==> page.owning_container == prc_mp.spec_index(pt_mp.spec_index(pg_ptr).view().proc_ptr).view_rodata().view().owning_container
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
                ==> page.owning_container == prc_mp.spec_index(it_mp.spec_index(pg_ptr).view().proc_ptr).view_rodata().view().owning_container
            &&& page.state is Allocated4k
                && alloc_state is PageTable
                && alloc_state->PageTable_table_type == PT_TYPE
                ==> page.owning_container == prc_mp.spec_index(pt_mp.spec_index(alloc_state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            &&& page.state is Allocated4k
                && alloc_state is PageTable
                && alloc_state->PageTable_table_type == IOMMU_TYPE
                ==> page.owning_container == prc_mp.spec_index(it_mp.spec_index(alloc_state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
        }),
{ reveal(process_object_pages_owner_wf); }
}

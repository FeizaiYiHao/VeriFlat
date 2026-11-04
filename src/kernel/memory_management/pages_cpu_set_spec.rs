use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn cpu_set_pages_wf(cpu_set_map: CpuSetLockedMap, page_array: PageLockedArray) -> bool {
    // Page -> cpu_set.
    &&& forall|pg_idx: PageIndex|
        #![trigger page_array.spec_index(pg_idx).view().view().state]
        #![trigger cpu_set_map.dom().contains(page_index2page_ptr(pg_idx))]
        index_valid(NUM_PAGES, pg_idx) && (page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet, }) ==> cpu_set_map.dom().contains(page_index2page_ptr(pg_idx))
    // CpuSet -> page.
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr| #![trigger cpu_set_map.dom().contains(cpu_set_ptr)] #![trigger page_array.spec_index(page_ptr2page_index(cpu_set_ptr)).view().view().state]
        cpu_set_map.dom().contains(cpu_set_ptr) ==> page_ptr_valid(cpu_set_ptr) && (page_array.spec_index(page_ptr2page_index(cpu_set_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet, })
}

pub proof fn cpu_set_pages_wf_at(cpu_set_map: CpuSetLockedMap, page_array: PageLockedArray, cpu_set_ptr: RwLockCpuSetPtr)
    requires cpu_set_pages_wf(cpu_set_map, page_array)
    ensures
        cpu_set_map.dom().contains(cpu_set_ptr) ==> page_ptr_valid(cpu_set_ptr) && (page_array.spec_index(page_ptr2page_index(cpu_set_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet, }),
{ reveal(cpu_set_pages_wf); }
}

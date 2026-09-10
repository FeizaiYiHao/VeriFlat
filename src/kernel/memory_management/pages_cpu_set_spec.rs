use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn cpu_set_pages_wf(
    cpu_set_map: CpuSetLockedMap,
    page_array: PageLockedArray,
) -> bool {
    // Page -> cpu_set.
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        #![trigger cpu_set_map.dom().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index)
        && (page_array.spec_index(page_index).view().view().state
            matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet, })
        ==> cpu_set_map.dom().contains(page_index2page_ptr(page_index))
    // CpuSet -> page.
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_map.dom().contains(cpu_set_ptr)]
        #![trigger page_array.spec_index(page_ptr2page_index(cpu_set_ptr))
            .view().view().state]
        cpu_set_map.dom().contains(cpu_set_ptr)
        ==> page_ptr_valid(cpu_set_ptr)
            && (page_array.spec_index(page_ptr2page_index(cpu_set_ptr))
                .view().view().state
                matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet, })
}
}

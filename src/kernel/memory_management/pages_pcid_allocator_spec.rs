use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn pcid_allocator_pages_wf(page_array: PageLockedArray, pcid_allocator_map: PcidAllocatorLockedMap) -> bool {
    // Page -> PCID allocator.
    &&& forall|pg_idx: PageIndex|
        #![trigger page_array.spec_index(pg_idx).view().view().state]
        index_valid(NUM_PAGES, pg_idx) && (page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
            ==> pcid_allocator_map.dom().contains(page_index2page_ptr(pg_idx))
    // PCID allocator -> page.
    &&& forall|allc_ptr: RwLockPcidAllocatorPtr|
        #![trigger pcid_allocator_map.dom().contains(allc_ptr)]
        pcid_allocator_map.dom().contains(allc_ptr)
            ==> page_ptr_valid(allc_ptr) && (page_array.spec_index(page_ptr2page_index(allc_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
}

pub proof fn pcid_allocator_pages_wf_at(page_array: PageLockedArray, pcid_allocator_map: PcidAllocatorLockedMap, allc_ptr: RwLockPcidAllocatorPtr)
    requires pcid_allocator_pages_wf(page_array, pcid_allocator_map)
    ensures
        pcid_allocator_map.dom().contains(allc_ptr)
            ==> page_ptr_valid(allc_ptr) && (page_array.spec_index(page_ptr2page_index(allc_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
{ reveal(pcid_allocator_pages_wf); }
}

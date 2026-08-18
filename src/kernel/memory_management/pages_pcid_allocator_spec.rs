use vstd::prelude::*;
use crate::*;

verus! {

#[verifier::opaque]
pub open spec fn pcid_allocator_pages_wf(
    page_array: PageLockedArray,
    pcid_allocator_map: PcidAllocatorLockedMap,
) -> bool {
    // Page -> PCID allocator.
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index)
        && (page_array.spec_index(page_index).view().view().state
            matches PageState::Allocated2m {
                state: Allocated2MPageState::AsPcidAllocator,
            })
        ==> pcid_allocator_map.dom().contains(page_index2page_ptr(page_index))
    // PCID allocator -> page.
    &&& forall|allocator_ptr: RwLockPcidAllocatorPtr|
        #![trigger pcid_allocator_map.dom().contains(allocator_ptr)]
        pcid_allocator_map.dom().contains(allocator_ptr)
        ==>
        page_ptr_valid(allocator_ptr)
        && (page_array.spec_index(page_ptr2page_index(allocator_ptr))
            .view().view().state
            matches PageState::Allocated2m {
                state: Allocated2MPageState::AsPcidAllocator,
            })
}

}

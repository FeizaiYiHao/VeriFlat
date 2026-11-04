use vstd::prelude::*;
use crate::*;

verus! {
/// PCID allocators and AsPcidAllocator pages agree in both directions.
#[verifier::opaque]
pub open spec fn pcid_allocator_pages_wf(pcid_allc_mp: PcidAllocatorLockedMap, pg_arr: PageLockedArray) -> bool {
    // Page -> PCID allocator.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
            ==>
            pcid_allc_mp.dom().contains(page_index2page_ptr(p_i))
    // PCID allocator -> page.
    &&& forall|pa: RwLockPcidAllocatorPtr|
        #![trigger pcid_allc_mp.dom().contains(pa)]
        pcid_allc_mp.dom().contains(pa)
            ==>
            page_ptr_valid(pa)
            && (pg_arr.spec_index(page_ptr2page_index(pa)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
}

pub proof fn pcid_allocator_pages_wf_at(pcid_allc_mp: PcidAllocatorLockedMap, pg_arr: PageLockedArray, pcid_allc_ptr: RwLockPcidAllocatorPtr)
    requires pcid_allocator_pages_wf(pcid_allc_mp, pg_arr)
    ensures
        pcid_allc_mp.dom().contains(pcid_allc_ptr)
            ==> page_ptr_valid(pcid_allc_ptr) && (pg_arr.spec_index(page_ptr2page_index(pcid_allc_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
{ reveal(pcid_allocator_pages_wf); }
}

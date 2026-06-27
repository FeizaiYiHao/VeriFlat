use vstd::prelude::*;
use crate::*;

verus! {

// ---------- 4k ----------

/// Bi-directional invariant for `Process.temp_alloc_cache_4k` against
/// `Page.state == Owned4k{process_ptr}`.
///
/// Forward: page in Owned4k{p} ==> process p has this page in temp_alloc_cache_4k.
/// Backward: page in p.temp_alloc_cache_4k ==> page is Owned4k{p} and valid.
#[verifier::opaque]
pub open spec fn process_staged_pages_4k_wf(
    process_map: ProcessLockedMap,
    page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
        && page_array.spec_index(page_index).view().view().state is Owned4k
        ==>
        {
            let process_ptr = page_array.spec_index(page_index).view().view().state->Owned4k_process_ptr;
            &&&
            process_map.dom().contains(process_ptr)
            &&&
            process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|p_ptr:RwLockProcessPtr, page_ptr:PagePtr|
        #![trigger process_map.spec_index(p_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
        process_map.dom().contains(p_ptr)
        && process_map.spec_index(p_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned4k{process_ptr: p_ptr}
}

// ---------- 2m ----------

#[verifier::opaque]
pub open spec fn process_staged_pages_2m_wf(
    process_map: ProcessLockedMap,
    page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
        && page_array.spec_index(page_index).view().view().state is Owned2m
        ==>
        {
            let process_ptr = page_array.spec_index(page_index).view().view().state->Owned2m_process_ptr;
            &&&
            process_map.dom().contains(process_ptr)
            &&&
            process_map.spec_index(process_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|p_ptr:RwLockProcessPtr, page_ptr:PagePtr|
        #![trigger process_map.spec_index(p_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
        process_map.dom().contains(p_ptr)
        && process_map.spec_index(p_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned2m{process_ptr: p_ptr}
}

// ---------- 1g ----------

#[verifier::opaque]
pub open spec fn process_staged_pages_1g_wf(
    process_map: ProcessLockedMap,
    page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
        && page_array.spec_index(page_index).view().view().state is Owned1g
        ==>
        {
            let process_ptr = page_array.spec_index(page_index).view().view().state->Owned1g_process_ptr;
            &&&
            process_map.dom().contains(process_ptr)
            &&&
            process_map.spec_index(process_ptr).view().temp_alloc_cache_1g.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|p_ptr:RwLockProcessPtr, page_ptr:PagePtr|
        #![trigger process_map.spec_index(p_ptr).view().temp_alloc_cache_1g.view().contains(page_ptr)]
        process_map.dom().contains(p_ptr)
        && process_map.spec_index(p_ptr).view().temp_alloc_cache_1g.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned1g{process_ptr: p_ptr}
}

// ---------- Combined ----------

#[verifier::opaque]
pub open spec fn process_staged_pages_wf(
    process_map: ProcessLockedMap,
    page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
) -> bool {
    &&& process_staged_pages_4k_wf(process_map, page_array)
    &&& process_staged_pages_2m_wf(process_map, page_array)
    &&& process_staged_pages_1g_wf(process_map, page_array)
}

}

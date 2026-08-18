use vstd::prelude::*;
use crate::*;

verus! {

// ---------- 4k ----------

/// Bi-directional invariant for `Thread.temp_alloc_cache_4k` against
/// `Page.state == Owned4k{thread_ptr}`.
///
/// Forward: page in Owned4k{t} ==> thread t has this page in temp_alloc_cache_4k.
/// Backward: page in t.temp_alloc_cache_4k ==> page is Owned4k{t} and valid.
#[verifier::opaque]
pub open spec fn thread_staged_pages_4k_wf(
    thread_map: ThreadLockedMap,
    page_array: PageLockedArray,
) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index)]
        index_valid(NUM_PAGES, page_index)
        && page_array.spec_index(page_index).view().view().state is Owned4k
        ==>
        {
            let thread_ptr = page_array.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
            &&&
            thread_map.dom().contains(thread_ptr)
            &&&
            thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|p_ptr:RwLockThreadPtr, page_ptr:PagePtr|
        #![trigger thread_map.dom().contains(p_ptr), page_ptr2page_index(page_ptr)]
        thread_map.dom().contains(p_ptr)
        && thread_map.spec_index(p_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned4k{thread_ptr: p_ptr}
}

// ---------- 2m ----------

#[verifier::opaque]
pub open spec fn thread_staged_pages_2m_wf(
    thread_map: ThreadLockedMap,
    page_array: PageLockedArray,
) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger index_valid(NUM_PAGES, page_index)]
        index_valid(NUM_PAGES, page_index)
        && page_array.spec_index(page_index).view().view().state is Owned2m
        ==>
        {
            let thread_ptr = page_array.spec_index(page_index).view().view().state->Owned2m_thread_ptr;
            &&&
            thread_map.dom().contains(thread_ptr)
            &&&
            thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|p_ptr:RwLockThreadPtr, page_ptr:PagePtr|
        #![trigger thread_map.dom().contains(p_ptr), page_ptr_valid(page_ptr)]
        thread_map.dom().contains(p_ptr)
        && thread_map.spec_index(p_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned2m{thread_ptr: p_ptr}
}

// ---------- 1g ----------

#[verifier::opaque]
pub open spec fn thread_staged_pages_1g_wf(
    thread_map: ThreadLockedMap,
    page_array: PageLockedArray,
) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger index_valid(NUM_PAGES, page_index)]
        index_valid(NUM_PAGES, page_index)
        && page_array.spec_index(page_index).view().view().state is Owned1g
        ==>
        {
            let thread_ptr = page_array.spec_index(page_index).view().view().state->Owned1g_thread_ptr;
            &&&
            thread_map.dom().contains(thread_ptr)
            &&&
            thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|p_ptr:RwLockThreadPtr, page_ptr:PagePtr|
        #![trigger thread_map.dom().contains(p_ptr), page_ptr_valid(page_ptr)]
        thread_map.dom().contains(p_ptr)
        && thread_map.spec_index(p_ptr).view().temp_alloc_cache_1g.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned1g{thread_ptr: p_ptr}
}

// ---------- Combined ----------

pub open spec fn thread_staged_pages_wf(
    thread_map: ThreadLockedMap,
    page_array: PageLockedArray,
) -> bool {
    &&& thread_staged_pages_4k_wf(thread_map, page_array)
    &&& thread_staged_pages_2m_wf(thread_map, page_array)
    &&& thread_staged_pages_1g_wf(thread_map, page_array)
}

}

use vstd::prelude::*;
use crate::*;

verus! {
// ---------- 4k ----------

/// Bi-directional invariant for `Thread.temp_alloc_cache_4k` against
/// `Page.state == Owned4k{thrd_ptr}`.
///
/// Forward: page in Owned4k{t} ==> thread t has this page in temp_alloc_cache_4k.
/// Backward: page in t.temp_alloc_cache_4k ==> page is Owned4k{t} and valid.
#[verifier::opaque]
pub open spec fn thread_staged_pages_4k_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
    &&& forall|pg_idx:PageIndex|
        #![trigger index_valid(NUM_PAGES, pg_idx)]
        index_valid(NUM_PAGES, pg_idx) && page_array.spec_index(pg_idx).view().view().state is Owned4k ==> {
            let thrd_ptr = page_array.spec_index(pg_idx).view().view().state->Owned4k_thread_ptr;
            &&& thread_map.dom().contains(thrd_ptr)
            &&& thread_map.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(pg_idx))
        }
    &&& forall|p_ptr:RwLockThreadPtr| #![trigger thread_map.dom().contains(p_ptr)]
        thread_map.dom().contains(p_ptr) ==> forall|pg_ptr:PagePtr| #![trigger thread_map.spec_index(p_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)]
            thread_map.spec_index(p_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)
                ==> page_ptr_valid(pg_ptr) && page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Owned4k{thread_ptr: p_ptr}
}

/// A page staged in thread `thrd_ptr`'s 4k temp cache is a valid page owned by that thread.
pub proof fn thread_staged_pages_4k_wf_at(thread_map: ThreadLockedMap, page_array: PageLockedArray, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr)
    requires
        thread_staged_pages_4k_wf(thread_map, page_array),
        thread_map.dom().contains(thrd_ptr),
    ensures
        thread_map.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)
            ==> page_ptr_valid(pg_ptr) && page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: thrd_ptr }),
{ reveal(thread_staged_pages_4k_wf); }

// ---------- 2m ----------

pub open spec fn thread_staged_pages_2m_forward_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
    forall|pg_idx:PageIndex|
        #![trigger page_array.spec_index(pg_idx).view().view().state]
        index_valid(NUM_PAGES, pg_idx) && page_array.spec_index(pg_idx).view().view().state is Owned2m ==> {
            let thrd_ptr = page_array.spec_index(pg_idx).view().view().state->Owned2m_thread_ptr;
            &&& thread_map.dom().contains(thrd_ptr)
            &&& thread_map.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(pg_idx))
        }
}

pub open spec fn thread_staged_pages_2m_backward_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
    forall|p_ptr:RwLockThreadPtr| #![trigger thread_map.dom().contains(p_ptr)]
        thread_map.dom().contains(p_ptr) ==> forall|pg_ptr:PagePtr| #![trigger thread_map.spec_index(p_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr)]
            thread_map.spec_index(p_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr)
                ==> page_ptr_valid(pg_ptr) && page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Owned2m{thread_ptr: p_ptr}
}

#[verifier::opaque]
pub open spec fn thread_staged_pages_2m_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
    &&& thread_staged_pages_2m_forward_wf(thread_map, page_array)
    &&& thread_staged_pages_2m_backward_wf(thread_map, page_array)
}

/// A page staged in thread `thrd_ptr`'s 2m temp cache is a valid page owned by that thread.
pub proof fn thread_staged_pages_2m_wf_at(thread_map: ThreadLockedMap, page_array: PageLockedArray, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr)
    requires
        thread_staged_pages_2m_wf(thread_map, page_array),
        thread_map.dom().contains(thrd_ptr),
    ensures
        thread_map.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr)
            ==> page_ptr_valid(pg_ptr) && page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
{ reveal(thread_staged_pages_2m_wf); }

// ---------- 1g ----------

#[verifier::opaque]
pub open spec fn thread_staged_pages_1g_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
    &&& forall|pg_idx:PageIndex|
        #![trigger index_valid(NUM_PAGES, pg_idx)]
        index_valid(NUM_PAGES, pg_idx) && page_array.spec_index(pg_idx).view().view().state is Owned1g ==> {
            let thrd_ptr = page_array.spec_index(pg_idx).view().view().state->Owned1g_thread_ptr;
            &&& thread_map.dom().contains(thrd_ptr)
            &&& thread_map.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(page_index2page_ptr(pg_idx))
        }
    &&& forall|p_ptr:RwLockThreadPtr| #![trigger thread_map.dom().contains(p_ptr)]
        thread_map.dom().contains(p_ptr) ==> forall|pg_ptr:PagePtr| #![trigger thread_map.spec_index(p_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr)]
            thread_map.spec_index(p_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr)
                ==> page_ptr_valid(pg_ptr) && page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Owned1g{thread_ptr: p_ptr}
}

// ---------- Combined ----------

pub open spec fn thread_staged_pages_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
    &&& thread_staged_pages_4k_wf(thread_map, page_array)
    &&& thread_staged_pages_2m_wf(thread_map, page_array)
    &&& thread_staged_pages_1g_wf(thread_map, page_array)
}
}

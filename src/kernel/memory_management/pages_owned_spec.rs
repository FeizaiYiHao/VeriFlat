use vstd::prelude::*;
use crate::*;

verus! {

// ---------- 4k ----------

/// Bi-directional invariant for `Thread.direct_container_page_cache_4k`
/// against `Page.state == Owned4k{thread_ptr}`.
///
/// - Forward: every page index whose state is `Owned4k{t}` corresponds to
///   a thread `t` that records this page in its
///   `direct_container_page_cache_4k`.
/// - Backward: every page in any thread's
///   `direct_container_page_cache_4k` is in `Owned4k` state with the
///   matching `thread_ptr`.
///
/// Marked `#[verifier::opaque]` so the body is not auto-unfolded; callers
/// who need to reason about it write `reveal(thread_owned_pages_4k_wf);`
/// in a proof block.
#[verifier::opaque]
pub open spec fn thread_owned_pages_4k_wf(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
    &&&
    // Forward: page in Owned4k{t} ==> thread t exists and contains this page.
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
        && page_array.spec_index(page_index).view().view().state is Owned4k
        ==>
        {
            let thread_ptr = page_array.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
            &&&
            thread_map.dom().contains(thread_ptr)
            &&&
            thread_map.spec_index(thread_ptr).view().direct_container_page_cache_4k.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    // Backward: page in t.direct_container_page_cache_4k
    //         ==> page is Owned4k{t}.
    forall|t_ptr:RwLockThreadPtr, page_ptr:PagePtr|
        #![trigger thread_map.spec_index(t_ptr).view().direct_container_page_cache_4k.view().contains(page_ptr)]
        thread_map.dom().contains(t_ptr)
        && thread_map.spec_index(t_ptr).view().direct_container_page_cache_4k.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned4k{thread_ptr: t_ptr}
}

// ---------- 2m ----------

#[verifier::opaque]
pub open spec fn thread_owned_pages_2m_wf(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
        && page_array.spec_index(page_index).view().view().state is Owned2m
        ==>
        {
            let thread_ptr = page_array.spec_index(page_index).view().view().state->Owned2m_thread_ptr;
            &&&
            thread_map.dom().contains(thread_ptr)
            &&&
            thread_map.spec_index(thread_ptr).view().direct_container_page_cache_2m.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|t_ptr:RwLockThreadPtr, page_ptr:PagePtr|
        #![trigger thread_map.spec_index(t_ptr).view().direct_container_page_cache_2m.view().contains(page_ptr)]
        thread_map.dom().contains(t_ptr)
        && thread_map.spec_index(t_ptr).view().direct_container_page_cache_2m.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned2m{thread_ptr: t_ptr}
}

// ---------- 1g ----------

#[verifier::opaque]
pub open spec fn thread_owned_pages_1g_wf(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
    &&&
    forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
        && page_array.spec_index(page_index).view().view().state is Owned1g
        ==>
        {
            let thread_ptr = page_array.spec_index(page_index).view().view().state->Owned1g_thread_ptr;
            &&&
            thread_map.dom().contains(thread_ptr)
            &&&
            thread_map.spec_index(thread_ptr).view().direct_container_page_cache_1g.view().contains(page_index2page_ptr(page_index))
        }
    &&&
    forall|t_ptr:RwLockThreadPtr, page_ptr:PagePtr|
        #![trigger thread_map.spec_index(t_ptr).view().direct_container_page_cache_1g.view().contains(page_ptr)]
        thread_map.dom().contains(t_ptr)
        && thread_map.spec_index(t_ptr).view().direct_container_page_cache_1g.view().contains(page_ptr)
        ==>
        page_ptr_valid(page_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state ==
            PageState::Owned1g{thread_ptr: t_ptr}
}

// ---------- Combined ----------

#[verifier::opaque]
pub open spec fn thread_owned_pages_wf(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
    &&& thread_owned_pages_4k_wf(thread_map, page_array)
    &&& thread_owned_pages_2m_wf(thread_map, page_array)
    &&& thread_owned_pages_1g_wf(thread_map, page_array)
}

}

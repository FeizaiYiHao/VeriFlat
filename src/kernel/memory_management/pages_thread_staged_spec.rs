use vstd::prelude::*;
use crate::*;

verus! {
// A thread's staged pages (`temp_alloc_cache_4k`, `_2m`, `_1g`) agree with the pages in state Owned4k / Owned2m /
// Owned1g naming that thread.
// Forward: a page in state OwnedXk { thread_ptr: t } is staged in thread t's cache.
// Backward: a page staged in thread t's cache is a valid page in state OwnedXk { thread_ptr: t }.

// ---------- 4K ----------

/// 4K pages staged by threads agree with Owned4k pages in both directions.
#[verifier::opaque]
pub open spec fn thread_staged_4k_pages_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& forall|p_i: PageIndex|
        #![trigger index_valid(NUM_PAGES, p_i)]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state is Owned4k
            ==> {
                let thrd_ptr = pg_arr.spec_index(p_i).view().view().state->Owned4k_thread_ptr;
                &&& thrd_mp.dom().contains(thrd_ptr)
                &&& thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(p_i))
            }
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.dom().contains(t)]
        thrd_mp.dom().contains(t)
            ==>
            forall|pg_ptr: PagePtr|
                #![trigger thrd_mp.spec_index(t).view().temp_alloc_cache_4k.view().contains(pg_ptr)]
                thrd_mp.spec_index(t).view().temp_alloc_cache_4k.view().contains(pg_ptr)
                    ==>
                    page_ptr_valid(pg_ptr)
                    && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Owned4k { thread_ptr: t }
}

/// A page staged in thread `thrd_ptr`'s 4K cache is a valid page owned by that thread.
pub proof fn thread_staged_4k_pages_wf_at(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr)
    requires
        thread_staged_4k_pages_wf(thrd_mp, pg_arr),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)
            ==> page_ptr_valid(pg_ptr) && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: thrd_ptr }),
{ reveal(thread_staged_4k_pages_wf); }

// ---------- 2M ----------

/// Page -> thread: a page in state Owned2m is staged in its thread's 2M cache.
pub open spec fn thread_staged_2m_pages_forward_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state is Owned2m
            ==> {
                let thrd_ptr = pg_arr.spec_index(p_i).view().view().state->Owned2m_thread_ptr;
                &&& thrd_mp.dom().contains(thrd_ptr)
                &&& thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(p_i))
            }
}

/// Thread -> page: a page staged in a thread's 2M cache is a valid page in state Owned2m naming that thread.
pub open spec fn thread_staged_2m_pages_backward_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.dom().contains(t)]
        thrd_mp.dom().contains(t)
            ==>
            forall|pg_ptr: PagePtr|
                #![trigger thrd_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(pg_ptr)]
                thrd_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(pg_ptr)
                    ==>
                    page_ptr_valid(pg_ptr)
                    && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Owned2m { thread_ptr: t }
}

/// 2M pages staged by threads agree with Owned2m pages in both directions.
#[verifier::opaque]
pub open spec fn thread_staged_2m_pages_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& thread_staged_2m_pages_forward_wf(thrd_mp, pg_arr)
    &&& thread_staged_2m_pages_backward_wf(thrd_mp, pg_arr)
}

/// A page staged in thread `thrd_ptr`'s 2M cache is a valid page owned by that thread.
pub proof fn thread_staged_2m_pages_wf_at(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr)
    requires
        thread_staged_2m_pages_wf(thrd_mp, pg_arr),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr)
            ==> page_ptr_valid(pg_ptr) && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
{ reveal(thread_staged_2m_pages_wf); }

// ---------- 1G ----------

/// 1G pages staged by threads agree with Owned1g pages in both directions.
#[verifier::opaque]
pub open spec fn thread_staged_1g_pages_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& forall|p_i: PageIndex|
        #![trigger index_valid(NUM_PAGES, p_i)]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state is Owned1g
            ==> {
                let thrd_ptr = pg_arr.spec_index(p_i).view().view().state->Owned1g_thread_ptr;
                &&& thrd_mp.dom().contains(thrd_ptr)
                &&& thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(page_index2page_ptr(p_i))
            }
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.dom().contains(t)]
        thrd_mp.dom().contains(t)
            ==>
            forall|pg_ptr: PagePtr|
                #![trigger thrd_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(pg_ptr)]
                thrd_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(pg_ptr)
                    ==>
                    page_ptr_valid(pg_ptr)
                    && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Owned1g { thread_ptr: t }
}

// ---------- Combined ----------

/// Staged 4K, 2M, and 1G pages agree with the Owned pages naming their thread.
pub open spec fn thread_staged_pages_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& thread_staged_4k_pages_wf(thrd_mp, pg_arr)
    &&& thread_staged_2m_pages_wf(thrd_mp, pg_arr)
    &&& thread_staged_1g_pages_wf(thrd_mp, pg_arr)
}
}

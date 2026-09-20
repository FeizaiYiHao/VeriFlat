use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// Framing lemmas for each page-size component of `thread_staged_pages_wf`.
// Hypothesis: same thread domain, the corresponding per-thread
// `temp_alloc_cache_*` unchanged, and every page slot that is old or new
// `Owned*` keeps its state—the only fields each component reads.

// thread_staged_pages_4k_wf: Owned4k <-> thread temp_alloc_cache_4k.
pub proof fn thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(
    old_thread_map: ThreadLockedMap,
    new_thread_map: ThreadLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        thread_staged_pages_4k_wf(old_thread_map, old_page_array),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr).view().temp_alloc_cache_4k]
            new_thread_map.dom().contains(t_ptr)
            ==> new_thread_map.spec_index(t_ptr).view().temp_alloc_cache_4k
                == old_thread_map.spec_index(t_ptr).view().temp_alloc_cache_4k,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state is Owned4k)
                || (new_page_array.spec_index(p_i).view().view().state is Owned4k))
            ==> new_page_array.spec_index(p_i).view().view().state
                == old_page_array.spec_index(p_i).view().view().state,
    ensures
        thread_staged_pages_4k_wf(new_thread_map, new_page_array),
{
    reveal(thread_staged_pages_4k_wf);
}

// thread_staged_pages_2m_wf: Owned2m <-> thread temp_alloc_cache_2m.
pub proof fn thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(
    old_thread_map: ThreadLockedMap,
    new_thread_map: ThreadLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        thread_staged_pages_2m_wf(old_thread_map, old_page_array),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr).view().temp_alloc_cache_2m]
            new_thread_map.dom().contains(t_ptr)
            ==> new_thread_map.spec_index(t_ptr).view().temp_alloc_cache_2m == old_thread_map.spec_index(t_ptr).view().temp_alloc_cache_2m,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state is Owned2m)
                || (new_page_array.spec_index(p_i).view().view().state is Owned2m))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        thread_staged_pages_2m_wf(new_thread_map, new_page_array),
{
    reveal(thread_staged_pages_2m_wf);
}

// thread_staged_pages_1g_wf: Owned1g <-> thread temp_alloc_cache_1g.
pub proof fn thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(
    old_thread_map: ThreadLockedMap,
    new_thread_map: ThreadLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        thread_staged_pages_1g_wf(old_thread_map, old_page_array),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr).view().temp_alloc_cache_1g]
            new_thread_map.dom().contains(t_ptr)
            ==> new_thread_map.spec_index(t_ptr).view().temp_alloc_cache_1g == old_thread_map.spec_index(t_ptr).view().temp_alloc_cache_1g,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state is Owned1g)
                || (new_page_array.spec_index(p_i).view().view().state is Owned1g))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        thread_staged_pages_1g_wf(new_thread_map, new_page_array),
{
    reveal(thread_staged_pages_1g_wf);
}

}

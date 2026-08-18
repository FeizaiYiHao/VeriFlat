use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// Framing lemmas for the 2m/1g halves of `thread_staged_pages_wf`.
// Reusable by any syscall that leaves the 2m/1g staging untouched (e.g. a 4k
// alloc/free). The 4k half genuinely reasons about a 4k stage, so it has NO twin
// here. Hypothesis: same thread dom, per-thread temp_alloc_cache_{2m,1g}
// unchanged, and every Owned{2m,1g} page slot (old or new) keeps its state -- the
// only fields the halves read.

// thread_staged_pages_2m_wf: Owned2m <-> thread temp_alloc_cache_2m.
pub proof fn thread_staged_pages_4k_wf_preserved_for_eq(
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
pub proof fn thread_staged_pages_2m_wf_preserved_for_eq(
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
pub proof fn thread_staged_pages_1g_wf_preserved_for_eq(
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

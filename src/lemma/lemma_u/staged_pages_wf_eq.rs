use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// Framing lemmas for the 2m/1g halves of `process_staged_pages_wf` (each binds
// the Owned2m/Owned1g page-state class to a process's temp_alloc_cache_2m/1g).
// Reusable by any syscall that leaves the 2m/1g staging untouched (e.g. a 4k
// alloc/free). The 4k half genuinely reasons about a 4k stage, so it has NO twin
// here. Hypothesis: same process dom, per-process temp_alloc_cache_{2m,1g}
// unchanged, and every Owned{2m,1g} page slot (old or new) keeps its state -- the
// only fields the halves read.

// process_staged_pages_2m_wf: Owned2m <-> process temp_alloc_cache_2m.
pub proof fn process_staged_pages_2m_wf_preserved_for_eq(
    old_process_map: ProcessLockedMap,
    new_process_map: ProcessLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        process_staged_pages_2m_wf(old_process_map, old_page_array),
        new_process_map.dom() == old_process_map.dom(),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_map.spec_index(p_ptr).view().temp_alloc_cache_2m]
            new_process_map.dom().contains(p_ptr)
            ==> new_process_map.spec_index(p_ptr).view().temp_alloc_cache_2m == old_process_map.spec_index(p_ptr).view().temp_alloc_cache_2m,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state is Owned2m)
                || (new_page_array.spec_index(p_i).view().view().state is Owned2m))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        process_staged_pages_2m_wf(new_process_map, new_page_array),
{
    reveal(process_staged_pages_2m_wf);
}

// process_staged_pages_1g_wf: Owned1g <-> process temp_alloc_cache_1g.
pub proof fn process_staged_pages_1g_wf_preserved_for_eq(
    old_process_map: ProcessLockedMap,
    new_process_map: ProcessLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        process_staged_pages_1g_wf(old_process_map, old_page_array),
        new_process_map.dom() == old_process_map.dom(),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_map.spec_index(p_ptr).view().temp_alloc_cache_1g]
            new_process_map.dom().contains(p_ptr)
            ==> new_process_map.spec_index(p_ptr).view().temp_alloc_cache_1g == old_process_map.spec_index(p_ptr).view().temp_alloc_cache_1g,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state is Owned1g)
                || (new_page_array.spec_index(p_i).view().view().state is Owned1g))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        process_staged_pages_1g_wf(new_process_map, new_page_array),
{
    reveal(process_staged_pages_1g_wf);
}

}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {
// Framing lemma: `hugepage_2m_wf` reads only the `state` of 2m-related slots, so it survives any change that keeps the state of every slot 2m-related before or after.
pub proof fn hugepage_2m_wf_preserved_for_page_state_eq(old_page_array: PageLockedArray, new_page_array: PageLockedArray)
    requires
        hugepage_2m_wf(old_page_array),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i) && (page_state_2m_related(old_page_array.spec_index(p_i).view().view().state) || page_state_2m_related(new_page_array.spec_index(p_i).view().view().state))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        hugepage_2m_wf(new_page_array),
{ reveal(hugepage_2m_wf); }

// 1g twin of `hugepage_2m_wf_preserved_for_page_state_eq`.
pub proof fn hugepage_1g_wf_preserved_for_page_state_eq(old_page_array: PageLockedArray, new_page_array: PageLockedArray)
    requires
        hugepage_1g_wf(old_page_array),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i) && (page_state_1g_related(old_page_array.spec_index(p_i).view().view().state) || page_state_1g_related(new_page_array.spec_index(p_i).view().view().state))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        hugepage_1g_wf(new_page_array),
{ reveal(hugepage_1g_wf); }
}

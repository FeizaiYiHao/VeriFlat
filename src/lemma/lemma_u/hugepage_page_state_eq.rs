use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// Framing lemma: if every page slot that is 2m-related (in the OLD or the NEW
// array) has an unchanged `state` and `owning_container`, then `hugepage_2m_wf`
// is preserved. Mirror of `process_no_change_to_tree_fields_imply_wf` — scoped to
// exactly the fields the invariant reads. `hugepage_2m_wf`'s three conjuncts only
// ever read `state`/`owning_container` of 2m-related slots (a leaf-2m or merge
// head p_i, its Merged2m tail p_j, or a Merged2m slot's leaf-2m truncation), so a
// mutation that touches only non-2m slots (e.g. a Free4k→Owned4k retype) leaves
// every read-slot byte-equal and the invariant stands.
pub proof fn hugepage_2m_wf_preserved_for_page_state_eq(
    old_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
    new_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
)
    requires
        hugepage_2m_wf(old_page_array),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && (page_state_2m_related(old_page_array.spec_index(p_i).view().view().state)
                || page_state_2m_related(new_page_array.spec_index(p_i).view().view().state))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                && new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container,
    ensures
        hugepage_2m_wf(new_page_array),
{
    reveal(hugepage_2m_wf);
}

// Quantified-fact form of `hugepage_2m_wf_preserved_for_page_state_eq`: a single
// invocation installs the fact for ALL `(old, new)` arrays, so a caller need not
// spell out the pair or wrap it in an `assert forall`. Multi-trigger on the
// source + target `hugepage_2m_wf` terms: fires once the caller has
// `hugepage_2m_wf(old)` in scope and the goal mentions `hugepage_2m_wf(new)`.
pub proof fn hugepage_2m_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
            new_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
        |
            #![trigger hugepage_2m_wf(old_page_array), hugepage_2m_wf(new_page_array)]
            (hugepage_2m_wf(old_page_array)
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && (page_state_2m_related(old_page_array.spec_index(p_i).view().view().state)
                    || page_state_2m_related(new_page_array.spec_index(p_i).view().view().state))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                    && new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container)
            ==>
            hugepage_2m_wf(new_page_array),
{
    assert forall|
        old_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
        new_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
    |
        (hugepage_2m_wf(old_page_array)
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && (page_state_2m_related(old_page_array.spec_index(p_i).view().view().state)
                || page_state_2m_related(new_page_array.spec_index(p_i).view().view().state))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                && new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container)
        implies
        hugepage_2m_wf(new_page_array)
    by {
        hugepage_2m_wf_preserved_for_page_state_eq(old_page_array, new_page_array);
    };
}

// 1g twin of `hugepage_2m_wf_preserved_for_page_state_eq`.
pub proof fn hugepage_1g_wf_preserved_for_page_state_eq(
    old_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
    new_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
)
    requires
        hugepage_1g_wf(old_page_array),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && (page_state_1g_related(old_page_array.spec_index(p_i).view().view().state)
                || page_state_1g_related(new_page_array.spec_index(p_i).view().view().state))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                && new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container,
    ensures
        hugepage_1g_wf(new_page_array),
{
    reveal(hugepage_1g_wf);
}

// Quantified-fact form of `hugepage_1g_wf_preserved_for_page_state_eq`; see the
// 2m twin for the trigger rationale.
pub proof fn hugepage_1g_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
            new_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
        |
            #![trigger hugepage_1g_wf(old_page_array), hugepage_1g_wf(new_page_array)]
            (hugepage_1g_wf(old_page_array)
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && (page_state_1g_related(old_page_array.spec_index(p_i).view().view().state)
                    || page_state_1g_related(new_page_array.spec_index(p_i).view().view().state))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                    && new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container)
            ==>
            hugepage_1g_wf(new_page_array),
{
    assert forall|
        old_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
        new_page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
    |
        (hugepage_1g_wf(old_page_array)
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && (page_state_1g_related(old_page_array.spec_index(p_i).view().view().state)
                || page_state_1g_related(new_page_array.spec_index(p_i).view().view().state))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                && new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container)
        implies
        hugepage_1g_wf(new_page_array)
    by {
        hugepage_1g_wf_preserved_for_page_state_eq(old_page_array, new_page_array);
    };
}

}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// A single non-mapped page may change payload/state without affecting the
/// bidirectional page-table mapping invariant. All mapped pages remain exact
/// because `unchanged_except` frames every other page slot.
pub proof fn page_pagetable_wf_preserved_for_nonmapped_page_change(
    old_pagetable_map: PageTableLockedMap,
    new_pagetable_map: PageTableLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    changed_page: PageIndex,
)
    requires
        page_pagetable_wf(old_pagetable_map, old_page_array),
        pagetable_perms_wf(old_pagetable_map),
        new_pagetable_map == old_pagetable_map,
        page_index_wf(changed_page),
        new_page_array.unchanged_except(&old_page_array, changed_page),
        !old_page_array.spec_index(changed_page).view().view().is_mapped(),
        !new_page_array.spec_index(changed_page).view().view().is_mapped(),
    ensures
        page_pagetable_wf(new_pagetable_map, new_page_array),
{
    page_ptr_lemma1();
    reveal(page_pagetable_wf);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
    reveal(pagetable_perms_wf);
}

/// Lock-state-only changes preserve the mapping invariant when every page
/// payload is unchanged.
pub proof fn page_pagetable_wf_preserved_for_page_payloads_unchanged(
    old_pagetable_map: PageTableLockedMap,
    new_pagetable_map: PageTableLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        page_pagetable_wf(old_pagetable_map, old_page_array),
        pagetable_perms_wf(old_pagetable_map),
        new_pagetable_map == old_pagetable_map,
        new_page_array.payloads_unchanged(&old_page_array),
    ensures
        page_pagetable_wf(new_pagetable_map, new_page_array),
{
    page_ptr_lemma1();
    reveal(page_pagetable_wf);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
    reveal(pagetable_perms_wf);
    reveal(LockedArray::payloads_unchanged);
}

}

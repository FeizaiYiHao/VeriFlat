use vstd::prelude::*;
use crate::*;

verus! {
/// Every user 1G L3 entry of the table `pt_ptr` with the kernel_present and PS bits set, and every present 1G mapping of it, names a Mapped1g page that lists `pt_ptr` at that VA.
pub(crate) proof fn mapped_1g_page_pagetable_wf_table_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pt_ptr: RwLockPageTableRoot)
    requires
        mapped_1g_page_pagetable_wf(pt_mp, pt_lower, pg_arr),
        pt_mp.dom().contains(pt_ptr),
    ensures
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)]
            whole_pagetable(pt_mp, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i) is Some ==> {
                let pg_idx = page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)->0.addr);
                &&& index_valid(NUM_PAGES, pg_idx)
                &&& pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped1g
                &&& pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt_ptr, spec_index2va((l4i, l3i, 0, 0))))
            },
        forall|va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_1g().contains_key(va)]
            whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_1g().contains_key(va) ==> {
                let page = pg_arr.spec_index(page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_1g().spec_index(va).addr)).view().view();
                &&& page.state == PageState::Mapped1g
                &&& page.mappings().contains((pt_ptr, va))
            },
{ reveal(mapped_1g_page_pagetable_wf); }

}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {
// Framing lemma for `container_owned_pages_wf`: it reads containers' `owned_pages`, slots' `owning_container`, and only the merged and huge-page classes of page states.
pub proof fn container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_page_array: PageLockedArray, new_page_array: PageLockedArray)
    requires
        container_owned_pages_wf(old_container_map, old_page_array),
        new_container_map.dom() == old_container_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr).view().owned_pages]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view().owned_pages == old_container_map.spec_index(c_ptr).view().owned_pages,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().owning_container]
            index_valid(NUM_PAGES, p_i) ==> new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container,
        forall|p_i: PageIndex| #![trigger new_page_array.spec_index(p_i).view().view().state] index_valid(NUM_PAGES, p_i) ==> {
            let old_state = old_page_array.spec_index(p_i).view().view().state;
            let new_state = new_page_array.spec_index(p_i).view().view().state;
            &&& (new_state is Merged2m) == (old_state is Merged2m) && (new_state is Merged1g) == (old_state is Merged1g)
            &&& page_state_2m_related(new_state) == page_state_2m_related(old_state) && page_state_1g_related(new_state) == page_state_1g_related(old_state)
        },
    ensures
        container_owned_pages_wf(new_container_map, new_page_array),
{ reveal(container_owned_pages_wf); }
}

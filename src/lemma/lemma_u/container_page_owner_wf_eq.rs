use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// Framing lemma for `container_page_owner_wf` (the container_map <-> page_array
// owning_container bridge). Distinct from the page-state-class families: this
// invariant reads NO page-state variant, only every slot's `owning_container`
// plus each container's `owned_pages`. So the hypothesis frames on those two:
// per-container `owned_pages` unchanged (same container dom) and per-slot
// `owning_container` unchanged. Reusable by any syscall that retypes/moves pages
// without changing which container owns them (e.g. a Free4k->Owned4k stage, which
// preserves owning_container). Keeps the predicate opaque at the call site.
pub proof fn container_page_owner_wf_preserved_for_owning_container_eq(
    old_container_map: ContainerLockedMap,
    new_container_map: ContainerLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        container_page_owner_wf(old_container_map, old_page_array),
        new_container_map.dom() == old_container_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr).view().owned_pages]
            new_container_map.dom().contains(c_ptr)
            ==> new_container_map.spec_index(c_ptr).view().owned_pages == old_container_map.spec_index(c_ptr).view().owned_pages,
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().owning_container]
            page_index_valid(p_i)
            ==> new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container,
    ensures
        container_page_owner_wf(new_container_map, new_page_array),
{
    reveal(container_page_owner_wf);
}

}

use vstd::prelude::*;
use crate::*;

verus! {
/// A single non-mapped page may change payload/state without affecting the IOMMU page relations: every mapped page
/// stays exact because `entries_unchanged_except` frames every other page slot.
pub proof fn page_iommu_table_wf_preserved_for_nonmapped_page_change(
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, old_iommu_table_map: IommuTableLockedMap, new_iommu_table_map: IommuTableLockedMap,
    old_page_array: PageLockedArray, new_page_array: PageLockedArray, changed_page: PageIndex,
)
    requires
        page_iommu_table_wf(container_map, process_map, old_iommu_table_map, old_page_array),
        iommu_table_perms_wf(old_iommu_table_map),
        new_iommu_table_map == old_iommu_table_map,
        index_valid(NUM_PAGES, changed_page),
        new_page_array.entries_unchanged_except(&old_page_array, changed_page),
        !old_page_array.spec_index(changed_page).view().view().is_mapped(),
        !new_page_array.spec_index(changed_page).view().view().is_mapped(),
    ensures
        page_iommu_table_wf(container_map, process_map, new_iommu_table_map, new_page_array),
{ reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); }

pub proof fn lemma_page_iommu_table_wf_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|container_map: ContainerLockedMap, pre: ProcessLockedMap, post: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray|
            #![trigger page_iommu_table_wf(container_map, pre, iommu_table_map, page_array), page_iommu_table_wf(container_map, post, iommu_table_map, page_array)]
            page_iommu_table_wf(container_map, pre, iommu_table_map, page_array) && process_invariant_fields_except_quota_unchanged(pre, post)
                ==> page_iommu_table_wf(container_map, post, iommu_table_map, page_array),
{ reveal(page_iommu_table_wf); }

pub proof fn lemma_page_iommu_table_wf_preserved_for_container_invariant_fields_forall()
    ensures
        forall|pre: ContainerLockedMap, post: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray|
            #![trigger page_iommu_table_wf(pre, process_map, iommu_table_map, page_array), page_iommu_table_wf(post, process_map, iommu_table_map, page_array)]
            page_iommu_table_wf(pre, process_map, iommu_table_map, page_array) && container_invariant_fields_unchanged(pre, post)
                ==> page_iommu_table_wf(post, process_map, iommu_table_map, page_array),
{ reveal(page_iommu_table_wf); }

/// `iommu_table_perms_wf` gives the page-index validity of each IOMMU leaf address, as in the non-mapped-page lemma above.
pub proof fn page_iommu_table_wf_preserved_for_page_iommu_fields_eq(container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, old_page_array: PageLockedArray, new_page_array: PageLockedArray)
    requires
        page_iommu_table_wf(container_map, process_map, iommu_table_map, old_page_array),
        iommu_table_perms_wf(iommu_table_map),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i)]
            index_valid(NUM_PAGES, p_i) && (old_page_array.spec_index(p_i).view().view().is_mapped() || new_page_array.spec_index(p_i).view().view().is_mapped()) ==> {
                &&& new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state
                &&& new_page_array.spec_index(p_i).view().view().iommu_mappings() == old_page_array.spec_index(p_i).view().view().iommu_mappings()
                &&& new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container
            },
    ensures
        page_iommu_table_wf(container_map, process_map, iommu_table_map, new_page_array),
{ reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); }
}

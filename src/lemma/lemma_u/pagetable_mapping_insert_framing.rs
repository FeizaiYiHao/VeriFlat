use vstd::prelude::*;
use crate::*;

verus! {

pub proof fn process_pagetable_match_preserved_for_pagetable_payload_change(
    process_map: ProcessLockedMap,
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    changed: RwLockPageTableRoot,
)
    requires
        process_pagetable_match(process_map, pre),
        pre.dom().contains(changed),
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view().proc_ptr
            == pre.spec_index(changed).view().proc_ptr,
        post.spec_index(changed).view().pcid_value()
            == pre.spec_index(changed).view().pcid_value(),
    ensures
        process_pagetable_match(process_map, post),
{
    reveal(process_pagetable_match);
}

pub proof fn cpu_dirty_map_contains_pagetable_pcid_match_preserved_for_pagetable_payload_change(
    cpu_array: CpuLockedArray,
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    changed: RwLockPageTableRoot,
)
    requires
        cpu_dirty_map_contains_pagetable_pcid_match(pre, cpu_array),
        pre.dom().contains(changed),
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view().pcid_value()
            == pre.spec_index(changed).view().pcid_value(),
    ensures
        cpu_dirty_map_contains_pagetable_pcid_match(post, cpu_array),
{
    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
}

pub proof fn pagetable_pages_wf_preserved_for_nonstructural_page_and_pagetable_payload_change(
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    changed_pagetable: RwLockPageTableRoot,
    changed_page: PageIndex,
)
    requires
        pagetable_pages_wf(pre_pagetable_map, pre_page_array),
        pre_pagetable_map.dom().contains(changed_pagetable),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, changed_pagetable),
        post_pagetable_map.spec_index(changed_pagetable).view().page_closure()
            == pre_pagetable_map.spec_index(changed_pagetable).view().page_closure(),
        page_index_wf(changed_page),
        post_page_array.unchanged_except(&pre_page_array, changed_page),
        pre_page_array.spec_index(changed_page).view().view().state is Owned4k,
        post_page_array.spec_index(changed_page).view().view().state is Mapped4k,
    ensures
        pagetable_pages_wf(post_pagetable_map, post_page_array),
{
    reveal(pagetable_pages_wf);
}

pub proof fn iommu_table_pages_wf_preserved_for_nonstructural_page_change(
    iommu_table_map: IommuTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    changed_page: PageIndex,
)
    requires
        iommu_table_pages_wf(iommu_table_map, pre_page_array),
        page_index_wf(changed_page),
        post_page_array.unchanged_except(&pre_page_array, changed_page),
        pre_page_array.spec_index(changed_page).view().view().state is Owned4k,
        post_page_array.spec_index(changed_page).view().view().state is Mapped4k,
    ensures
        iommu_table_pages_wf(iommu_table_map, post_page_array),
{
    reveal(iommu_table_pages_wf);
}

}

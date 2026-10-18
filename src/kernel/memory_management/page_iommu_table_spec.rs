use vstd::prelude::*;
use crate::*;
verus! {
    /// Every IOMMU mapping recorded on a mapped page is a leaf of its size in that table, 4K IOMMU leaves and the
    /// pages they map agree in both directions, and a page is mapped only by IOMMU tables of processes inside its
    /// owner's subtree. Only 4K IOMMU leaves are ever installed: there is no 2M or 1G IOMMU map path.
    // Proof dependency (confirmed): iommu_table_perms_wf.
    #[verifier::opaque]
    pub open spec fn page_iommu_table_wf(container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray) -> bool {
        &&& forall|p_i: PageIndex|
            #![trigger page_array.spec_index(p_i)]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() ==> forall|it_ptr: RwLockPageTableRoot, iova: VAddr|
                #![trigger page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova))]
                #![trigger iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova)]
                page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova)) ==> {
                    let mapping = match page_array.spec_index(p_i).view().view().state {
                        PageState::Mapped4k => iommu_table_map.spec_index(it_ptr).view().mapping_4k(),
                        PageState::Mapped2m => iommu_table_map.spec_index(it_ptr).view().mapping_2m(),
                        _ => iommu_table_map.spec_index(it_ptr).view().mapping_1g(),
                    };
                    &&& iommu_table_map.dom().contains(it_ptr)
                    &&& mapping.contains_key(iova)
                    &&& mapping.spec_index(iova).addr == page_index2page_ptr(p_i)
                }
        &&& forall|it_ptr: RwLockPageTableRoot|
            #![trigger iommu_table_map.dom().contains(it_ptr)]
            iommu_table_map.dom().contains(it_ptr) ==> forall|iova: VAddr|
                #![trigger iommu_table_map.spec_index(it_ptr).view().mapping_4k().contains_key(iova)]
                #![trigger iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova)]
                iommu_table_map.spec_index(it_ptr).view().mapping_4k().contains_key(iova) ==> {
                    &&& page_array.spec_index(page_ptr2page_index(iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova).addr)).view().view().state == PageState::Mapped4k
                    &&& page_array.spec_index(page_ptr2page_index(iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova).addr)).view().view().iommu_mappings().contains((it_ptr, iova))
                    &&& iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova).owning_container.view()
                        == page_array.spec_index(page_ptr2page_index(iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova).addr)).view().view().owning_container
                }
        &&& forall|p_i: PageIndex, it_ptr: RwLockPageTableRoot, iova: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova))]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() && page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova)) ==> {
                let proc_ptr = iommu_table_map.spec_index(it_ptr).view().proc_ptr;
                let page_owner = page_array.spec_index(p_i).view().view().owning_container;
                &&& iommu_table_map.dom().contains(it_ptr)
                &&& process_map.dom().contains(proc_ptr)
                &&& container_map.dom().contains(page_owner)
                &&& {
                    ||| process_map.spec_index(proc_ptr).view_rodata().view().owning_container == page_owner
                    ||| container_map.spec_index(page_owner).view_ghost().subtree_set.view().contains(process_map.spec_index(proc_ptr).view_rodata().view().owning_container)
                }
            }
    }

    /// The 4K leaf `iova` of IOMMU table `it_ptr` names a `Mapped4k` page that records the mapping.
    pub proof fn page_iommu_table_wf_table_at(
        container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray, it_ptr: RwLockPageTableRoot, iova: VAddr,
    )
        requires
            page_iommu_table_wf(container_map, process_map, iommu_table_map, page_array),
            iommu_table_map.dom().contains(it_ptr),
            iommu_table_map.spec_index(it_ptr).view().mapping_4k().contains_key(iova),
        ensures
            ({
                let p_i = page_ptr2page_index(iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova).addr);
                &&& page_array.spec_index(p_i).view().view().state == PageState::Mapped4k
                &&& page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova))
                &&& iommu_table_map.spec_index(it_ptr).view().mapping_4k().spec_index(iova).owning_container.view() == page_array.spec_index(p_i).view().view().owning_container
            }),
    { reveal(page_iommu_table_wf); }
}

use vstd::prelude::*;
use crate::*;
verus! {
/// Mapped pages and IOMMU table leaves agree. Only 4K IOMMU leaves are ever installed: there is no 2M or 1G IOMMU map path.
// Proof dependency (confirmed): iommu_table_perms_wf.
#[verifier::opaque]
pub open spec fn page_iommu_table_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap, pg_arr: PageLockedArray) -> bool {
    // Every `(it, iova)` in a mapped page's IOMMU mappings is a leaf of the page's size in table `it` that points at the page.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        index_valid(NUM_PAGES, p_i) && pg_arr.spec_index(p_i).view().view().is_mapped()
            ==>
            forall|it: RwLockPageTableRoot, iova: VAddr|
                #![trigger pg_arr.spec_index(p_i).view().view().iommu_mappings().contains((it, iova))]
                #![trigger it_mp.spec_index(it).view().mapping_4k().spec_index(iova)]
                pg_arr.spec_index(p_i).view().view().iommu_mappings().contains((it, iova)) ==> {
                    let mapping = match pg_arr.spec_index(p_i).view().view().state {
                        PageState::Mapped4k => it_mp.spec_index(it).view().mapping_4k(),
                        PageState::Mapped2m => it_mp.spec_index(it).view().mapping_2m(),
                        _ => it_mp.spec_index(it).view().mapping_1g(),
                    };
                    &&& it_mp.dom().contains(it)
                    &&& mapping.contains_key(iova)
                    &&& mapping.spec_index(iova).addr == page_index2page_ptr(p_i)
                }
    // Every 4K leaf of an IOMMU table points at a Mapped4k page that lists it in its IOMMU mappings and shares the leaf's
    // container.
    &&& forall|it: RwLockPageTableRoot|
        #![trigger it_mp.dom().contains(it)]
        it_mp.dom().contains(it)
            ==>
            forall|iova: VAddr|
                #![trigger it_mp.spec_index(it).view().mapping_4k().contains_key(iova)]
                #![trigger it_mp.spec_index(it).view().mapping_4k().spec_index(iova)]
                it_mp.spec_index(it).view().mapping_4k().contains_key(iova) ==> {
                    let leaf = it_mp.spec_index(it).view().mapping_4k().spec_index(iova);
                    let page = pg_arr.spec_index(page_ptr2page_index(leaf.addr)).view().view();
                    &&& page.state == PageState::Mapped4k
                    &&& page.iommu_mappings().contains((it, iova))
                    &&& leaf.owning_container.view() == page.owning_container
                }
    // A page is mapped only by IOMMU tables whose process's container is the page's owner or inside its subtree.
    &&& forall|p_i: PageIndex, it: RwLockPageTableRoot, iova: VAddr|
        #![trigger pg_arr.spec_index(p_i).view().view().iommu_mappings().contains((it, iova))]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().is_mapped()
            && pg_arr.spec_index(p_i).view().view().iommu_mappings().contains((it, iova))
            ==> {
                let prc_ptr = it_mp.spec_index(it).view().proc_ptr;
                let page_owner = pg_arr.spec_index(p_i).view().view().owning_container;
                &&& it_mp.dom().contains(it)
                &&& prc_mp.dom().contains(prc_ptr)
                &&& ctn_mp.dom().contains(page_owner)
                &&& {
                    ||| prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == page_owner
                    ||| ctn_mp.spec_index(page_owner).view_ghost().subtree_set.view().contains(prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container)
                }
            }
}

/// The 4K leaf `iova` of IOMMU table `it_ptr` points at a `Mapped4k` page that lists `(it_ptr, iova)` in its IOMMU mappings.
pub proof fn page_iommu_table_wf_table_at(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap, pg_arr: PageLockedArray, it_ptr: RwLockPageTableRoot, iova: VAddr,
)
    requires
        page_iommu_table_wf(ctn_mp, prc_mp, it_mp, pg_arr),
        it_mp.dom().contains(it_ptr),
        it_mp.spec_index(it_ptr).view().mapping_4k().contains_key(iova),
    ensures
        ({
            let pg_idx = page_ptr2page_index(it_mp.spec_index(it_ptr).view().mapping_4k().spec_index(iova).addr);
            &&& pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped4k
            &&& pg_arr.spec_index(pg_idx).view().view().iommu_mappings().contains((it_ptr, iova))
            &&& it_mp.spec_index(it_ptr).view().mapping_4k().spec_index(iova).owning_container.view() == pg_arr.spec_index(pg_idx).view().view().owning_container
        }),
{ reveal(page_iommu_table_wf); }

/// The owner of the mapped page `p_i` that the leaf at `iova` of the IOMMU table `it_ptr` maps is the container of that
/// table's process or one of its ancestors.
pub proof fn page_iommu_table_wf_page_owner_at(
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray, p_i: PageIndex, it_ptr: RwLockPageTableRoot,
    iova: VAddr,
)
    requires
        page_iommu_table_wf(container_map, process_map, iommu_table_map, page_array),
        index_valid(NUM_PAGES, p_i),
        page_array.spec_index(p_i).view().view().is_mapped(),
        page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova)),
    ensures
        ({
            let proc_ptr = iommu_table_map.spec_index(it_ptr).view().proc_ptr;
            let page_owner = page_array.spec_index(p_i).view().view().owning_container;
            &&& process_map.dom().contains(proc_ptr)
            &&& container_map.dom().contains(page_owner)
            &&& process_map.spec_index(proc_ptr).view_rodata().view().owning_container == page_owner || container_map.spec_index(page_owner).view_ghost().subtree_set.view().contains(process_map.spec_index(proc_ptr).view_rodata().view().owning_container)
        }),
{ reveal(page_iommu_table_wf); }
}

use vstd::prelude::*;
use crate::*;

verus! {

#[verifier::opaque]
pub open spec fn iommu_table_pages_wf(
    iommu_table_map: IommuTableLockedMap,
    page_array: PageLockedArray,
) -> bool {
    // A root-object page names an IOMMU table in the map.
    &&& forall|page_index: PageIndex|
        #![trigger iommu_table_map.dom().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index)
        && (page_array.spec_index(page_index).view().view().state matches
            PageState::Allocated4k {
                state: Allocated4KPageState::AsIommuTableRoot,
            })
        ==> iommu_table_map.dom().contains(page_index2page_ptr(page_index))
    // Every internal page names its owning IOMMU table and belongs to its
    // page-table closure.
    &&& forall|page_index: PageIndex|
        #![trigger iommu_table_map.dom().contains(
            page_array.spec_index(page_index).view().view().state
                ->IOMMUTable_iommu_table_root)]
        #![trigger iommu_table_map.spec_index(
            page_array.spec_index(page_index).view().view().state
                ->IOMMUTable_iommu_table_root)
            .view().page_closure().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index)
        && (page_array.spec_index(page_index).view().view().state matches
            PageState::IOMMUTable { iommu_table_root })
        ==>
        {
            let iommu_root = page_array.spec_index(page_index).view().view().state
                ->IOMMUTable_iommu_table_root;
            &&& iommu_table_map.dom().contains(iommu_root)
            &&& iommu_table_map.spec_index(iommu_root).view()
                .page_closure().contains(page_index2page_ptr(page_index))
        }
    // Every map entry is backed by its distinct root-object page.
    &&& forall|iommu_root: RwLockPageTableRoot|
        #![trigger iommu_table_map.dom().contains(iommu_root)]
        iommu_table_map.dom().contains(iommu_root)
        ==>
        {
            let page_index = page_ptr2page_index(iommu_root);
            &&& page_ptr_valid(iommu_root)
            &&& page_array.spec_index(page_index).view().view().state
                == PageState::Allocated4k {
                    state: Allocated4KPageState::AsIommuTableRoot,
                }
        }
    // Every physical page used by the table walk is tagged with the owning
    // root. The root-object page itself is not part of this closure.
    &&& forall|iommu_root: RwLockPageTableRoot, table_page: PagePtr|
        #![trigger iommu_table_map.spec_index(iommu_root).view()
            .page_closure().contains(table_page)]
        iommu_table_map.dom().contains(iommu_root)
        && iommu_table_map.spec_index(iommu_root).view()
            .page_closure().contains(table_page)
        ==>
        {
            &&& page_ptr_valid(table_page)
            &&& page_array.spec_index(page_ptr2page_index(table_page)).view()
                .view().state == PageState::IOMMUTable {
                    iommu_table_root: iommu_root,
                }
        }
}

}

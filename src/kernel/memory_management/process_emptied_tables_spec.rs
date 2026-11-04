use vstd::prelude::*;
use crate::*;

verus! {
/// No CPU page table maps a 1G leaf.
/// Interim: until the thread_exit and kill reclaim paths remove 2M leaves and `process_emptied_tables_wf` excludes them for
/// emptied tables, this also keeps every CPU table free of 2M leaves; that conjunct is then deleted.
#[verifier::opaque]
pub open spec fn pagetable_no_1g_leaf_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    forall|pt_ptr: RwLockPageTableRoot|
        #![trigger whole_pagetable(pagetable_map, pt_lower, pt_ptr)]
        pagetable_map.dom().contains(pt_ptr) ==> {
            &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().dom() =~= Set::<VAddr>::empty()
        }
}

pub proof fn pagetable_no_1g_leaf_wf_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_no_1g_leaf_wf(pagetable_map, pt_lower),
        pagetable_map.dom().contains(pt_ptr),
    ensures
        whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().dom() =~= Set::<VAddr>::empty(),
{ reveal(pagetable_no_1g_leaf_wf); }

/// Every IOMMU table maps only 4K leaves.
#[verifier::opaque]
pub open spec fn iommu_table_no_huge_leaf_wf(iommu_table_map: IommuTableLockedMap) -> bool {
    forall|iommu_root: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_root)]
        iommu_table_map.dom().contains(iommu_root) ==> {
            &&& iommu_table_map.spec_index(iommu_root).view().mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& iommu_table_map.spec_index(iommu_root).view().mapping_1g().dom() =~= Set::<VAddr>::empty()
        }
}

pub proof fn iommu_table_no_huge_leaf_wf_at(iommu_table_map: IommuTableLockedMap, iommu_root: RwLockPageTableRoot)
    requires
        iommu_table_no_huge_leaf_wf(iommu_table_map),
        iommu_table_map.dom().contains(iommu_root),
    ensures
        iommu_table_map.spec_index(iommu_root).view().mapping_2m().dom() =~= Set::<VAddr>::empty(),
        iommu_table_map.spec_index(iommu_root).view().mapping_1g().dom() =~= Set::<VAddr>::empty(),
{ reveal(iommu_table_no_huge_leaf_wf); }

/// The page table, and the IOMMU table if any, of a process whose tables were emptied or that is a zombie map no 4K leaf;
/// its page table is named by no record of a mapped page and no user root entry of it resolves;
/// 2M/1G leaves are excluded by `pagetable_no_1g_leaf_wf` and `iommu_table_no_huge_leaf_wf`.
// Proof dependencies (for page-table and IOMMU-table changes): process_pagetable_match, process_iommu_table_match.
#[verifier::opaque]
pub open spec fn process_emptied_tables_wf(
    process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray,
) -> bool {
    forall|proc_ptr: RwLockProcessPtr|
        #![trigger process_map.spec_index(proc_ptr)]
        process_map.dom().contains(proc_ptr) && (process_map.spec_index(proc_ptr).view().state.view() is TablesEmptied || process_map.spec_index(proc_ptr).view().state.view() is Zombie) ==> {
            let process = process_map.spec_index(proc_ptr).view();
            &&& whole_pagetable(pagetable_map, pt_lower, process.pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& process.iommu_table is Some ==> iommu_table_map.spec_index(process.iommu_table.unwrap()).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& forall|p_i: PageIndex, va: VAddr|
                #![trigger page_array.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))]
                index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() ==> !page_array.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))
            &&& forall|l4i: L4Index| #![trigger whole_pagetable(pagetable_map, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i)]
                whole_pagetable(pagetable_map, pt_lower, process.pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(pagetable_map, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i) is None
        }
}

pub proof fn process_emptied_tables_wf_at(
    process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray,
    proc_ptr: RwLockProcessPtr,
)
    requires
        process_emptied_tables_wf(process_map, pagetable_map, pt_lower, iommu_table_map, page_array),
    ensures
        process_map.dom().contains(proc_ptr) && (process_map.spec_index(proc_ptr).view().state.view() is TablesEmptied || process_map.spec_index(proc_ptr).view().state.view() is Zombie) ==> ({
            let process = process_map.spec_index(proc_ptr).view();
            &&& whole_pagetable(pagetable_map, pt_lower, process.pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& process.iommu_table is Some ==> iommu_table_map.spec_index(process.iommu_table.unwrap()).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& forall|p_i: PageIndex, va: VAddr|
                #![trigger page_array.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))]
                index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() ==> !page_array.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))
            &&& forall|l4i: L4Index| #![trigger whole_pagetable(pagetable_map, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i)]
                whole_pagetable(pagetable_map, pt_lower, process.pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(pagetable_map, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i) is None
        }),
{ reveal(process_emptied_tables_wf); }
}

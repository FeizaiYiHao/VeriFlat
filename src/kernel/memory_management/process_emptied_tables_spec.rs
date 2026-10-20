use vstd::prelude::*;
use crate::*;

verus! {
/// Every user and IOMMU page table maps only 4K leaves.
/// TODO: 2M/1G user mappings are not modeled yet; when `map_2m_page`/1G mapping syscalls are added, this leaf must be replaced
/// by 2M/1G leaf removal in the kill and thread_exit reclaim paths.
#[verifier::opaque]
pub open spec fn pagetable_no_huge_leaf_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pagetable_c(pagetable_map, pt_lower, pt_ptr)]
        pagetable_map.dom().contains(pt_ptr) ==> {
            &&& pagetable_c(pagetable_map, pt_lower, pt_ptr).mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& pagetable_c(pagetable_map, pt_lower, pt_ptr).mapping_1g().dom() =~= Set::<VAddr>::empty()
        }
    &&& forall|iommu_root: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_root)]
        iommu_table_map.dom().contains(iommu_root) ==> {
            &&& iommu_table_map.spec_index(iommu_root).view().mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& iommu_table_map.spec_index(iommu_root).view().mapping_1g().dom() =~= Set::<VAddr>::empty()
        }
}

pub proof fn pagetable_no_huge_leaf_wf_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, iommu_table_map: IommuTableLockedMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_no_huge_leaf_wf(pagetable_map, pt_lower, iommu_table_map),
    ensures
        pagetable_map.dom().contains(pt_ptr) ==> pagetable_c(pagetable_map, pt_lower, pt_ptr).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        pagetable_map.dom().contains(pt_ptr) ==> pagetable_c(pagetable_map, pt_lower, pt_ptr).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        iommu_table_map.dom().contains(pt_ptr) ==> iommu_table_map.spec_index(pt_ptr).view().mapping_2m().dom() =~= Set::<VAddr>::empty(),
        iommu_table_map.dom().contains(pt_ptr) ==> iommu_table_map.spec_index(pt_ptr).view().mapping_1g().dom() =~= Set::<VAddr>::empty(),
{ reveal(pagetable_no_huge_leaf_wf); }

/// The page table, and the IOMMU table if any, of a process whose tables were emptied or that is a zombie map no 4K leaf;
/// 2M/1G leaves are excluded by `pagetable_no_huge_leaf_wf`.
// Proof dependencies (for page-table and IOMMU-table changes): process_pagetable_match, process_iommu_table_match.
#[verifier::opaque]
pub open spec fn process_emptied_tables_wf(process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, iommu_table_map: IommuTableLockedMap) -> bool {
    forall|proc_ptr: RwLockProcessPtr|
        #![trigger process_map.spec_index(proc_ptr)]
        process_map.dom().contains(proc_ptr) && (process_map.spec_index(proc_ptr).view().state.view() is TablesEmptied || process_map.spec_index(proc_ptr).view().state.view() is Zombie) ==> {
            let process = process_map.spec_index(proc_ptr).view();
            &&& pagetable_c(pagetable_map, pt_lower, process.pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& process.iommu_table is Some ==> iommu_table_map.spec_index(process.iommu_table.unwrap()).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
        }
}

pub proof fn process_emptied_tables_wf_at(process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, iommu_table_map: IommuTableLockedMap, proc_ptr: RwLockProcessPtr)
    requires
        process_emptied_tables_wf(process_map, pagetable_map, pt_lower, iommu_table_map),
    ensures
        process_map.dom().contains(proc_ptr) && (process_map.spec_index(proc_ptr).view().state.view() is TablesEmptied || process_map.spec_index(proc_ptr).view().state.view() is Zombie) ==> ({
            let process = process_map.spec_index(proc_ptr).view();
            &&& pagetable_c(pagetable_map, pt_lower, process.pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& process.iommu_table is Some ==> iommu_table_map.spec_index(process.iommu_table.unwrap()).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
        }),
{ reveal(process_emptied_tables_wf); }
}

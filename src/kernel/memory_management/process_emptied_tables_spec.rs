use vstd::prelude::*;
use crate::*;

verus! {
/// The page table, and the IOMMU table if any, of a process whose tables were emptied or that is a zombie map no 4K leaf;
/// no mapped page lists its page table in its mappings, and no user L4 entry of its page table resolves.
/// 1G leaves are excluded by `pagetable_no_1g_leaf_wf` and IOMMU 2M/1G leaves by `iommu_table_no_huge_leaf_wf`; a 2M leaf of a
/// page table names a Mapped2m page that lists the table (`mapped_2m_page_pagetable_wf`), which the no-listing clause excludes.
#[verifier::opaque]
pub open spec fn process_emptied_tables_wf(
    prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pg_arr: PageLockedArray,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p)]
        prc_mp.dom().contains(p)
            && (prc_mp.spec_index(p).view().state.view() is TablesEmptied || prc_mp.spec_index(p).view().state.view() is Zombie)
            ==> {
                let process = prc_mp.spec_index(p).view();
                // Its page table has no 4K leaf.
                &&& whole_pagetable(pt_mp, pt_lower, process.pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()
                // Its IOMMU table has no 4K leaf.
                &&& process.iommu_table is Some ==> it_mp.spec_index(process.iommu_table.unwrap()).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
                // No mapped page lists its page table in its mappings.
                &&& forall|p_i: PageIndex, va: VAddr|
                    #![trigger pg_arr.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))]
                    index_valid(NUM_PAGES, p_i)
                        && pg_arr.spec_index(p_i).view().view().is_mapped()
                        ==>
                        !pg_arr.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))
                // No user L4 entry resolves.
                &&& forall|l4i: L4Index|
                    #![trigger whole_pagetable(pt_mp, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i)]
                    whole_pagetable(pt_mp, pt_lower, process.pagetable).kernel_l4_end() <= l4i
                        && pei_valid(l4i)
                        ==>
                        whole_pagetable(pt_mp, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i) is None
            }
}

pub proof fn process_emptied_tables_wf_at(
    prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pg_arr: PageLockedArray,
    prc_ptr: RwLockProcessPtr,
)
    requires
        process_emptied_tables_wf(prc_mp, pt_mp, pt_lower, it_mp, pg_arr),
    ensures
        prc_mp.dom().contains(prc_ptr)
            && (prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied || prc_mp.spec_index(prc_ptr).view().state.view() is Zombie)
            ==> ({
                let process = prc_mp.spec_index(prc_ptr).view();
                &&& whole_pagetable(pt_mp, pt_lower, process.pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()
                &&& process.iommu_table is Some ==> it_mp.spec_index(process.iommu_table.unwrap()).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
                &&& forall|p_i: PageIndex, va: VAddr|
                    #![trigger pg_arr.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))]
                    index_valid(NUM_PAGES, p_i)
                        && pg_arr.spec_index(p_i).view().view().is_mapped()
                        ==>
                        !pg_arr.spec_index(p_i).view().view().mappings().contains((process.pagetable, va))
                &&& forall|l4i: L4Index|
                    #![trigger whole_pagetable(pt_mp, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i)]
                    whole_pagetable(pt_mp, pt_lower, process.pagetable).kernel_l4_end() <= l4i
                        && pei_valid(l4i)
                        ==>
                        whole_pagetable(pt_mp, pt_lower, process.pagetable).spec_resolve_mapping_l4(l4i) is None
            }),
{ reveal(process_emptied_tables_wf); }
}

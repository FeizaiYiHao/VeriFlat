use vstd::prelude::*;
use crate::*;

verus! {
/// Processes and IOMMU tables name each other.
#[verifier::opaque]
pub open spec fn process_iommu_table_wf(prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap) -> bool {
    // Process -> IOMMU table; the read-only `iommu_table_ptr` and `iommu_cr3` mirror the table object and its root so
    // readers never lock the process or the table.
    &&& forall|p: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view().iommu_table]
        prc_mp.dom().contains(p) ==> {
            let process = prc_mp.spec_index(p);
            &&& process.view_rodata().view().iommu_table_ptr == process.view().iommu_table
            &&& (process.view().iommu_table is Some) == (process.view_rodata().view().iommu_cr3 is Some)
            &&& process.view().iommu_table is Some ==> {
                let it_ptr = process.view().iommu_table.unwrap();
                &&& it_mp.dom().contains(it_ptr)
                &&& it_mp.spec_index(it_ptr).view().proc_ptr == p
                &&& process.view_rodata().view().iommu_cr3 == Some(it_mp.spec_index(it_ptr).view().cr3)
            }
        }
    // IOMMU table -> process.
    &&& forall|it: RwLockPageTableRoot|
        #![trigger it_mp.spec_index(it).view().proc_ptr]
        it_mp.dom().contains(it) ==> {
            let prc_ptr = it_mp.spec_index(it).view().proc_ptr;
            &&& prc_mp.dom().contains(prc_ptr)
            &&& prc_mp.spec_index(prc_ptr).view().iommu_table == Some(it)
        }
}

pub proof fn process_iommu_table_wf_process_at(prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_iommu_table_wf(prc_mp, it_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) ==> ({
            let process = prc_mp.spec_index(prc_ptr);
            &&& process.view_rodata().view().iommu_table_ptr == process.view().iommu_table
            &&& (process.view().iommu_table is Some) == (process.view_rodata().view().iommu_cr3 is Some)
            &&& process.view().iommu_table is Some ==> {
                let it_ptr = process.view().iommu_table.unwrap();
                &&& it_mp.dom().contains(it_ptr)
                &&& it_mp.spec_index(it_ptr).view().proc_ptr == prc_ptr
                &&& process.view_rodata().view().iommu_cr3 == Some(it_mp.spec_index(it_ptr).view().cr3)
            }
        }),
{ reveal(process_iommu_table_wf); }
}

use vstd::prelude::*;
use crate::*;

verus! {
/// The IOMMU table lock map is well-formed, every table lock satisfies inv(), and a table that hides leaves is write-locked.
#[verifier::opaque]
pub open spec fn iommu_table_perms_wf(it_mp: IommuTableLockedMap) -> bool {
    &&& it_mp.perms_wf()
    &&& pagetables_inv(it_mp)
    &&& iommu_table_hidden_leaves_only_when_write_locked(it_mp)
}

/// An IOMMU table with a leaf the device cannot see is write-locked: thread exit clears present bits and reclaims
/// those leaves before it releases the table.
#[verifier::opaque]
pub open spec fn iommu_table_hidden_leaves_only_when_write_locked(it_mp: IommuTableLockedMap) -> bool {
    forall|it: RwLockPageTableRoot|
        #![trigger it_mp.spec_index(it).locking_thread()]
        it_mp.dom().contains(it)
            && !it_mp.spec_index(it).view().leaves_present()
            ==>
            it_mp.spec_index(it).locking_thread() is Write
}

pub proof fn iommu_table_perms_wf_at(it_mp: IommuTableLockedMap, it_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(it_mp),
        it_mp.dom().contains(it_ptr),
    ensures
        it_mp.view().spec_index(it_ptr).is_init(),
        it_mp.view().spec_index(it_ptr).addr() == it_ptr,
        it_mp.spec_index(it_ptr).inv(),
        it_mp.spec_index(it_ptr).is_init(),
        it_mp.spec_index(it_ptr).view().inv(),
{ reveal(iommu_table_perms_wf); }

/// IOMMU table `it_ptr` maps no kernel L4 entries.
pub proof fn iommu_table_perms_wf_kernel_l4_end_at(it_mp: IommuTableLockedMap, it_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(it_mp),
        it_mp.dom().contains(it_ptr),
    ensures it_mp.spec_index(it_ptr).view().kernel_l4_end == 0,
{ reveal(iommu_table_perms_wf); reveal(PageTable::kernel_entries_wf); }

pub proof fn iommu_table_perms_wf_map(it_mp: IommuTableLockedMap)
    requires iommu_table_perms_wf(it_mp)
    ensures it_mp.perms_wf()
{ reveal(iommu_table_perms_wf); }

/// Every IOMMU table maps only 4K leaves.
#[verifier::opaque]
pub open spec fn iommu_table_no_huge_leaf_wf(it_mp: IommuTableLockedMap) -> bool {
    forall|it: RwLockPageTableRoot|
        #![trigger it_mp.spec_index(it)]
        it_mp.dom().contains(it) ==> {
            &&& it_mp.spec_index(it).view().mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& it_mp.spec_index(it).view().mapping_1g().dom() =~= Set::<VAddr>::empty()
        }
}

pub proof fn iommu_table_no_huge_leaf_wf_at(it_mp: IommuTableLockedMap, it_ptr: RwLockPageTableRoot)
    requires
        iommu_table_no_huge_leaf_wf(it_mp),
        it_mp.dom().contains(it_ptr),
    ensures
        it_mp.spec_index(it_ptr).view().mapping_2m().dom() =~= Set::<VAddr>::empty(),
        it_mp.spec_index(it_ptr).view().mapping_1g().dom() =~= Set::<VAddr>::empty(),
{ reveal(iommu_table_no_huge_leaf_wf); }
}

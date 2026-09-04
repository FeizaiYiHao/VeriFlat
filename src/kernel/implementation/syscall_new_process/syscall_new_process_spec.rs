use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::share_mapping_4k_target_map_after;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::share_mapping_4k::share_mapping_4k_target_map_after;

verus! {

pub open spec fn kernel_u_new_process_shared(
    created_u: KernelU,
    shared_u: KernelU,
    parent_ptr: RwLockProcessPtr,
    child_ptr: RwLockProcessPtr,
    range: &VaRange4K,
) -> bool {
    let created_child = created_u.process_map.spec_index(child_ptr);
    let child = shared_u.process_map.spec_index(child_ptr);
    &&& created_u.process_map.dom().contains(parent_ptr)
    &&& created_u.process_map.dom().contains(child_ptr)
    &&& shared_u.process_map.dom().contains(child_ptr)
    &&& range.wf()
    &&& range.len > 0
    &&& child.pagetable.mapping_4k == share_mapping_4k_target_map_after(shared_u.process_map.spec_index(parent_ptr).pagetable.mapping_4k, created_child.pagetable.mapping_4k, range, range, range.len as nat)
    &&& child.pagetable.mapping_2m == created_child.pagetable.mapping_2m
    &&& child.pagetable.mapping_1g == created_child.pagetable.mapping_1g
    &&& child.iommu_table == created_child.iommu_table
    &&& child.quota_4k == created_child.quota_4k
    &&& child.quota_2m == created_child.quota_2m
    &&& child.quota_1g == created_child.quota_1g
    &&& child.parent == created_child.parent
    &&& child.children == created_child.children
    &&& child.depth == created_child.depth
    &&& child.uppertree_seq == created_child.uppertree_seq
    &&& child.subtree_set == created_child.subtree_set
    &&& child.owned_threads == created_child.owned_threads
    &&& child.killed == created_child.killed
}

}

use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn container_pcid_allocator_wf(container_map: ContainerLockedMap, pcid_allocator_map: PcidAllocatorLockedMap) -> bool {
    // Container -> PCID allocator.
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr) ==> {
            let allc_ptr = container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator;
            &&& pcid_allocator_map.dom().contains(allc_ptr)
            &&& pcid_allocator_map.spec_index(allc_ptr).view().owning_container.view() == c_ptr
            &&& pcid_allocator_map.spec_index(allc_ptr).view().container_depth.view() == container_map.spec_index(c_ptr).view_rodata().view().depth
        }
    // PCID allocator -> container.
    &&& forall|allc_ptr: RwLockPcidAllocatorPtr|
        #![trigger pcid_allocator_map.dom().contains(allc_ptr)]
        pcid_allocator_map.dom().contains(allc_ptr) ==> {
            let c_ptr = pcid_allocator_map.spec_index(allc_ptr).view().owning_container.view();
            &&& container_map.dom().contains(c_ptr)
            &&& container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator == allc_ptr
        }
}

pub proof fn container_pcid_allocator_wf_container_at(container_map: ContainerLockedMap, pcid_allocator_map: PcidAllocatorLockedMap, c_ptr: RwLockContainerPtr)
    requires
        container_pcid_allocator_wf(container_map, pcid_allocator_map),
    ensures
        container_map.dom().contains(c_ptr) ==> ({
            let allc_ptr = container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator;
            &&& pcid_allocator_map.dom().contains(allc_ptr)
            &&& pcid_allocator_map.spec_index(allc_ptr).view().owning_container.view() == c_ptr
            &&& pcid_allocator_map.spec_index(allc_ptr).view().container_depth.view() == container_map.spec_index(c_ptr).view_rodata().view().depth
        }),
{ reveal(container_pcid_allocator_wf); }

pub proof fn container_pcid_allocator_wf_allocator_at(container_map: ContainerLockedMap, pcid_allocator_map: PcidAllocatorLockedMap, allc_ptr: RwLockPcidAllocatorPtr)
    requires
        container_pcid_allocator_wf(container_map, pcid_allocator_map),
    ensures
        pcid_allocator_map.dom().contains(allc_ptr) ==> ({
            let c_ptr = pcid_allocator_map.spec_index(allc_ptr).view().owning_container.view();
            &&& container_map.dom().contains(c_ptr)
            &&& container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator == allc_ptr
        }),
{ reveal(container_pcid_allocator_wf); }
}

use vstd::prelude::*;
use crate::*;

verus! {

#[verifier::opaque]
pub open spec fn container_pcid_allocator_wf(
    container_map: ContainerLockedMap,
    pcid_allocator_map: PcidAllocatorLockedMap,
) -> bool {
    // Container -> PCID allocator.
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr)
        ==>
        {
            let allocator_ptr =
                container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator;
            &&& pcid_allocator_map.dom().contains(allocator_ptr)
            &&& pcid_allocator_map.spec_index(allocator_ptr)
                .view().owning_container.view() == c_ptr
            &&& pcid_allocator_map.spec_index(allocator_ptr)
                .view().container_depth.view()
                == container_map.spec_index(c_ptr).view_rodata().view().depth
        }
    // PCID allocator -> container.
    &&& forall|allocator_ptr: RwLockPcidAllocatorPtr|
        #![trigger pcid_allocator_map.dom().contains(allocator_ptr)]
        pcid_allocator_map.dom().contains(allocator_ptr)
        ==>
        {
            let c_ptr = pcid_allocator_map.spec_index(allocator_ptr)
                .view().owning_container.view();

            &&& container_map.dom().contains(c_ptr)
            &&& container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator
                == allocator_ptr
        }
}

}

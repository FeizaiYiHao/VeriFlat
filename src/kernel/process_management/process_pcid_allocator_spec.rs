use vstd::prelude::*;
use crate::*;

verus! {

#[verifier::opaque]
pub open spec fn process_pcid_allocator_wf(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pcid_allocator_map: PcidAllocatorLockedMap,
) -> bool {
    // Process -> containing container's PCID allocator.
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.dom().contains(p_ptr)]
        process_map.dom().contains(p_ptr)
        ==>
        {
            let c_ptr =
                process_map.spec_index(p_ptr).view_rodata().view().owning_container;
            let pcid = process_map.spec_index(p_ptr).view().pcid;
            let allocator_ptr =
                container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator;

            &&& container_map.dom().contains(c_ptr)
            &&& pcid_allocator_map.dom().contains(allocator_ptr)
            &&& pcid_valid(pcid)
            &&& pcid_allocator_map.spec_index(allocator_ptr)
                .view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)
        }
    // PCID allocator -> process.
    &&& forall|allocator_ptr: RwLockPcidAllocatorPtr,
        pcid: Pcid,
        p_ptr: RwLockProcessPtr|
        #![trigger process_map.dom().contains(p_ptr), pcid_allocator_map.dom().contains(allocator_ptr), pcid_valid(pcid)]
        pcid_allocator_map.dom().contains(allocator_ptr)
        && pcid_valid(pcid)
        && pcid_allocator_map.spec_index(allocator_ptr)
            .view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)
        ==>
        {
            &&& process_map.dom().contains(p_ptr)
            &&& process_map.spec_index(p_ptr).view().pcid == pcid
            &&& process_map.spec_index(p_ptr).view_rodata().view().owning_container
                == pcid_allocator_map.spec_index(allocator_ptr)
                    .view().owning_container.view()
        }
}

}

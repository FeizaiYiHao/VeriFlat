use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn process_pcid_allocator_wf(container_map: ContainerLockedMap, process_map: ProcessLockedMap, pcid_allocator_map: PcidAllocatorLockedMap) -> bool {
    // Process -> containing container's PCID allocator.
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.dom().contains(p_ptr)]
        process_map.dom().contains(p_ptr) ==> {
            let c_ptr = process_map.spec_index(p_ptr).view_rodata().view().owning_container;
            let pcid = process_map.spec_index(p_ptr).view().pcid;
            let allocator_ptr = container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator;
            &&& container_map.dom().contains(c_ptr)
            &&& pcid_allocator_map.dom().contains(allocator_ptr)
            &&& pcid_valid(pcid)
            // A zombie keeps its `pcid` field but has released the id back to the allocator.
            &&& !process_map.spec_index(p_ptr).view().zombie ==> pcid_allocator_map.spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)
            &&& process_map.spec_index(p_ptr).view().zombie ==> !pcid_allocator_map.spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)
        }
    // PCID allocator -> process. The outer quantifier is keyed by the allocator's view so that a map whose
    // views are unchanged instantiates the inner one through a ground allocator term.
    &&& forall|allocator_ptr: RwLockPcidAllocatorPtr|
        #![trigger pcid_allocator_map.spec_index(allocator_ptr).view()]
        pcid_allocator_map.dom().contains(allocator_ptr) ==> forall|pcid: Pcid, p_ptr: RwLockProcessPtr|
            #![trigger pcid_allocator_map.spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)]
            pcid_valid(pcid) && pcid_allocator_map.spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr) ==> {
                &&& process_map.dom().contains(p_ptr)
                &&& process_map.spec_index(p_ptr).view().pcid == pcid
                &&& process_map.spec_index(p_ptr).view_rodata().view().owning_container == pcid_allocator_map.spec_index(allocator_ptr).view().owning_container.view()
            }
}

pub proof fn process_pcid_allocator_wf_process_at(container_map: ContainerLockedMap, process_map: ProcessLockedMap, pcid_allocator_map: PcidAllocatorLockedMap, p_ptr: RwLockProcessPtr)
    requires
        process_pcid_allocator_wf(container_map, process_map, pcid_allocator_map),
    ensures
        process_map.dom().contains(p_ptr) ==> ({
            let c_ptr = process_map.spec_index(p_ptr).view_rodata().view().owning_container;
            let pcid = process_map.spec_index(p_ptr).view().pcid;
            let allocator_ptr = container_map.spec_index(c_ptr).view_rodata().view().pcid_allocator;
            &&& container_map.dom().contains(c_ptr)
            &&& pcid_allocator_map.dom().contains(allocator_ptr)
            &&& pcid_valid(pcid)
            &&& !process_map.spec_index(p_ptr).view().zombie ==> pcid_allocator_map.spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)
            &&& process_map.spec_index(p_ptr).view().zombie ==> !pcid_allocator_map.spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(p_ptr)
        }),
{ reveal(process_pcid_allocator_wf); }

pub proof fn process_pcid_allocator_wf_unallocated_at(container_map: ContainerLockedMap, process_map: ProcessLockedMap, pcid_allocator_map: PcidAllocatorLockedMap,
    allocator_ptr: RwLockPcidAllocatorPtr, p_ptr: RwLockProcessPtr)
    requires
        process_pcid_allocator_wf(container_map, process_map, pcid_allocator_map),
        pcid_allocator_map.dom().contains(allocator_ptr),
        !process_map.dom().contains(p_ptr),
    ensures
        pcid_allocator_map.spec_index(allocator_ptr).view().process_is_unallocated(p_ptr),
{ reveal(process_pcid_allocator_wf); }
}

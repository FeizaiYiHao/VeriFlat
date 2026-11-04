use vstd::prelude::*;
use crate::*;

verus! {
/// Each container owns exactly its PCID allocator, tagged with its depth.
#[verifier::opaque]
pub open spec fn container_pcid_allocator_wf(ctn_mp: ContainerLockedMap, pcid_allc_mp: PcidAllocatorLockedMap) -> bool {
    // Container -> PCID allocator.
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) ==> {
            let pcid_allc_ptr = ctn_mp.spec_index(c).view_rodata().view().pcid_allocator;
            &&& pcid_allc_mp.dom().contains(pcid_allc_ptr)
            &&& pcid_allc_mp.spec_index(pcid_allc_ptr).view().owning_container.view() == c
            &&& pcid_allc_mp.spec_index(pcid_allc_ptr).view().container_depth.view() == ctn_mp.spec_index(c).view_rodata().view().depth
        }
    // PCID allocator -> container.
    &&& forall|pa: RwLockPcidAllocatorPtr|
        #![trigger pcid_allc_mp.dom().contains(pa)]
        pcid_allc_mp.dom().contains(pa) ==> {
            let ctn_ptr = pcid_allc_mp.spec_index(pa).view().owning_container.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pa
        }
}

pub proof fn container_pcid_allocator_wf_container_at(ctn_mp: ContainerLockedMap, pcid_allc_mp: PcidAllocatorLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_pcid_allocator_wf(ctn_mp, pcid_allc_mp),
    ensures
        ctn_mp.dom().contains(ctn_ptr) ==> ({
            let pcid_allc_ptr = ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator;
            &&& pcid_allc_mp.dom().contains(pcid_allc_ptr)
            &&& pcid_allc_mp.spec_index(pcid_allc_ptr).view().owning_container.view() == ctn_ptr
            &&& pcid_allc_mp.spec_index(pcid_allc_ptr).view().container_depth.view() == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth
        }),
{ reveal(container_pcid_allocator_wf); }

pub proof fn container_pcid_allocator_wf_allocator_at(ctn_mp: ContainerLockedMap, pcid_allc_mp: PcidAllocatorLockedMap, pcid_allc_ptr: RwLockPcidAllocatorPtr)
    requires
        container_pcid_allocator_wf(ctn_mp, pcid_allc_mp),
    ensures
        pcid_allc_mp.dom().contains(pcid_allc_ptr) ==> ({
            let ctn_ptr = pcid_allc_mp.spec_index(pcid_allc_ptr).view().owning_container.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pcid_allc_ptr
        }),
{ reveal(container_pcid_allocator_wf); }
}

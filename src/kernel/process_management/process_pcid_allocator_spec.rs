use vstd::prelude::*;
use crate::*;

verus! {
/// A live process holds its pcid in its container's PCID allocator; a zombie has released it.
#[verifier::opaque]
pub open spec fn process_pcid_allocator_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, pcid_allc_mp: PcidAllocatorLockedMap) -> bool {
    // Process -> containing container's PCID allocator.
    &&& forall|p: RwLockProcessPtr|
        #![trigger prc_mp.dom().contains(p)]
        prc_mp.dom().contains(p) ==> {
            let ctn_ptr = prc_mp.spec_index(p).view_rodata().view().owning_container;
            let pcid = prc_mp.spec_index(p).view().pcid;
            let pcid_allc_ptr = ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator;
            let ids = pcid_allc_mp.spec_index(pcid_allc_ptr).view().id_to_proc.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& pcid_allc_mp.dom().contains(pcid_allc_ptr)
            &&& pcid_valid(pcid)
            // A zombie keeps its `pcid` field but has released the id back to the allocator.
            &&& !prc_mp.spec_index(p).view().zombie ==> ids.spec_index(pcid as int).contains(p)
            &&& prc_mp.spec_index(p).view().zombie ==> !ids.spec_index(pcid as int).contains(p)
        }
    // PCID allocator -> process (the outer trigger on the allocator's view is load-bearing).
    &&& forall|pa: RwLockPcidAllocatorPtr|
        #![trigger pcid_allc_mp.spec_index(pa).view()]
        pcid_allc_mp.dom().contains(pa)
            ==> forall|pcid: Pcid, p: RwLockProcessPtr|
                #![trigger pcid_allc_mp.spec_index(pa).view().id_to_proc.view().spec_index(pcid as int).contains(p)]
                pcid_valid(pcid) && pcid_allc_mp.spec_index(pa).view().id_to_proc.view().spec_index(pcid as int).contains(p) ==> {
                    &&& prc_mp.dom().contains(p)
                    &&& prc_mp.spec_index(p).view().pcid == pcid
                    &&& prc_mp.spec_index(p).view_rodata().view().owning_container == pcid_allc_mp.spec_index(pa).view().owning_container.view()
                }
}

pub proof fn process_pcid_allocator_wf_process_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, pcid_allc_mp: PcidAllocatorLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_pcid_allocator_wf(ctn_mp, prc_mp, pcid_allc_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) ==> ({
            let ctn_ptr = prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container;
            let pcid = prc_mp.spec_index(prc_ptr).view().pcid;
            let pcid_allc_ptr = ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator;
            let ids = pcid_allc_mp.spec_index(pcid_allc_ptr).view().id_to_proc.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& pcid_allc_mp.dom().contains(pcid_allc_ptr)
            &&& pcid_valid(pcid)
            &&& !prc_mp.spec_index(prc_ptr).view().zombie ==> ids.spec_index(pcid as int).contains(prc_ptr)
            &&& prc_mp.spec_index(prc_ptr).view().zombie ==> !ids.spec_index(pcid as int).contains(prc_ptr)
        }),
{ reveal(process_pcid_allocator_wf); }

pub proof fn process_pcid_allocator_wf_unallocated_at(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, pcid_allc_mp: PcidAllocatorLockedMap, pcid_allc_ptr: RwLockPcidAllocatorPtr, prc_ptr: RwLockProcessPtr,
)
    requires
        process_pcid_allocator_wf(ctn_mp, prc_mp, pcid_allc_mp),
        pcid_allc_mp.dom().contains(pcid_allc_ptr),
        !prc_mp.dom().contains(prc_ptr),
    ensures
        pcid_allc_mp.spec_index(pcid_allc_ptr).view().process_is_unallocated(prc_ptr),
{ reveal(process_pcid_allocator_wf); }
}

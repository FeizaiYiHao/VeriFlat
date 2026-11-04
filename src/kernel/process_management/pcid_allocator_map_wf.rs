use vstd::prelude::*;
use crate::*;

verus! {
/// The PCID allocator map's permissions are well formed and every PCID allocator satisfies its own invariant.
#[verifier::opaque]
pub open spec fn pcid_allocator_perms_wf(pcid_allc_mp: PcidAllocatorLockedMap) -> bool {
    &&& pcid_allc_mp.perms_wf()
    &&& forall|pa: RwLockPcidAllocatorPtr|
        #![trigger pcid_allc_mp.dom().contains(pa)]
        pcid_allc_mp.dom().contains(pa) ==> pcid_allc_mp.spec_index(pa).inv()
}

pub proof fn pcid_allocator_perms_wf_map(pcid_allc_mp: PcidAllocatorLockedMap)
    requires pcid_allocator_perms_wf(pcid_allc_mp)
    ensures pcid_allc_mp.perms_wf()
{ reveal(pcid_allocator_perms_wf); }

pub proof fn pcid_allocator_perms_wf_at(pcid_allc_mp: PcidAllocatorLockedMap, pcid_allc_ptr: RwLockPcidAllocatorPtr)
    requires
        pcid_allocator_perms_wf(pcid_allc_mp),
        pcid_allc_mp.dom().contains(pcid_allc_ptr),
    ensures
        pcid_allc_mp.spec_index(pcid_allc_ptr).inv(),
{ reveal(pcid_allocator_perms_wf); }
}

use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn pcid_allocator_perms_wf(
    allocator_map: PcidAllocatorLockedMap,
) -> bool {
    &&& allocator_map.perms_wf()
    &&& forall|allocator_ptr: RwLockPcidAllocatorPtr|
        #![trigger allocator_map.dom().contains(allocator_ptr)]
        allocator_map.dom().contains(allocator_ptr)
        ==> allocator_map.spec_index(allocator_ptr).inv()
}

pub proof fn pcid_allocator_perms_wf_map(allocator_map: PcidAllocatorLockedMap) requires pcid_allocator_perms_wf(allocator_map) ensures allocator_map.perms_wf() { reveal(pcid_allocator_perms_wf); }

pub proof fn pcid_allocator_perms_wf_at(
    allocator_map: PcidAllocatorLockedMap,
    allocator_ptr: RwLockPcidAllocatorPtr,
)
    requires
        pcid_allocator_perms_wf(allocator_map),
        allocator_map.dom().contains(allocator_ptr),
    ensures
        allocator_map.perms_wf(),
        allocator_map.spec_index(allocator_ptr).inv(),
{
    reveal(pcid_allocator_perms_wf);
}
}

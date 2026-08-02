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

}

use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn allocator_perms_wf(alloc_map: LockedMap<RwLockPageAllocatorPtr, PageAllocator, ALLOCATOR_HAS_KILL_STATE>) -> bool {
        &&&
        alloc_map.perms_wf()
        &&&
        forall|a_ptr:RwLockPageAllocatorPtr|
            #![auto]
            alloc_map.dom().contains(a_ptr)
            ==>
            alloc_map[a_ptr].wlocked() || alloc_map[a_ptr].inv()
    }
}
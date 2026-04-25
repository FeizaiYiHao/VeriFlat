use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn allocator_perms_wf(alloc_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool {
        &&&
        alloc_map.perms_wf()
        &&&
        forall|a_ptr:RwLockPageAllocatorPtr|
            #![auto]
            alloc_map.dom().contains(a_ptr)
            ==>
            alloc_map[a_ptr].inv()
    }
}
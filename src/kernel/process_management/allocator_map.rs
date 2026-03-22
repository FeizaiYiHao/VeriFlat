use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub open spec fn allocator_4k_perms_wf(&self) -> bool{
            &&&
            self.allocator_4k_map.perms_wf()
            &&&
            self.allocators_4k_wlocked_or_inv()
        }
        pub open spec fn allocators_4k_wlocked_or_inv(&self) -> bool{
        &&&
        forall|allocator_4k_p:RwLockPageAllocatorPtr|
            #![auto]
            self.allocator_4k_map.dom().contains(allocator_4k_p)
            ==>
            self.allocator_4k_map[allocator_4k_p].wlocked() || self.allocator_4k_map[allocator_4k_p].inv()
    }
    }
}
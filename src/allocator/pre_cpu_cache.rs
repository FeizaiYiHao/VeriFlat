use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {

pub struct AllocatorCache{
    pub linked_list: LinkedList<PagePtr, 233>,
    pub local_quota: usize,
}

impl LockOwnerIdTrait for AllocatorCache{
    open spec fn container_depth(&self) -> LockOwnerId {
        self.linked_list.container_depth()
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        self.linked_list.process_depth()
    }
}

impl LockInvTrait for AllocatorCache{
    open spec fn inv(&self) -> bool {
        self.wf()
    }
}

impl LockMajorTrait for AllocatorCache{
    open spec fn lock_major_1(&self) -> LockMajorId {
        ALLOCATOR_CACHE_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        false
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        false
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        false
    }
}

impl AllocatorCache{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.linked_list.wf()
        &&&
        self.watermark_wf()
        &&&
        self.linked_list.view().no_duplicates()
    }
    pub open spec fn dom(&self) -> Set<PagePtr>
    {
        self.linked_list.dom()
    } 
    pub open spec fn watermark_wf(&self) -> bool{
        &&&
        self.local_quota <= ALLOCATOR_MAX_WATERMARK
    }
}

}
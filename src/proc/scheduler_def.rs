use vstd::prelude::*;
verus! {

use crate::*;

pub struct Scheduler{
    pub queue: LinkedList<RwLockThreadPtr, 233>,
    pub owning_container: RwLockContainerPtr, 
}

impl LockInvTrait for Scheduler {
    open spec fn inv(&self) -> bool {
        &&&
        self.queue.inv()
    }
}

impl LockMajorTrait for Scheduler {
    open spec fn lock_major_1(&self) -> LockMajorId {
        SCHEDULER_LOCK_MAJOR
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
        true
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        true
    }
}

impl LockOwnerIdTrait for Scheduler {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockUserVisibilityTrait for Scheduler {
    open spec fn is_user_visible() -> bool {
        false
    }
}

}
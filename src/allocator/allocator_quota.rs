use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {
pub struct AllocatorQuota{
    pub value: usize,
    pub minor: Ghost<LockMinorId>,
    pub container_depth: usize,
}

impl LockInvTrait for AllocatorQuota{
    open spec fn inv(&self) -> bool {
        true
    }
}

impl LockMajorTrait for AllocatorQuota {
    open spec fn lock_major_1(&self) -> LockMajorId {
        QUOTA_MAJOR
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

impl LockMinorTrait for AllocatorQuota {
    open spec fn lock_minor(&self) -> LockMinorId{
        self.minor@
    }
}

impl LockOwnerIdTrait for AllocatorQuota{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockUserVisibilityTrait for AllocatorQuota{
    open spec fn is_user_visible() -> bool {
        true
    }
}

impl LockIdTrait for AllocatorQuota{
    open spec fn lock_id(&self) -> LockId {
        LockId{
            container: self.container_depth(),
            process: self.process_depth(),
            major: self.current_lock_major(),
            minor: self.lock_minor(),
        }
    }
}

impl AllocatorQuota{
    pub open spec fn view(&self) -> usize{
        self.value
    }
    #[verifier(external_body)]
    pub fn exec_lock_minor(&self) -> (ret:LockMinorId)
        ensures
            ret == self.lock_minor(),
    {
        self as *const AllocatorQuota as LockMinorId
    }
}

}
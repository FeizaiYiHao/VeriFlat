use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;
verus! {
pub struct AllocatorQuota<const SIZE: usize> {
    pub value: usize,
    pub minor: Ghost<LockMinorId>,
    pub container_depth: usize,
}

impl<const SIZE: usize> LockInvTrait for AllocatorQuota<SIZE> {
    open spec fn inv(&self) -> bool { true }
}

impl<const SIZE: usize> LockMajorTrait for AllocatorQuota<SIZE> {
    open spec fn lock_major_1(&self) -> LockMajorId { allocator_quota_major(SIZE) }
    open spec fn lock_major_2(&self) -> LockMajorId { 233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 233 }
    open spec fn lock_major_default(&self) -> LockMajorId { 233 }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl<const SIZE: usize> LockMinorTrait for AllocatorQuota<SIZE> {
    open spec fn lock_minor(&self) -> LockMinorId { self.minor.view() }
}

impl<const SIZE: usize> LockOwnerIdTrait for AllocatorQuota<SIZE> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
}

impl<const SIZE: usize> LockIdTrait for AllocatorQuota<SIZE> {
    open spec fn lock_id(&self) -> LockId {
        LockId { container: self.container_depth(), process: self.process_depth(), major: self.current_lock_major(), minor: self.lock_minor() }
    }
}

impl<const SIZE: usize> AllocatorQuota<SIZE> {
    pub open spec fn view(&self) -> usize { self.value }
}
}

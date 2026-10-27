use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
verus! {
pub trait LockInvTrait {
    spec fn inv(&self) -> bool;
}

pub trait LockMajorTrait {
    spec fn lock_major_1(&self) -> LockMajorId;
    spec fn lock_major_2(&self) -> LockMajorId;
    spec fn lock_major_3(&self) -> LockMajorId;
    spec fn lock_major_default(&self) -> LockMajorId;

    spec fn lock_major_1_predicate(&self) -> bool;
    spec fn lock_major_2_predicate(&self) -> bool;
    spec fn lock_major_3_predicate(&self) -> bool;
    spec fn lock_major_default_predicate(&self) -> bool;

    open spec fn lock_major_sat(&self, lock_major: LockMajorId) -> bool {
        if lock_major == self.lock_major_1() { self.lock_major_1_predicate() }
        else if lock_major == self.lock_major_2() { self.lock_major_2_predicate() }
        else if lock_major == self.lock_major_3() { self.lock_major_3_predicate() }
        else if lock_major == self.lock_major_default() { self.lock_major_default_predicate() }
        else { false }
    }

    /// The lock major id corresponding to the object's current state.
    /// First state-specific predicate that holds (1, then 2, then 3) wins;
    /// otherwise the default major. Used to infer `lock_id.major` at lock
    /// acquire/release sites without asking the caller to construct it.
    open spec fn current_lock_major(&self) -> LockMajorId {
        if self.lock_major_1_predicate() { self.lock_major_1() }
        else if self.lock_major_2_predicate() { self.lock_major_2() }
        else if self.lock_major_3_predicate() { self.lock_major_3() }
        else { self.lock_major_default() }
    }
}

pub trait LockOwnerIdTrait {
    spec fn container_depth(&self) -> LockOwnerId;
    spec fn process_depth(&self) -> LockOwnerId;
    /// Source of the container component when this is a lock's read-only data: by default its own fixed owner.
    open spec fn container_source(&self) -> OwnerSource { OwnerSource::Fixed(self.container_depth()) }
    /// Source of the process component when this is a lock's read-only data: by default its own fixed owner.
    open spec fn process_source(&self) -> OwnerSource { OwnerSource::Fixed(self.process_depth()) }
}

/// Empty read-only data (`ROT = ()`) selects the payload `T`'s own owner ids; its own depths are never consulted.
impl LockOwnerIdTrait for () {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn container_source(&self) -> OwnerSource { OwnerSource::Payload }
    open spec fn process_source(&self) -> OwnerSource { OwnerSource::Payload }
}

pub trait LockMinorTrait {
    spec fn lock_minor(&self) -> LockMinorId;
}

pub trait UserViewHasKillState {
    spec fn killed(&self) -> bool;
}

pub trait LockIdTrait {
    spec fn lock_id(&self) -> LockId;
}
}

use vstd::prelude::*;
use crate::*;

verus! {

pub ghost enum LCtxtLockState {
    Acquire,
    Release,
}

pub tracked struct LCtxtState {
    pub kernel_view_locking_state: LCtxtLockState,
}

/// Per-thread ledgers of held locks.
///
/// `lock_id_set` contains only objects whose id can change with kernel state;
/// `stable_lock_id_set` contains objects whose id is immutable for the
/// object's lifetime.  Only the former needs kernel/object alignment at an
/// interleaving boundary.
pub tracked struct LocalContext {
    thread_id: LockThreadId,
    lock_id_set: Set<HeldLock>,
    stable_lock_id_set: Set<HeldLock>,
    state: LCtxtState,
}

impl LocalContext {
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set
    }

    pub closed spec fn stable_lock_id_set(&self) -> Set<HeldLock> {
        self.stable_lock_id_set
    }

    pub open spec fn held_lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set().union(self.stable_lock_id_set())
    }

    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState {
        self.state.kernel_view_locking_state
    }

    pub open spec fn lock_entry_contains(
        &self,
        lock_id: LockId,
        obj_id: KernelObjId,
    ) -> bool {
        self.held_lock_id_set().contains((lock_id, obj_id))
    }

    pub open spec fn lock_entry_contains_for(
        &self,
        lock_id: LockId,
        obj_id: KernelObjId,
        lock_id_mutable: bool,
    ) -> bool {
        if lock_id_mutable {
            self.lock_id_set().contains((lock_id, obj_id))
        } else {
            self.stable_lock_id_set().contains((lock_id, obj_id))
        }
    }

    pub open spec fn lock_obj_contains(&self, obj_id: KernelObjId) -> bool {
        exists|lock_id: LockId| self.lock_entry_contains(lock_id, obj_id)
    }

    pub open spec fn stable_lock_obj_contains(&self, obj_id: KernelObjId) -> bool {
        exists|lock_id: LockId|
            self.stable_lock_id_set().contains((lock_id, obj_id))
    }

    /// Immutable-id objects are fresh when their exact pair is absent from the
    /// stable ledger.  For a dynamic-id object, freshness is object-sensitive
    /// across all ids in the dynamic ledger.
    pub open spec fn lock_entry_fresh(
        &self,
        lock_id: LockId,
        obj_id: KernelObjId,
        lock_id_mutable: bool,
    ) -> bool {
        if lock_id_mutable {
            !exists|held_lock_id: LockId|
                self.lock_id_set().contains((held_lock_id, obj_id))
        } else {
            !self.stable_lock_id_set().contains((lock_id, obj_id))
        }
    }

    /// `lock_id` is strictly greater than every dynamic or stable id held.
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool {
        &&& forall|held: HeldLock|
                #![trigger self.lock_id_set().contains(held)]
                self.lock_id_set().contains(held)
                ==> lock_id.spec_gt(held.0)
        &&& forall|held: HeldLock|
                #![trigger self.stable_lock_id_set().contains(held)]
                self.stable_lock_id_set().contains(held)
                ==> lock_id.spec_gt(held.0)
    }

    pub open spec fn held_lock_majors_lt(&self, major: LockMajorId) -> bool {
        &&& forall|held: HeldLock|
                #![trigger self.lock_id_set().contains(held)]
                self.lock_id_set().contains(held) ==> held.0.major < major
        &&& forall|held: HeldLock|
                #![trigger self.stable_lock_id_set().contains(held)]
                self.stable_lock_id_set().contains(held) ==> held.0.major < major
    }

    pub open spec fn held_lock_majors_le(&self, major: LockMajorId) -> bool {
        &&& forall|held: HeldLock|
                #![trigger self.lock_id_set().contains(held)]
                self.lock_id_set().contains(held) ==> held.0.major <= major
        &&& forall|held: HeldLock|
                #![trigger self.stable_lock_id_set().contains(held)]
                self.stable_lock_id_set().contains(held) ==> held.0.major <= major
    }

    pub open spec fn holds_no_allocator_locks(&self, page_size: PageSize) -> bool {
        &&& forall|held: HeldLock|
                #![trigger self.lock_id_set().contains(held)]
                self.lock_id_set().contains(held) ==> match held.1 {
                    KernelObjId::AllocatorQuota(size, _) => size != page_size,
                    KernelObjId::AllocatorCache(size, _, _) => size != page_size,
                    KernelObjId::AllocatorGlobalPoll(size, _) => size != page_size,
                    _ => true,
                }
        &&& forall|held: HeldLock|
                #![trigger self.stable_lock_id_set().contains(held)]
                self.stable_lock_id_set().contains(held) ==> match held.1 {
                    KernelObjId::AllocatorQuota(size, _) => size != page_size,
                    KernelObjId::AllocatorCache(size, _, _) => size != page_size,
                    KernelObjId::AllocatorGlobalPoll(size, _) => size != page_size,
                    _ => true,
                }
    }

    pub proof fn lemma_lock_id_eq_imply_acyclic_eq(&self)
        ensures
            forall|lock_id1: LockId, lock_id2: LockId|
                #![trigger self.lock_id_acyclic(lock_id1), self.lock_id_acyclic(lock_id2)]
                {
                    &&& lock_id1.container == lock_id2.container
                    &&& lock_id1.process == lock_id2.process
                    &&& lock_id1.major == lock_id2.major
                    &&& lock_id1.minor == lock_id2.minor
                }
                ==>
                self.lock_id_acyclic(lock_id1) == self.lock_id_acyclic(lock_id2)
    {
    }

    /// TCB: close the Acquire phase without changing either held-lock ledger.
    #[verifier::external_body]
    pub proof fn enter_kernel_view_release(tracked &mut self)
        requires
            old(self).kernel_view_locking_state() is Acquire,
        ensures
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() is Release,
            final(self).lock_id_set() == old(self).lock_id_set(),
            final(self).stable_lock_id_set() == old(self).stable_lock_id_set(),
    {
        unimplemented!()
    }

    /// TCB: replace one held object's dynamic id during Release.
    #[verifier::external_body]
    pub proof fn update_lock_id(
        tracked &mut self,
        obj_id: KernelObjId,
        old_lock_id: LockId,
        new_lock_id: LockId,
    )
        requires
            old(self).kernel_view_locking_state() is Release,
            old(self).lock_id_set().contains((old_lock_id, obj_id)),
        ensures
            final(self).lock_id_set()
                == old(self).lock_id_set()
                    .remove((old_lock_id, obj_id))
                    .insert((new_lock_id, obj_id)),
            final(self).stable_lock_id_set() == old(self).stable_lock_id_set(),
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state()
                == old(self).kernel_view_locking_state(),
    {
        unimplemented!()
    }
}

pub open spec fn lock_ensures<T>(
    old: &LocalContext,
    new: &LocalContext,
    value: T,
    lock_id: LockId,
    obj_id: KernelObjId,
    lock_id_mutable: bool,
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& new.kernel_view_locking_state() is Acquire
    &&& if lock_id_mutable {
            &&& new.lock_id_set() == old.lock_id_set().insert((lock_id, obj_id))
            &&& new.stable_lock_id_set() == old.stable_lock_id_set()
        } else {
            &&& new.lock_id_set() == old.lock_id_set()
            &&& new.stable_lock_id_set()
                == old.stable_lock_id_set().insert((lock_id, obj_id))
        }
}

pub open spec fn unlock_ensures<T>(
    old: &LocalContext,
    new: &LocalContext,
    value: T,
    lock_token: LockToken,
    obj_id: KernelObjId,
    lock_id: LockId,
    lock_id_mutable: bool,
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& old.kernel_view_locking_state() is Acquire
        ==> new.kernel_view_locking_state() is Release
    &&& old.kernel_view_locking_state() is Release
        ==> new.kernel_view_locking_state() is Release
    &&& if lock_id_mutable {
            &&& new.lock_id_set() == old.lock_id_set().remove((lock_id, obj_id))
            &&& new.stable_lock_id_set() == old.stable_lock_id_set()
        } else {
            &&& new.lock_id_set() == old.lock_id_set()
            &&& new.stable_lock_id_set()
                == old.stable_lock_id_set().remove((lock_id, obj_id))
        }
}

/// The dynamic ledger follows the payload's current id.  The stable ledger
/// uses the immutable ordering id recorded when the lock was acquired.
pub open spec fn lock_id_for_unlock(
    current_lock_id: LockId,
    acquired_lock_id: LockId,
    lock_id_mutable: bool,
) -> LockId {
    if lock_id_mutable { current_lock_id } else { acquired_lock_id }
}

}

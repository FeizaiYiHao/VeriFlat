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

/// Per-thread ledger of held locks.
///
/// Every entry records the exact ordering id and object used by the physical
/// lock. If a held object's dynamic ordering id changes during Release, the
/// corresponding pair is replaced explicitly by `update_lock_id`.
pub tracked struct LocalContext {
    thread_id: LockThreadId,
    lock_id_set: Set<HeldLock>,
    state: LCtxtState,
}

impl LocalContext {
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set
    }

    pub open spec fn held_lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set()
    }

    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState {
        self.state.kernel_view_locking_state
    }

    pub open spec fn lock_entry_contains(
        &self,
        lock_id: LockId,
        obj_id: KernelObjId,
    ) -> bool {
        self.lock_id_set().contains((lock_id, obj_id))
    }

    pub open spec fn lock_obj_contains(&self, obj_id: KernelObjId) -> bool {
        exists|lock_id: LockId| self.lock_entry_contains(lock_id, obj_id)
    }


    /// `lock_id` is strictly greater than every held id.
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> lock_id.spec_gt(held.0)
    }

    pub open spec fn held_lock_majors_lt(&self, major: LockMajorId) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> held.0.major < major
    }

    pub open spec fn held_lock_majors_le(&self, major: LockMajorId) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> held.0.major <= major
    }

    pub open spec fn holds_no_allocator_locks(&self, page_size: PageSize) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> match held.1 {
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

    /// TCB: close the Acquire phase without changing the held-lock ledger.
    #[verifier::external_body]
    pub proof fn enter_kernel_view_release(tracked &mut self)
        requires
            old(self).kernel_view_locking_state() is Acquire,
        ensures
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() is Release,
            final(self).lock_id_set() == old(self).lock_id_set(),
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
            final(self).thread_id() == old(self).thread_id(),
            final(self).lock_id_set().contains((new_lock_id, obj_id)),
            old_lock_id != new_lock_id ==>
                !final(self).lock_id_set().contains((old_lock_id, obj_id)),
            forall|held: HeldLock|
                #![trigger final(self).lock_entry_contains(held.0, held.1)]
                held.1 != obj_id
                ==> final(self).lock_entry_contains(held.0, held.1)
                    == old(self).lock_entry_contains(held.0, held.1),
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
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& new.kernel_view_locking_state() is Acquire
    &&& new.lock_id_set() == old.lock_id_set().insert((lock_id, obj_id))
}

pub open spec fn unlock_ensures<T>(
    old: &LocalContext,
    new: &LocalContext,
    value: T,
    lock_token: LockToken,
    obj_id: KernelObjId,
    lock_id: LockId,
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& old.kernel_view_locking_state() is Acquire
        ==> new.kernel_view_locking_state() is Release
    &&& old.kernel_view_locking_state() is Release
        ==> new.kernel_view_locking_state() is Release
    &&& new.lock_id_set() == old.lock_id_set().remove((lock_id, obj_id))
    &&& !new.lock_id_set().contains((lock_id, obj_id))
    &&& forall|held: HeldLock|
        #![trigger new.lock_entry_contains(held.0, held.1)]
        held.1 != obj_id
        ==> new.lock_entry_contains(held.0, held.1)
            == old.lock_entry_contains(held.0, held.1)
}

}

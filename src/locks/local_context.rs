use vstd::prelude::*;
use crate::*;
use core::sync::atomic::*;
use vstd::std_specs::cmp::*;

verus! {

pub ghost enum LCtxtLockState{
    Acquire,
    Release,
}
pub tracked struct LCtxtState{  
    pub kernel_view_locking_state: LCtxtLockState,
    pub user_view_locking_state: LCtxtLockState,
}
pub tracked struct LocalContext{
    thread_id: LockThreadId,
    lock_map: Map<KernelObjId, LockId>,
    state: LCtxtState,
}

impl LocalContext{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }
    pub closed spec fn lock_map(&self) -> Map<KernelObjId, LockId>{
        self.lock_map
    }
    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState{
        self.state.kernel_view_locking_state
    }    
    pub closed spec fn user_view_locking_state(&self) -> LCtxtLockState{
        self.state.user_view_locking_state
    }

    pub open spec fn wf(&self) -> bool{
        true
    }

    /// Predicate: `lock_id` is strictly greater than every lock id currently
    /// held in `lock_map`. This is the deadlock-freedom check: a thread may
    /// only acquire a lock whose id exceeds every id it already holds.
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool{
        forall|k: KernelObjId|
            #![trigger self.lock_map().dom().contains(k)]
            #![trigger self.lock_map()[k]]
            self.lock_map().dom().contains(k) ==> lock_id.spec_gt(self.lock_map()[k])
    }

    /// Predicate: `obj_id` is not already a key in `lock_map`. Required at
    /// every wlock to prevent the user from silently dropping a held lock id
    /// by re-using its key.
    pub open spec fn obj_id_fresh(&self, obj_id: KernelObjId) -> bool{
        !self.lock_map().dom().contains(obj_id)
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
}

    pub open spec fn lock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_id: LockId, obj_id: KernelObjId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        new.kernel_view_locking_state() is Acquire
        &&&
        new.user_view_locking_state() == old.user_view_locking_state()
        &&&
        new.lock_map() =~= old.lock_map().insert(obj_id, lock_id)
    }

    /// Precondition for releasing any lock guarded by `T`.
    ///
    /// User-visible locks may only be released after the syscall has
    /// manually flipped `user_view_locking_state` to `Release`. That flip is
    /// the linearization point and captures `old_user`; without it the
    /// syscall's user-view spec is incomplete.
    pub open spec fn unlock_requires<T:LockUserVisibilityTrait>(old:&LocalContext) -> bool{
        T::is_user_visible() ==> old.user_view_locking_state() is Release
    }

    pub open spec fn unlock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_id: LockId, obj_id: KernelObjId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        old.kernel_view_locking_state() is Acquire ==> new.kernel_view_locking_state() is Release
        &&&
        old.kernel_view_locking_state() is Release ==> new.kernel_view_locking_state() is Release
        &&&
        new.user_view_locking_state() == old.user_view_locking_state()
        &&&
        new.lock_map() =~= old.lock_map().remove(obj_id)
    }

}
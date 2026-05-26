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
    lock_seq: Seq<LockId>,
    state: LCtxtState,
}

impl LocalContext{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }
    pub closed spec fn lock_seq(&self) -> Seq<LockId>{
        self.lock_seq
    }
    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState{
        self.state.kernel_view_locking_state
    }    
    pub closed spec fn user_view_locking_state(&self) -> LCtxtLockState{
        self.state.user_view_locking_state
    }
    pub open spec fn wf(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger self.lock_seq()[i]] 
            1<=i<self.lock_seq().len() 
            ==> 
            self.lock_seq()[i] > self.lock_seq()[i - 1]
    }            
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool{
        |||
        self.lock_seq().len() == 0
        |||
        lock_id.spec_gt(self.lock_seq().last())
    }
}

    pub open spec fn lock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_id: LockId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        new.kernel_view_locking_state() is Acquire
        &&&
        new.user_view_locking_state() == old.user_view_locking_state()
        &&&
        new.lock_seq() =~= old.lock_seq().push(lock_id)
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

    pub open spec fn unlock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_id: LockId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        old.kernel_view_locking_state() is Acquire ==> new.kernel_view_locking_state() is Release
        &&&
        old.kernel_view_locking_state() is Release ==> new.kernel_view_locking_state() is Release
        &&&
        new.user_view_locking_state() == old.user_view_locking_state()
        &&&
        new.lock_seq() =~= old.lock_seq().remove_value(lock_id)
    }

}
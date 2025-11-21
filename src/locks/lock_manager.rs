use vstd::prelude::*;
use crate::define::*;
use core::sync::atomic::*;

use super::LockPerm;

verus! {

pub enum LMState{
    Lock,
    Unlock,
    ReLock,
}
pub struct LockManager{
    thread_id: LockThreadId,
    lock_seq: Seq<LockId>,
    state: LMState,
}

impl LockManager{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }
    pub closed spec fn lock_seq(&self) -> Seq<LockId>{
        self.lock_seq
    }
    pub closed spec fn state(&self) -> LMState{
        self.state
    }
    pub open spec fn wf(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger self.lock_seq()[i]] 
            1<=i<self.lock_seq().len() 
            ==> 
            self.lock_seq()[i].greater(self.lock_seq()[i - 1])
    }
    pub open spec fn lock_id_valid(&self, lock_id: LockId) -> bool{
        |||
        self.lock_seq().len() == 0
        |||
        lock_id.greater(self.lock_seq().last())
    }
}

    pub open spec fn lock_ensures(old:&LockManager, new:&LockManager, lock_id: LockId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        old.state() is Lock ==> new.state() is Lock
        &&&
        old.state() is Unlock ==> new.state() is ReLock
        &&&
        old.state() is ReLock ==> new.state() is ReLock 
        &&&
        new.lock_seq() =~= old.lock_seq().push(lock_id)
    }

    pub open spec fn unlock_ensures(old:&LockManager, new:&LockManager, lock_id: LockId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        old.state() is Lock ==> new.state() is Unlock
        &&&
        old.state() is Unlock ==> new.state() is Unlock
        &&&
        old.state() is ReLock ==> new.state() is Unlock 
        &&&
        new.lock_seq() =~= old.lock_seq().remove_value(lock_id)
    }

}
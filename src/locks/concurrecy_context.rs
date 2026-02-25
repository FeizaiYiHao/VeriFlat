use vstd::prelude::*;
use crate::define::*;
use core::sync::atomic::*;
use vstd::std_specs::cmp::*;

use super::LockPerm;

verus! {

pub enum CCtxtLockState{
    Lock,
    Unlock,
    // ReLock,
}
pub struct CCtxtState{  
    pub locking_state: CCtxtLockState,
    pub serial_num: nat,
}
pub struct ConcurrencyContext{
    thread_id: LockThreadId,
    lock_seq: Seq<LockId>,
    state: CCtxtState,
}

impl ConcurrencyContext{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }
    pub closed spec fn lock_seq(&self) -> Seq<LockId>{
        self.lock_seq
    }
    pub closed spec fn locking_state(&self) -> CCtxtLockState{
        self.state.locking_state
    }
    pub closed spec fn locking_serial_num(&self) -> nat{
        self.state.serial_num
    }
    pub open spec fn wf(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger self.lock_seq()[i]] 
            1<=i<self.lock_seq().len() 
            ==> 
            self.lock_seq()[i] > self.lock_seq()[i - 1]
    }
    pub open spec fn lock_id_valid(&self, lock_id: LockId) -> bool{
        |||
        self.lock_seq().len() == 0
        |||
        lock_id > self.lock_seq().last()
    }
}

    pub open spec fn lock_ensures(old:&ConcurrencyContext, new:&ConcurrencyContext, lock_id: LockId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        old.locking_state() is Lock ==> new.locking_state() is Lock
        &&&
        old.locking_state() is Unlock ==> new.locking_state() is Lock
        &&&
        old.locking_state() is Lock ==> old.locking_serial_num() == new.locking_serial_num()
        &&&
        old.locking_state() is Unlock ==> old.locking_serial_num() + 1 == new.locking_serial_num()
        &&&
        new.lock_seq() =~= old.lock_seq().push(lock_id)
    }

    pub open spec fn unlock_ensures(old:&ConcurrencyContext, new:&ConcurrencyContext, lock_id: LockId) -> bool{
        &&&
        new.thread_id() == old.thread_id()
        &&&
        old.locking_state() is Lock ==> new.locking_state() is Unlock
        &&&
        old.locking_state() is Unlock ==> new.locking_state() is Unlock
        &&&
        old.locking_serial_num() + 1 == new.locking_serial_num()
        &&&
        new.lock_seq() =~= old.lock_seq().remove_value(lock_id)
    }

}
use vstd::prelude::*;
use crate::define::*;
use core::sync::atomic::*;

use super::LockPerm;

verus! {

pub tracked struct ThreadIdPerm{
}

impl ThreadIdPerm{
    pub uninterp spec fn id(&self) -> LockThreadId;
}

pub struct LockManager{
    thread_id: LockThreadId,
    lock_seq: Seq<LockId>,
}

impl LockManager{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }
    pub closed spec fn lock_seq(&self) -> Seq<LockId>{
        self.lock_seq
    }
    pub open spec fn wf(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger self.lock_seq()[i]] 
            1<=i<self.lock_seq().len() 
            ==> 
            self.lock_seq()[i].greater(self.lock_seq()[i - 1])
    }
}



}
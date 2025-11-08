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
}

impl LockManager{
    pub uninterp spec fn thread_id(&self) -> LockThreadId;
    pub uninterp spec fn lock_seq(&self) -> Seq<LockId>;
    pub open spec fn wf(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger self.lock_seq()[i]] 
            1<=i<self.lock_seq().len() 
            ==> 
            self.lock_seq()[i].greater(&self.lock_seq()[i - 1])
    }
}



}
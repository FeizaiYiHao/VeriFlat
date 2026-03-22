use vstd::prelude::*;
verus! {

use crate::*;

pub struct Scheduler{
    pub queue: LinkedList<RwLockThreadPtr, 233>,
    pub owning_container: RwLockContainerPtr, 
}

impl LockInvTrait for Scheduler {
    open spec fn inv(&self) -> bool {
        &&&
        self.queue.inv()
    }
}

}
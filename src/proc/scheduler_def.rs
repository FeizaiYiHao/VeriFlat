use vstd::prelude::*;
verus! {

use crate::*;

pub struct Scheduler{
    pub queue: LinkedList<RwLockThreadPtr, 233>,
    pub owning_container: RwLockContainerPtr, 
}

}
use vstd::prelude::*;
verus! {

use crate::*;

pub struct Endpoint {
    pub queue: LinkedList<RwLockThreadPtr, 233>,
    pub queue_state: EndpointState,
    pub rf_counter: usize,
    pub owning_threads: Ghost<Set<(RwLockThreadPtr, EndpointIdx)>>,
    pub owning_container: RwLockContainerPtr,
}

impl LockInvTrait for Endpoint {
    open spec fn inv(&self) -> bool {
        &&&
        self.queue.wf()
    }
}

} // verus!

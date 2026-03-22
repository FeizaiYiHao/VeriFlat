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


impl Endpoint {
    pub open spec fn rf_counter_is_full(&self) -> bool {
        self.rf_counter == usize::MAX
    }

    pub open spec fn get_owning_threads(&self) -> Set<(RwLockThreadPtr, EndpointIdx)> {
        self.owning_threads@
    }
}

} // verus!

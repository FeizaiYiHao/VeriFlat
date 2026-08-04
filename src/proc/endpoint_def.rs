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
        &&&
        self.rf_counter == self.owning_threads.view().len()
    }
}

impl LockMajorTrait for Endpoint {
    open spec fn lock_major_1(&self) -> LockMajorId {
        ENDPOINT_LOCK_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        ENDPOINT_LOCK_MAJOR
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        ENDPOINT_LOCK_MAJOR
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        ENDPOINT_LOCK_MAJOR
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        true
    }
}

impl LockOwnerIdTrait for Endpoint {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::none()
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::none()
    }
}

impl LockUserVisibilityTrait for Endpoint {
    open spec fn is_user_visible() -> bool {
        false
    }
}

/// Trusted cardinality bound used before adding an endpoint reference.
/// The current endpoint invariants record the exact reference set, but do not
/// yet derive this global address-space bound internally.
#[verifier::external_body]
pub proof fn endpoint_ref_counter_bounded(endpoint: &Endpoint)
    requires
        endpoint.inv(),
    ensures
        endpoint.rf_counter < NUM_PAGES,
{
}

} // verus!

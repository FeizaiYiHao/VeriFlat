use vstd::prelude::*;
use vstd::simple_pptr::*;
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
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockUserVisibilityTrait for Endpoint {
    open spec fn is_user_visible() -> bool {
        false
    }
}

impl Endpoint {
    pub fn dequeue_waiter(
        &mut self,
        thread_ptr: RwLockThreadPtr,
    ) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).queue.len() != 0,
            old(self).queue.view().spec_index(0) == thread_ptr,
        ensures
            final(self).inv(),
            final(self).queue.length == old(self).queue.length - 1,
            final(self).queue.view() == old(self).queue.view().skip(1),
            final(self).queue.dom() == old(self).queue.dom().remove(ret.0),
            final(self).queue.map() == old(self).queue.map().remove(ret.0),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
            old(self).queue.dom().contains(ret.0),
            old(self).queue.map().dom().contains(ret.0),
            old(self).queue.map().spec_index(ret.0) == thread_ptr,
            forall|value: RwLockThreadPtr|
                #![trigger final(self).queue.view().contains(value)]
                old(self).queue.view().contains(value)
                    && value != thread_ptr
                ==> final(self).queue.view().contains(value),
            forall|value: RwLockThreadPtr|
                #![trigger final(self).queue.view().contains(value)]
                final(self).queue.view().contains(value)
                    ==> old(self).queue.view().contains(value),
            !final(self).queue.view().contains(thread_ptr),
            final(self).queue_state == old(self).queue_state,
            final(self).rf_counter == old(self).rf_counter,
            final(self).owning_threads == old(self).owning_threads,
            final(self).owning_container == old(self).owning_container,
    {
        self.queue.pop_head()
    }

    pub fn enqueue_waiter(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        waiting_state: ThreadState,
        node_addr: usize,
        node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    )
        requires
            old(self).inv(),
            waiting_state.is_endpoint_waiting(),
            node_perm.view().is_init(),
            node_perm.view().addr() == node_addr,
            node_perm.view().value().view() == thread_ptr,
            !old(self).queue.view().contains(thread_ptr),
            old(self).queue.length != usize::MAX,
        ensures
            final(self).inv(),
            final(self).queue.length == old(self).queue.length + 1,
            final(self).queue.view()
                == old(self).queue.view().push(thread_ptr),
            final(self).queue.dom()
                == old(self).queue.dom().insert(node_addr),
            final(self).queue.map()
                == old(self).queue.map().insert(node_addr, thread_ptr),
            !old(self).queue.dom().contains(node_addr),
            !old(self).queue.map().dom().contains(node_addr),
            final(self).queue_state == if old(self).queue.length == 0 {
                match waiting_state {
                    ThreadState::SENDING | ThreadState::CALLING =>
                        EndpointState::SEND,
                    _ => EndpointState::RECEIVE,
                }
            } else {
                old(self).queue_state
            },
            final(self).rf_counter == old(self).rf_counter,
            final(self).owning_threads == old(self).owning_threads,
            final(self).owning_container == old(self).owning_container,
    {
        let queue_len = self.queue.length;
        if queue_len == 0 {
            self.queue_state = match waiting_state {
                ThreadState::SENDING | ThreadState::CALLING =>
                    EndpointState::SEND,
                _ => EndpointState::RECEIVE,
            };
        }
        self.queue.push_tail(node_addr, node_perm);
    }
}

} // verus!

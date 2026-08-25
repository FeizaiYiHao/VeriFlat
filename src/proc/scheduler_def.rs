use vstd::prelude::*;
use vstd::simple_pptr::*;
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

impl LockMajorTrait for Scheduler {
    open spec fn lock_major_1(&self) -> LockMajorId {
        SCHEDULER_LOCK_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        233
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

impl LockOwnerIdTrait for Scheduler {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockUserVisibilityTrait for Scheduler {
    open spec fn is_user_visible() -> bool {
        false
    }
}

impl Scheduler {
    pub fn enqueue_scheduled_thread(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        node_addr: usize,
        node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    )
        requires
            old(self).inv(),
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
            forall|value: RwLockThreadPtr|
                #![trigger final(self).queue.view().contains(value)]
                old(self).queue.view().contains(value)
                    ==> final(self).queue.view().contains(value),
            final(self).owning_container == old(self).owning_container,
    {
        self.queue.push_tail(node_addr, node_perm);
    }
}

}

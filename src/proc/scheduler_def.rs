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
        true
    }
}

impl Scheduler {
    pub fn new_boot_root(
        scheduler_ptr: RwLockSchedulerPtr,
        owning_container: RwLockContainerPtr,
        root_thread: RwLockThreadPtr,
        thread_node_addr: usize,
        thread_node_perm:
            Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    ) -> (ret: Self)
        requires
            thread_node_perm.view().is_init(),
            thread_node_perm.view().addr() == thread_node_addr,
            thread_node_perm.view().value().view() == root_thread,
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            ret.queue.view() =~= seq![root_thread],
            ret.queue.map()
                =~= Map::<usize, RwLockThreadPtr>::empty()
                    .insert(thread_node_addr, root_thread),
            ret.queue.container_depth == Some(0),
            ret.queue.lock_minor() == scheduler_ptr,
    {
        let mut ret = Self::new_empty(scheduler_ptr, owning_container, 0);
        ret.enqueue_scheduled_thread(root_thread, thread_node_addr, thread_node_perm);
        ret
    }

    pub fn new_empty(scheduler_ptr: RwLockSchedulerPtr, owning_container: RwLockContainerPtr, container_depth: usize) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            ret.queue.view() == Seq::<RwLockThreadPtr>::empty(),
            ret.queue.map() == Map::<usize, RwLockThreadPtr>::empty(),
            ret.queue.length == 0,
            ret.queue.container_depth == Some(container_depth),
            ret.queue.lock_minor() == scheduler_ptr,
    {
        Self {
            queue: LinkedList::new(Some(container_depth), Some(scheduler_ptr)),
            owning_container,
        }
    }

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
            final(self).queue.container_depth == old(self).queue.container_depth,
            final(self).queue.lock_minor() == old(self).queue.lock_minor(),
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

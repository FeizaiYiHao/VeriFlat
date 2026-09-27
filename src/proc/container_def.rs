use vstd::prelude::*;
verus! {
use crate::*;
use core::mem::offset_of;

// Each container uses a 2 MiB pages
#[repr(C)]
pub struct Container {
    pub parent_linkedlist_node: ExternalNode<RwLockContainerPtr>,
    pub children: LinkedList<RwLockContainerPtr, 233>,

    pub root_process: RwLockProcessPtr, // Not Option Maybe? Container with no process should be killed
    pub owned_processes: Ghost<Set<RwLockProcessPtr>>,
    pub owned_endpoints: Ghost<Set<RwLockEndpointPtr>>,
    pub owned_pages: Ghost<Set<PagePtr>>,
}
pub struct ContainerRO {
    pub parent: Option<RwLockContainerPtr>,
    pub depth: usize,
    pub scheduler: RwLockSchedulerPtr,
    pub pcid_allocator: RwLockPcidAllocatorPtr,
    pub cpu_set: RwLockCpuSetPtr,
    pub allocator_ptr_4k: RwLockPageAllocatorPtr,
    pub allocator_ptr_2m: RwLockPageAllocatorPtr,
    pub allocator_ptr_1g: RwLockPageAllocatorPtr,
}

/// Lock-free ghost state associated with a container's `RwLock`.
pub struct ContainerGhost {
    pub uppertree_seq: Ghost<Seq<RwLockContainerPtr>>,
    pub subtree_set: Ghost<Set<RwLockContainerPtr>>,
    pub owned_threads: Ghost<Set<RwLockThreadPtr>>,
    pub owned_indirect_threads: Ghost<Set<RwLockThreadPtr>>,
}

pub ghost struct ContainerU {
    pub lock_state: LockStateU,
    pub children: Seq<RwLockContainerPtr>,
    pub uppertree_seq: Seq<RwLockContainerPtr>,
    pub subtree_set: Set<RwLockContainerPtr>,
    pub root_process: RwLockProcessPtr,
    pub owned_processes: Set<RwLockProcessPtr>,
    pub owned_threads: Set<RwLockThreadPtr>,
    pub owned_endpoints: Set<RwLockEndpointPtr>,
    pub owned_pages: Set<PagePtr>,
    pub parent: Option<RwLockContainerPtr>,
    pub depth: usize,
    pub scheduler: Seq<RwLockThreadPtr>,
    pub cpu_set: RwLockCpuSetPtr,
    pub free_pcids: Set<Pcid>,
    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,

    pub killed: bool,
}

impl LockInvTrait for Container {
    open spec fn inv(&self) -> bool {
        &&&
        self.wf()
    }
}

impl Container{
    pub fn new_boot_root(
        container_ptr: RwLockContainerPtr,
        root_process: RwLockProcessPtr,
        root_endpoint: RwLockEndpointPtr,
        owned_pages: Ghost<Set<PagePtr>>,
    ) -> (ret: Self)
        ensures
            ret.inv(),
            ret.parent_linkedlist_node.is_init(),
            ret.children.view()
                == Seq::<RwLockContainerPtr>::empty(),
            ret.children.map()
                == Map::<usize, RwLockContainerPtr>::empty(),
            ret.root_process == root_process,
            ret.owned_processes.view()
                =~= set![root_process],
            ret.owned_endpoints.view()
                =~= set![root_endpoint],
            ret.owned_pages == owned_pages,
    {
        let mut ret = Self::new_staged(container_ptr, root_process, 0);
        ret.owned_processes = Ghost(
            Set::empty().insert(root_process),
        );
        ret.owned_endpoints = Ghost(
            Set::empty().insert(root_endpoint),
        );
        ret.owned_pages = owned_pages;
        ret
    }

    pub fn new_staged(container_ptr: RwLockContainerPtr, root_process: RwLockProcessPtr, depth: usize) -> (ret: Self)
        ensures
            ret.inv(),
            ret.parent_linkedlist_node.is_init(),
            ret.children.view() == Seq::<RwLockContainerPtr>::empty(),
            ret.children.map() == Map::<usize, RwLockContainerPtr>::empty(),
            ret.root_process == root_process,
            ret.owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
            ret.owned_endpoints.view() == Set::<RwLockEndpointPtr>::empty(),
            ret.owned_pages.view() == Set::<PagePtr>::empty(),
    {
        Self {
            parent_linkedlist_node: ExternalNode::new(container_ptr),
            children: LinkedList::new(Some(depth), Some(container_ptr)),
            root_process,
            owned_processes: Ghost(Set::empty()),
            owned_endpoints: Ghost(Set::empty()),
            owned_pages: Ghost(Set::empty()),
        }
    }

    pub fn add_owned_process(&mut self, process_ptr: RwLockProcessPtr)
        requires
            old(self).inv(),
            old(self).root_process_in_processes(),
        ensures
            final(self).inv(),
            *final(self) == (Container {
                owned_processes: final(self).owned_processes,
                ..*old(self)
            }),
            final(self).owned_processes.view()
                == old(self).owned_processes.view().insert(process_ptr),
    {
        self.owned_processes =
            Ghost(self.owned_processes.view().insert(process_ptr));
    }

    pub open spec fn wf(&self) -> bool {
        &&&
        self.children.inv()
        &&&
        (self.owned_processes.view().is_empty() || self.root_process_in_processes())
    }

    pub open spec fn root_process_in_processes(&self) -> bool {
        &&&
        self.owned_processes.view().contains(self.root_process)
    }
}

impl LockMajorTrait for Container {
    open spec fn lock_major_1(&self) -> LockMajorId {
        CONTAINER_LOCK_MAJOR
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

impl LockUserVisibilityTrait for Container{
    open spec fn is_user_visible() -> bool {
        true
    }
}

impl LockOwnerIdTrait for Container{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockOwnerIdTrait for ContainerRO{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}
} // verus!

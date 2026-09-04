use vstd::prelude::*;
verus! {

use crate::*;
use core::mem::offset_of;

// Each container uses a 2 MiB pages
#[repr(C)]
pub struct Container {
    pub parent_linkedlist_node: ExternalNode<RwLockContainerPtr>,
    pub children: LinkedList<RwLockContainerPtr, 233>,
    pub uppertree_seq: Ghost<Seq<RwLockContainerPtr>>,
    pub subtree_set: Ghost<Set<RwLockContainerPtr>>,

    pub root_process: RwLockProcessPtr, // Not Option Maybe? Container with no process should be killed
    pub owned_processes: Ghost<Set<RwLockProcessPtr>>,
    pub owned_cpus: ArraySet<NUM_CPUS>,
    pub owned_endpoints: Ghost<Set<RwLockEndpointPtr>>,
    pub owned_pages: Ghost<Set<PagePtr>>,
}
pub struct ContainerRO {
    pub parent: Option<RwLockContainerPtr>,
    pub depth: usize,
    pub scheduler: RwLockSchedulerPtr,
    pub pcid_allocator: RwLockPcidAllocatorPtr,
    pub allocator_ptr_4k: RwLockPageAllocatorPtr,
    pub allocator_ptr_2m: RwLockPageAllocatorPtr,
    pub allocator_ptr_1g: RwLockPageAllocatorPtr,
}

/// Lock-free ghost state associated with a container's `RwLock`.
pub struct ContainerGhost {
    pub owned_threads: Ghost<Set<RwLockThreadPtr>>,
    pub owned_indirect_threads: Ghost<Set<RwLockThreadPtr>>,
}

pub ghost struct ContainerU {
    pub children: LinkedList<RwLockContainerPtr, 233>,
    pub uppertree_seq: Ghost<Seq<RwLockContainerPtr>>,
    pub subtree_set: Ghost<Set<RwLockContainerPtr>>,
    pub root_process: RwLockProcessPtr,
    pub owned_processes: Ghost<Set<RwLockProcessPtr>>,
    pub owned_cpus: ArraySet<NUM_CPUS>,
    pub owned_threads: Ghost<Set<RwLockThreadPtr>>,
    pub owned_endpoints: Ghost<Set<RwLockEndpointPtr>>,
    pub owned_pages: Ghost<Set<PagePtr>>,
    pub parent: Option<RwLockContainerPtr>,    
    pub depth: usize,
    pub scheduler: RwLockSchedulerPtr,
    pub pcid_allocator: RwLockPcidAllocatorPtr,
    pub allocator_ptr_4k: RwLockPageAllocatorPtr,
    pub allocator_ptr_2m: RwLockPageAllocatorPtr,
    pub allocator_ptr_1g: RwLockPageAllocatorPtr,

    pub killed: bool,
}

impl LockInvTrait for Container {
    open spec fn inv(&self) -> bool {
        &&&
        self.wf()
    }
}

impl Container{
    pub open spec fn wf(&self) -> bool {
        &&&
        self.children.inv()
        &&&
        self.owned_cpus.wf()
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

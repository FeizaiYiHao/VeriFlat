use vstd::prelude::*;
verus! {

use crate::*;

pub struct PcidIoidAllocator{
    pub ref_counters: Array<usize, PCID_MAX>,
    pub id_to_proc: Ghost<Seq<Set<RwLockProcessPtr>>>,
}

// Each container uses a 2 MiB pages
pub struct Container {
    pub parent: Option<RwLockContainerPtr>,
    pub parent_linkedlist_node: ExternalNode<RwLockContainerPtr>,
    pub children: LinkedList<RwLockContainerPtr, 233>,
    pub depth: usize,
    pub uppertree_seq: Ghost<Seq<RwLockContainerPtr>>,
    pub subtree_set: Ghost<Set<RwLockContainerPtr>>,

    pub root_process: Option<RwLockProcessPtr>,
    pub owned_procs: Ghost<Set<RwLockProcessPtr>>,
    pub pcid_allocator: PcidIoidAllocator,
    pub ioid_allocator: PcidIoidAllocator,

    pub owned_cpus: ArraySet<NUM_CPUS>,

    pub owned_threads: Ghost<Set<RwLockThreadPtr>>,

    pub scheduler: RwLockSchedulerPtr,

    pub owned_endpoints: Ghost<Set<RwLockEndpointPtr>>,

    pub allocator_ptr_4k: RwLockPageAllocatorPtr,
    pub allocator_ptr_2m: RwLockPageAllocatorPtr,
    pub allocator_ptr_1g: RwLockPageAllocatorPtr,
}

impl LockInvTrait for Container {
    open spec fn inv(&self) -> bool {
        &&&
        self.children.inv()
        &&&
        self.owned_cpus.wf()
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

} // verus!

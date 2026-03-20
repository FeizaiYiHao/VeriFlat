use vstd::prelude::*;
verus! {

use crate::*;

pub struct Container {
    pub parent: Option<RwLockContainerPtr>,
    pub parent_rev_ptr: Option<usize>,
    pub children: LinkedList<RwLockContainerPtr, 233>,
    pub depth: usize,
    pub root_process: Option<RwLockProcessPtr>,
    pub allocator_ptr: RwLockPageAllocatorPtr,
    pub owned_cpus: ArraySet<NUM_CPUS>,

    pub uppertree_seq: Ghost<Seq<RwLockContainerPtr>>,
    pub subtree_set: Ghost<Set<RwLockContainerPtr>>,
    pub owned_procs: Ghost<Set<RwLockProcessPtr>>,
    pub owned_endpoints: Ghost<Set<RwLockEndpointPtr>>,
    pub owned_threads: Ghost<Set<RwLockThreadPtr>>,

    //missing fields: scheduler
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

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

} // verus!

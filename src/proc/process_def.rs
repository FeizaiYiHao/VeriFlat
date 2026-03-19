use vstd::prelude::*;
verus! {

use crate::*;

pub struct Process {
    pub owning_container: RwLockContainerPtr,
    
    pub pcid: Pcid,
    pub ioid: Option<IOid>,
    pub owned_threads: LinkedList<RwLockThreadPtr, 233>,
    pub parent: Option<RwLockProcessPtr>,
    pub parent_rev_ptr: Option<usize>,
    pub children: LinkedList<RwLockProcessPtr, PROC_CHILD_LIST_LEN>,
    pub uppertree_seq: Ghost<Seq<RwLockProcessPtr>>,
    pub subtree_set: Ghost<Set<RwLockProcessPtr>>,
    pub depth: usize,
}

} // verus!
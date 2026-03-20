use vstd::prelude::*;
verus! {

use crate::*;

pub struct Process {
    pub owning_container: RwLockContainerPtr,
    
    pub pcid: Pcid,
    pub ioid: Option<IOid>,
    pub pagetable: RwLockPageTableRoot,
    pub iommu_table: RwLockPageTableRoot,


    pub parent: Option<RwLockProcessPtr>,
    pub parent_linkedlist_node: ExternalNode<RwLockProcessPtr>,
    pub children: LinkedList<RwLockProcessPtr, 233>,
    pub depth: usize,
    pub uppertree_seq: Ghost<Seq<RwLockProcessPtr>>,
    pub subtree_set: Ghost<Set<RwLockProcessPtr>>,

    pub owned_threads: LinkedList<RwLockThreadPtr, 233>,
}

} // verus!
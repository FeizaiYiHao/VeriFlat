use vstd::prelude::*;
verus! {

use crate::*;

pub struct PcidIoidAllocator{
    pub ref_counters: Array<usize, PCID_MAX>,
    pub id_to_proc: Ghost<Seq<Set<RwLockProcessPtr>>>,
}

// Each container uses a 2 MiB pages
#[repr(C)]
pub struct Container {
    pub parent: Option<RwLockContainerPtr>,
    pub parent_linkedlist_node: ExternalNode<RwLockContainerPtr>,
    pub children: LinkedList<RwLockContainerPtr, 233>,
    pub depth: usize,
    pub uppertree_seq: ArrayVec<RwLockContainerPtr, MAX_CONTAINER_TREE_DEPTH>,
    pub uppertree_seq_ghost: Ghost<Seq<RwLockContainerPtr>>,
    pub subtree_set: Ghost<Set<RwLockContainerPtr>>,

    pub root_process: RwLockProcessPtr, // Not Option Maybe? Container with no process should be killed 
    pub owned_processes: Ghost<Set<RwLockProcessPtr>>,
    pub pcid_allocator: PcidIoidAllocator,
    pub ioid_allocator: PcidIoidAllocator,

    pub owned_cpus: ArraySet<NUM_CPUS>,

    pub owned_threads: Ghost<Set<RwLockThreadPtr>>,

    pub scheduler: RwLockSchedulerPtr,

    pub owned_endpoints: Ghost<Set<RwLockEndpointPtr>>,

    pub owned_pages: Ghost<Set<PagePtr>>,

    pub allocator_ptr_4k: RwLockPageAllocatorPtr,
    pub allocator_ptr_2m: RwLockPageAllocatorPtr,
    pub allocator_ptr_1g: RwLockPageAllocatorPtr,

    pub read_only_external_node: ExternalReadOnlyNode<ContainerRO>,
}

pub struct ContainerRO {
    pub parent: Option<RwLockContainerPtr>,
}


impl LockInvTrait for Container {
    open spec fn inv(&self) -> bool {
        &&&
        self.wf()
    }
}

// #[verifier(external_body)]
// pub fn container_read_only_node_offset(ptr: RwLockContainerPtr, ) -> (ret:usize)
//     ensures
//         ret == self.
// {

// }

pub closed spec fn 

impl Container{
    pub open spec fn wf(&self) -> bool {
        &&&
        self.children.inv()
        &&&
        self.owned_cpus.wf()
        &&&
        self.no_parent_implies_linkedlist_node_init()
        &&&
        self.root_process_in_processes()
        &&&
        self.uppertree_seq.wf()
    }

    pub open spec fn no_parent_implies_linkedlist_node_init(&self) -> bool{
        &&&
        self.parent is None == self.parent_linkedlist_node.is_init()
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

} // verus!

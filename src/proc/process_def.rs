use vstd::prelude::*;
verus! {

use crate::*;

pub struct Process {
    pub pcid: Pcid,
    pub ioid: Option<IOid>,
    pub pagetable: RwLockPageTableRoot,
    pub iommu_table: Option<RwLockPageTableRoot>,

    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,

    pub parent_linkedlist_node: ExternalNode<RwLockProcessPtr>,
    pub children: LinkedList<RwLockProcessPtr, 233>,
    pub uppertree_seq: ArrayVec<RwLockContainerPtr, MAX_PROCESS_TREE_DEPTH>,
    pub subtree_set: Ghost<Set<RwLockProcessPtr>>,

    pub owned_threads: LinkedList<RwLockThreadPtr, 233>,
}

pub ghost struct ProcessU {
    pub pagetable: PageTable<PT_TYPE>,
    // pub iommu_table: Option<PageTable<IOMMU_TYPE>>,
    
    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,

    pub parent: Option<RwLockProcessPtr>,
    pub children: Seq<RwLockProcessPtr>,
    pub depth: usize,
    pub uppertree_seq: Seq<RwLockContainerPtr>,
    pub subtree_set: Set<RwLockProcessPtr>,

    pub owned_threads: Seq<RwLockThreadPtr>,

    pub killed: bool,
}

pub struct ProcessRO {
    pub owning_container: RwLockContainerPtr,
    pub container_depth: usize,
    pub parent: Option<RwLockProcessPtr>,    
    pub depth: usize,
    pub pagetable: RwLockPageTableRoot,
}


impl UserViewHasKillState for ProcessU {
    open spec fn killed(&self) -> bool {
        self.killed
    }
}

impl LockInvTrait for Process {
    open spec fn inv(&self) -> bool {
        self.wf()
    }
}
 
impl Process{
    pub open spec fn wf(&self) -> bool {
        &&&
        self.children.inv()
        &&&
        self.owned_threads.wf()
        &&&
        self.uppertree_seq.wf()
        &&&
        self.iommu_table_wf()
        &&&
        self.pagetable_iommutable_different()
        &&&
        self.at_least_one_thread()
    }
    pub open spec fn iommu_table_wf(&self) -> bool {
        &&&
        self.ioid is Some == self.iommu_table is Some
    }
    pub open spec fn pagetable_iommutable_different(&self) -> bool {
        &&&
        self.iommu_table is Some ==> self.iommu_table.unwrap() != self.pagetable
    }
    pub open spec fn at_least_one_thread(&self) -> bool{
        &&&
        self.owned_threads.len() != 0
    }
}

impl LockMajorTrait for Process {
    open spec fn lock_major_1(&self) -> LockMajorId {
        PROCESS_LOCK_MAJOR
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

impl LockUserVisibilityTrait for Process{
    open spec fn is_user_visible() -> bool {
        true
    }
}

impl LockOwnerIdTrait for Process{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockOwnerIdTrait for ProcessRO{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.depth)
    }
}
} // verus!
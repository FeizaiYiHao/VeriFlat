use vstd::prelude::*;
verus! {

use crate::*;

pub struct Process {
    pub pcid: Pcid,
    pub pagetable: RwLockPageTableRoot,
    pub iommu_table: Option<RwLockPageTableRoot>,
    pub pci_function_ref_counter: usize,
    pub owned_pci_functions: Ghost<Set<PciBdf>>,

    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,

    pub parent_linkedlist_node: ExternalNode<RwLockProcessPtr>,
    pub children: LinkedList<RwLockProcessPtr, 233>,

    pub owned_threads: LinkedList<RwLockThreadPtr, 233>,
}

pub struct ProcessGhost {
    pub uppertree_seq: Ghost<Seq<RwLockProcessPtr>>,
    pub subtree_set: Ghost<Set<RwLockProcessPtr>>,
}

pub type ProcessRwLock = RwLock<Process, ReadOnlyNode<ProcessRO>, ProcessGhost, PROCESS_HAS_KILL_STATE>;

pub ghost struct ProcessU {
    pub pagetable: PageTableU,
    pub iommu_table: Option<PageTableU>,
    
    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,

    pub parent: Option<RwLockProcessPtr>,
    pub children: Seq<RwLockProcessPtr>,
    pub depth: usize,
    pub uppertree_seq: Seq<RwLockProcessPtr>,
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
    pub cr3: PageTableRoot,
    pub pcid: Pcid,
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
    pub fn new_fresh(
        process_ptr: RwLockProcessPtr,
        pcid: Pcid,
        pagetable: RwLockPageTableRoot,
        container_depth: usize,
        depth: usize,
    ) -> (ret: Self)
        requires
            pcid != KERNEL_DEFAULT_PCID,
        ensures
            ret.inv(),
            ret.pcid == pcid,
            ret.pagetable == pagetable,
            ret.iommu_table is None,
            ret.pci_function_ref_counter == 0,
            ret.owned_pci_functions.view() == Set::<PciBdf>::empty(),
            ret.quota_4k == 0,
            ret.quota_2m == 0,
            ret.quota_1g == 0,
            ret.parent_linkedlist_node.is_init(),
            ret.children.view() == Seq::<RwLockProcessPtr>::empty(),
            ret.owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
    {
        let parent_linkedlist_node = ExternalNode::new(process_ptr);
        let children = LinkedList::new(Some(container_depth), Some(depth));
        let owned_threads = LinkedList::new(Some(container_depth), Some(depth));
        Self {
            pcid,
            pagetable,
            iommu_table: None,
            pci_function_ref_counter: 0,
            owned_pci_functions: Ghost(Set::empty()),
            quota_4k: 0,
            quota_2m: 0,
            quota_1g: 0,
            parent_linkedlist_node,
            children,
            owned_threads,
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&&
        self.pcid != KERNEL_DEFAULT_PCID
        &&&
        self.children.inv()
        &&&
        self.owned_threads.wf()
        &&&
        self.pagetable_iommu_table_different()
        &&&
        self.pci_function_ownership_wf()
    }
    pub open spec fn pagetable_iommu_table_different(&self) -> bool {
        &&&
        self.iommu_table is Some ==> self.iommu_table.unwrap() != self.pagetable
    }
    pub open spec fn pci_function_ownership_wf(&self) -> bool {
        &&& self.pci_function_ref_counter
            == self.owned_pci_functions.view().len()
        &&& forall|bdf: PciBdf|
            #![trigger self.owned_pci_functions.view().contains(bdf)]
            self.owned_pci_functions.view().contains(bdf)
            ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2)
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

/// Process quota is independent from thread quota. A future transfer operation
/// moves quota between the two tiers while preserving their sum.
pub open spec fn process_effective_quota_4k(proc_lock: ProcessRwLock) -> int {
    proc_lock.view().quota_4k as int
}

pub open spec fn process_effective_quota_2m(proc_lock: ProcessRwLock) -> int {
    proc_lock.view().quota_2m as int
}

pub open spec fn process_effective_quota_1g(proc_lock: ProcessRwLock) -> int {
    proc_lock.view().quota_1g as int
}

} // verus!

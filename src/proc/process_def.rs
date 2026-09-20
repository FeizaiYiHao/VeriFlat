use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {

use crate::*;

pub struct Process {
    // Independent of the lock's kill state. Resource identifiers are historical when zombie.
    pub zombie: bool,
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
    pub zombie: bool,
    pub pagetable: Option<PageTableU>,
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
    pub fn new_boot_root(
        process_ptr: RwLockProcessPtr,
        pagetable: RwLockPageTableRoot,
        iommu_table: RwLockPageTableRoot,
        root_thread: RwLockThreadPtr,
        thread_node_addr: usize,
        thread_node_perm:
            Tracked<PointsTo<Node<RwLockThreadPtr>>>,
        owned_pci_functions: Ghost<Set<PciBdf>>,
    ) -> (ret: Self)
        requires
            pagetable != iommu_table,
            thread_node_perm.view().is_init(),
            thread_node_perm.view().addr() == thread_node_addr,
            thread_node_perm.view().value().view() == root_thread,
            owned_pci_functions.view().len() == VTD_DOMAIN_COUNT,
            forall|bdf: PciBdf|
                #![trigger owned_pci_functions.view().contains(bdf)]
                owned_pci_functions.view().contains(bdf)
                <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        ensures
            ret.inv(),
            !ret.zombie,
            ret.pcid == 1,
            ret.pagetable == pagetable,
            ret.iommu_table == Some(iommu_table),
            ret.pci_function_ref_counter == VTD_DOMAIN_COUNT,
            ret.owned_pci_functions == owned_pci_functions,
            ret.quota_4k == 0,
            ret.quota_2m == 0,
            ret.quota_1g == 0,
            ret.parent_linkedlist_node.is_init(),
            ret.children.view() == Seq::<RwLockProcessPtr>::empty(),
            ret.owned_threads.view() =~= seq![root_thread],
            ret.owned_threads.map()
                =~= Map::<usize, RwLockThreadPtr>::empty()
                    .insert(thread_node_addr, root_thread),
    {
        let mut ret = Self::new_fresh(
            process_ptr,
            1,
            pagetable,
            0,
            0,
        );
        ret.iommu_table = Some(iommu_table);
        ret.pci_function_ref_counter = VTD_DOMAIN_COUNT;
        ret.owned_pci_functions = owned_pci_functions;
        ret.owned_threads.push_tail(
            thread_node_addr,
            thread_node_perm,
        );
        assert(ret.inv());
        ret
    }

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
            !ret.zombie,
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
            ret.owned_threads.map()
                == Map::<usize, RwLockThreadPtr>::empty(),
            ret.owned_threads.length == 0,
    {
        let parent_linkedlist_node = ExternalNode::new(process_ptr);
        let children = LinkedList::new(Some(container_depth), Some(depth));
        let owned_threads = LinkedList::new(Some(container_depth), Some(depth));
        Self {
            zombie: false,
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
        &&& self.zombie ==> {
            &&& self.owned_threads.view().len() == 0
            &&& self.quota_4k == 0
            &&& self.quota_2m == 0
            &&& self.quota_1g == 0
            &&& self.pci_function_ref_counter == 0
            &&& self.owned_pci_functions.view().is_empty()
        }
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

    pub fn add_owned_thread(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        node_addr: usize,
        node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    )
        requires
            old(self).inv(),
            !old(self).zombie,
            node_perm.is_init(),
            node_perm.addr() == node_addr,
            !old(self).owned_threads.view().contains(thread_ptr),
            old(self).owned_threads.view().len() < usize::MAX,
        ensures
            final(self).inv(),
            *final(self) == (Process {
                owned_threads: final(self).owned_threads,
                ..*old(self)
            }),
            final(self).owned_threads.view()
                == old(self).owned_threads.view().push(thread_ptr),
            final(self).owned_threads.dom()
                == old(self).owned_threads.dom().insert(node_addr),
            final(self).owned_threads.map()
                == old(self).owned_threads.map().insert(node_addr, thread_ptr),
            final(self).owned_threads.length
                == old(self).owned_threads.length + 1,
            !old(self).owned_threads.dom().contains(node_addr),
            !old(self).owned_threads.map().dom().contains(node_addr),
    {
        let mut node_perm = node_perm;
        node_update_value(node_addr, &mut node_perm, thread_ptr);
        proof {
            assert(self.owned_threads.length != usize::MAX) by {
                reveal(LinkedList::wf_value_list);
            };
        }
        self.owned_threads.push_tail(node_addr, node_perm);
    }

    pub fn add_child(
        &mut self,
        child_ptr: RwLockProcessPtr,
        node_addr: usize,
        node_perm: Tracked<PointsTo<Node<RwLockProcessPtr>>>,
    )
        requires
            old(self).inv(),
            node_perm.is_init(),
            node_perm.addr() == node_addr,
            !old(self).children.view().contains(child_ptr),
            old(self).children.view().len() < usize::MAX,
        ensures
            final(self).inv(),
            *final(self) == (Process {
                children: final(self).children,
                ..*old(self)
            }),
            final(self).children.view() == old(self).children.view().push(child_ptr),
            final(self).children.dom() == old(self).children.dom().insert(node_addr),
            final(self).children.map() == old(self).children.map().insert(node_addr, child_ptr),
            final(self).children.length == old(self).children.length + 1,
            !old(self).children.dom().contains(node_addr),
            !old(self).children.map().dom().contains(node_addr),
    {
        let mut node_perm = node_perm;
        node_update_value(node_addr, &mut node_perm, child_ptr);
        proof {
            assert(self.children.length != usize::MAX) by {
                reveal(LinkedList::wf_value_list);
            };
        }
        self.children.push_tail(node_addr, node_perm);
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

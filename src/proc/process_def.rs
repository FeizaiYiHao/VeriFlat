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

    /// Pages pulled from the allocator, not yet retyped. Only non-empty while
    /// the process write-lock is held; flushed before wunlock.
    pub temp_alloc_cache_4k: Ghost<Set<PagePtr>>,
    pub temp_alloc_cache_2m: Ghost<Set<PagePtr>>,
    pub temp_alloc_cache_1g: Ghost<Set<PagePtr>>,

    pub parent_linkedlist_node: ExternalNode<RwLockProcessPtr>,
    pub children: LinkedList<RwLockProcessPtr, 233>,
    pub uppertree_seq: ArrayVec<RwLockContainerPtr, MAX_PROCESS_TREE_DEPTH>,
    pub subtree_set: Ghost<Set<RwLockProcessPtr>>,

    pub owned_threads: LinkedList<RwLockThreadPtr, 233>,
}

pub type ProcessRwLock = RwLock<Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>;

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
        &&&
        self.quota_within_bound()
    }
    /// Staged pages never exceed the nominal quota, so the effective quota
    /// (`quota_* - temp_alloc_cache_*.len()`) stays non-negative. This pins the
    /// conservation fold from below: a container's free-page total is at least
    /// each owned process's effective quota.
    pub open spec fn quota_within_bound(&self) -> bool {
        &&&
        self.quota_4k >= self.temp_alloc_cache_4k.view().len()
        &&&
        self.quota_2m >= self.temp_alloc_cache_2m.view().len()
        &&&
        self.quota_1g >= self.temp_alloc_cache_1g.view().len()
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

impl Process {
    pub open spec fn temp_alloc_clean(&self) -> bool {
        &&& self.temp_alloc_cache_4k.view().len() == 0
        &&& self.temp_alloc_cache_2m.view().len() == 0
        &&& self.temp_alloc_cache_1g.view().len() == 0
    }
}

/// Effective quota counted in the container conservation law: nominal quota
/// minus pages temporarily staged in `temp_alloc_cache` (not yet retyped).
pub open spec fn process_effective_quota_4k(proc_lock: ProcessRwLock) -> int {
    proc_lock.view().quota_4k as int - proc_lock.view().temp_alloc_cache_4k.view().len() as int
}

pub open spec fn process_effective_quota_2m(proc_lock: ProcessRwLock) -> int {
    proc_lock.view().quota_2m as int - proc_lock.view().temp_alloc_cache_2m.view().len() as int
}

pub open spec fn process_effective_quota_1g(proc_lock: ProcessRwLock) -> int {
    proc_lock.view().quota_1g as int - proc_lock.view().temp_alloc_cache_1g.view().len() as int
}

/// temp_alloc_cache is empty unless the process is write-locked.
#[verifier::opaque]
pub open spec fn process_temp_alloc_empty_unless_wlocked(
    process_map: ProcessLockedMap,
) -> bool {
    forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.spec_index(p_ptr).locking_thread()]
        process_map.dom().contains(p_ptr)
        ==>
        !(process_map.spec_index(p_ptr).locking_thread() is Write) ==>
            process_map.spec_index(p_ptr).view().temp_alloc_clean()
}

} // verus!
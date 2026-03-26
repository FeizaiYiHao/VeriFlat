use vstd::prelude::*;
use crate::*;
verus! {

pub enum  CpuState{
    Running,
    Idle,
    // Killing,
    // Killed,
    Off,
}


// #[derive(Clone, Copy, Debug)]
pub struct Cpu {
    pub owning_container: RwLockContainerPtr,
    pub state: CpuState,
    pub current_process: Option<RwLockProcessPtr>,
    pub current_thread: Option<RwLockThreadPtr>,

    pub current_pagetable: RwLockPageTableRoot,
    pub current_cr3: PageTableRoot,
    pub current_pcid: Pcid,

    pub tlb_dirty_bitmap: BitMap<Option<RwLockPageTableRoot>, PCID_MAX>,
    pub container_depth: usize, // killing_container's depth if being killed.
    pub process_depth: usize,
}

impl Cpu{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.state is Off
        // || self.state is Killing
        // || self.state is Killed 
        == (self.current_process is None && self.current_thread is None)
        &&&
        self.current_process is None == self.current_thread is None
        &&&
        self.tlb_dirty_bitmap.inv()
    }

    pub open spec fn tlb_dirty_bitmap(&self) -> Map<Pcid, Option<RwLockPageTableRoot>>{
        self.tlb_dirty_bitmap@
    }

    /// TCB
    // #[verifier(external_body)]
    pub fn set_pagetable(&mut self, pagetable_root:RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid)
        requires
            old(self).wf(),
            usize_in_range::<PCID_MAX>(pcid,)
        ensures
            self.wf(),
            self.owning_container == old(self).owning_container,
            self.state == old(self).state,
            self.current_process == old(self).current_process,
            self.current_thread == old(self).current_thread,
            // self.current_pagetable == old(self).current_pagetable,
            // self.current_cr3 == old(self).current_cr3,
            // self.current_pcid == old(self).current_pcid,
            self.current_pagetable == pagetable_root,
            self.current_cr3 == cr3,
            self.current_pcid == pcid,
            self.tlb_dirty_bitmap@ == old(self).tlb_dirty_bitmap@.insert(pcid, Some(pagetable_root)),
            self.container_depth == old(self).container_depth,
            self.process_depth == old(self).process_depth,
    {
            self.current_pagetable = pagetable_root;
            self.current_cr3 = cr3;
            self.current_pcid = pcid;
            self.tlb_dirty_bitmap.update(pcid, Some(pagetable_root))
    }
}

impl LockInvTrait for Cpu{
    open spec fn inv(&self) -> bool{
        &&&
        self.wf()
    }
}

impl LockMajorTrait for Cpu {
    open spec fn lock_major_1(&self) -> LockMajorId {
        CPU_LOCK_MAJOR_RUNNING
    }
    
    open spec fn lock_major_2(&self) -> LockMajorId {
        CPU_LOCK_MAJOR_IDLE
    }
    
    open spec fn lock_major_3(&self) -> LockMajorId {
        CPU_LOCK_MAJOR_OFF
    }
    
    open spec fn lock_major_default(&self) -> LockMajorId {
        PAGE_TABLE_LOCK_MAJOR
    }
    
    open spec fn lock_major_1_predicate(&self) -> bool {
        self.state is Running
    }
    
    open spec fn lock_major_2_predicate(&self) -> bool {
        self.state is Idle
    }
    
    open spec fn lock_major_3_predicate(&self) -> bool {
        self.state is Off
    }
    
    open spec fn lock_major_default_predicate(&self) -> bool {
        true
    }
    
}

impl LockOwnerIdTrait for Cpu {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.process_depth)
    }
}

}
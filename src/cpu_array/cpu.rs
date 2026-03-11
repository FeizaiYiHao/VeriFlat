use vstd::prelude::*;
use crate::*;
verus! {

pub enum  CpuState{
    Running,
    Idle,
    Killing,
    Killed,
    Off,
}


// #[derive(Clone, Copy, Debug)]
pub struct Cpu {
    pub owning_container: ContainerPtr,
    pub state: CpuState,
    pub current_process: Option<ProcPtr>,
    pub current_thread: Option<ThreadPtr>,

    pub tlb_dirty_bitmap: BitMap<PCID_MAX>,
    pub container_depth: usize, // killing_container's depth if being killed.
    pub process_depth: usize,
}

impl Cpu{
    pub closed spec fn wf(&self) -> bool{
        &&&
        self.state is Off || self.state is Killing || self.state is Killed ==> self.current_process is None && self.current_thread is None
        &&&
        self.tlb_dirty_bitmap.inv()
    }
}

impl LockedUtil for Cpu {
    open spec fn inv(&self) -> bool{
        &&&
        self.wf()
    }
    
    open spec fn lock_major_1(&self) -> LockMajorId {
        0x233
    }
    
    open spec fn lock_major_2(&self) -> LockMajorId {
        0x233
    }
    
    open spec fn lock_major_3(&self) -> LockMajorId {
        0x233
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

impl LockOwnerIdUtil for Cpu {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.process_depth)
    }
}

}
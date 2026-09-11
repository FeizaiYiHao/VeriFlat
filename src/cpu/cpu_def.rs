use vstd::prelude::*;
use crate::*;
use super::cpu_cr3_pcid::CpuCr3Pcid;
verus! {

#[derive(Clone, Copy)]
pub enum CpuState{
    Running,
    Idle,
    // Killing,
    // Killed,
    Off,
}


#[derive(Clone, Copy, Debug)]
pub struct ProcessPageTablePair{
    pub process_ptr: RwLockProcessPtr,
    pub pagetable_ptr: RwLockPageTableRoot,
}

pub struct Cpu {
    owning_container: RwLockContainerPtr,
    state: CpuState,
    current_process: Option<RwLockProcessPtr>,
    current_thread: Option<RwLockThreadPtr>,
    current_pagetable: Option<RwLockPageTableRoot>,
    cr3_pcid: CpuCr3Pcid,
    tlb_dirty_bitmap: BitMap<Option<ProcessPageTablePair>, PCID_MAX>,
    container_depth: usize,
    process_depth: usize,
}

pub ghost struct CpuView {
    pub owning_container: RwLockContainerPtr,
    pub state: CpuState,
    pub current_process: Option<RwLockProcessPtr>,
    pub current_thread: Option<RwLockThreadPtr>,

    /// None selects the kernel's default page table.
    pub current_pagetable: Option<RwLockPageTableRoot>,
    pub current_cr3: PageTableRoot,
    pub current_pcid: Pcid,

    pub tlb_dirty_bitmap: BitMap<Option<ProcessPageTablePair>, PCID_MAX>,
    pub container_depth: usize, // killing_container's depth if being killed.
    pub process_depth: usize,
}

pub ghost struct CpuU {
    pub owning_container: RwLockContainerPtr,
    pub state: CpuState,
    pub current_process: Option<RwLockProcessPtr>,
    pub current_thread: Option<RwLockThreadPtr>,
}

impl LockUserVisibilityTrait for Cpu{
    open spec fn is_user_visible() -> bool {
        true
    }
}

impl Cpu{
    pub closed spec fn view(&self) -> CpuView {
        CpuView {
            owning_container: self.owning_container,
            state: self.state,
            current_process: self.current_process,
            current_thread: self.current_thread,
            current_pagetable: self.current_pagetable,
            current_cr3: self.cr3_pcid.cr3(),
            current_pcid: self.cr3_pcid.pcid(),
            tlb_dirty_bitmap: self.tlb_dirty_bitmap,
            container_depth: self.container_depth,
            process_depth: self.process_depth,
        }
    }

    pub open spec fn spec_state(&self) -> CpuState { self.view().state }

    #[verifier(when_used_as_spec(spec_state))]
    pub fn state(&self) -> (ret: CpuState)
        ensures ret == self.state(),
    {
        self.state
    }

    pub open spec fn spec_owning_container(&self) -> RwLockContainerPtr { self.view().owning_container }

    #[verifier(when_used_as_spec(spec_owning_container))]
    pub fn owning_container(&self) -> (ret: RwLockContainerPtr)
        ensures ret == self.owning_container(),
    {
        self.owning_container
    }

    pub open spec fn spec_current_process(&self) -> Option<RwLockProcessPtr> { self.view().current_process }

    #[verifier(when_used_as_spec(spec_current_process))]
    pub fn current_process(&self) -> (ret: Option<RwLockProcessPtr>)
        ensures ret == self.current_process(),
    {
        self.current_process
    }

    pub open spec fn spec_current_thread(&self) -> Option<RwLockThreadPtr> { self.view().current_thread }

    #[verifier(when_used_as_spec(spec_current_thread))]
    pub fn current_thread(&self) -> (ret: Option<RwLockThreadPtr>)
        ensures ret == self.current_thread(),
    {
        self.current_thread
    }

    pub open spec fn spec_current_cr3(&self) -> PageTableRoot { self.view().current_cr3 }

    #[verifier(when_used_as_spec(spec_current_cr3))]
    pub fn current_cr3(&self) -> (ret: PageTableRoot)
        ensures ret == self.current_cr3(),
    {
        self.cr3_pcid.cr3()
    }

    pub open spec fn spec_current_pcid(&self) -> Pcid { self.view().current_pcid }

    #[verifier(when_used_as_spec(spec_current_pcid))]
    pub fn current_pcid(&self) -> (ret: Pcid)
        ensures ret == self.current_pcid(),
    {
        self.cr3_pcid.pcid()
    }

    pub open spec fn wf(&self) -> bool{
        &&&
        self.view().state is Off ==> (self.view().current_process is None && self.view().current_thread is None)
        &&& self.view().state is Idle ==> (self.view().current_process is None && self.view().current_thread is None)
        &&& (self.view().state is Off ==> forall|pcid: Pcid|
            #![trigger self.tlb_dirty_bitmap().spec_index(pcid)]
            pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> self.tlb_dirty_bitmap().spec_index(pcid) is None)
        &&& self.view().state is Running ==> (self.view().current_process is Some && self.view().current_thread is Some)
        &&& self.view().current_process is None == self.view().current_thread is None
        &&& self.view().current_process is None == self.view().current_pagetable is None
        &&&
        self.view().tlb_dirty_bitmap.inv()
    }

    pub open spec fn tlb_dirty_bitmap(&self) -> Map<Pcid, Option<ProcessPageTablePair>>{
        self.view().tlb_dirty_bitmap.view()
    }


    pub fn transfer_off_cpu_to_container(&mut self, container: RwLockContainerPtr, depth: usize)
        requires
            old(self).wf(),
            old(self).view().state is Off,
        ensures
            final(self).wf(),
            final(self).view() == (CpuView { owning_container: container, container_depth: depth, ..old(self).view() }),
    {
        self.owning_container = container;
        self.container_depth = depth;
    }

}

impl CpuLockedArray {
    pub fn block_current(&mut self, cpu_id: CpuId, default_cr3: PageTableRoot, tlb: &mut CpuTLB, Tracked(lctx): Tracked<&mut LocalContext>, cpu_lock_perm: Tracked<&LockPerm>)
        requires
            old(self).inv(),
            old(tlb).inv(),
            page_ptr_valid(default_cr3),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).typed_lock_map_aligned(old(lctx).cpu_lock_map(), old(lctx).thread_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(self).spec_index(cpu_id).view().is_init(),
            old(self).spec_index(cpu_id).view().view().wf(),
            old(self).spec_index(cpu_id).view().view().view().state is Running,
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(self).spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            *final(tlb) == *old(tlb),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            lock_id_set_aligned(old(lctx)) ==> lock_id_set_aligned(final(lctx)),
            old(lctx).cpu_lock_map().index(cpu_id).lock_id == old(self).spec_index(cpu_id).lock_id(),
            final(self).inv(),
            final(self).entries_unchanged_except(old(self), cpu_id),
            final(self).spec_index(cpu_id).view().is_init(),
            final(self).spec_index(cpu_id).view().view().wf(),
            final(self).spec_index(cpu_id).view().locking_thread() == old(self).spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(cpu_id).view().being_killed() == old(self).spec_index(cpu_id).view().being_killed(),
            final(self).spec_index(cpu_id).view().view_rodata() == old(self).spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(cpu_id).view().view_ghost() == old(self).spec_index(cpu_id).view().view_ghost(),
            final(self).typed_lock_map_aligned(old(lctx).cpu_lock_map().insert(cpu_id, TypedHeldLock { lock_id: final(self).spec_index(cpu_id).lock_id(), mode: TypedLockMode::Write }), final(lctx).thread_id()),
            final(self).spec_index(cpu_id).view().view().view() == (CpuView { state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None, current_cr3: default_cr3, current_pcid: KERNEL_DEFAULT_PCID, ..old(self).spec_index(cpu_id).view().view().view() }),
    {
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        cpu.cr3_pcid.write(cpu_id, default_cr3, KERNEL_DEFAULT_PCID, false, tlb, Tracked(&mut *lctx));
        cpu.current_process = None;
        cpu.current_thread = None;
        cpu.current_pagetable = None;
        cpu.state = CpuState::Idle;
    }

    /// Select a thread on this running or idle CPU without changing containers.
    pub fn switch_to_thread(
        &mut self,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        cr3: PageTableRoot,
        pcid: Pcid,
        process_depth: usize,
        tlb: &mut CpuTLB,
        Tracked(lctx): Tracked<&mut LocalContext>,
        cpu_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(tlb).inv(),
            page_ptr_valid(cr3),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).typed_lock_map_aligned(old(lctx).cpu_lock_map(), old(lctx).thread_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(self).spec_index(cpu_id).view().is_init(),
            old(self).spec_index(cpu_id).view().view().wf(),
            !(old(self).spec_index(cpu_id).view().view().view().state is Off),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(self).spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
        ensures
            final(tlb).inv(),
            forall|other_cpu: CpuId, other_pcid: Pcid|
                #![trigger final(tlb).spec_index((other_cpu, other_pcid))]
                #![trigger old(tlb).spec_index((other_cpu, other_pcid))]
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) ==> {
                    let entry = old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let flush = entry is Some && (entry.unwrap().process_ptr != process_ptr || entry.unwrap().pagetable_ptr != pagetable_ptr);
                    final(tlb).spec_index((other_cpu, other_pcid)) == if flush && other_cpu == cpu_id && other_pcid == pcid { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old(tlb).spec_index((other_cpu, other_pcid)) }
                },
            {
                let entry = old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let flush = entry is Some && (entry.unwrap().process_ptr != process_ptr || entry.unwrap().pagetable_ptr != pagetable_ptr);
                &&& (!flush ==> *final(tlb) == *old(tlb))
                &&& final(tlb).view() == if flush { old(tlb).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { old(tlb).view() }
            },
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            lock_id_set_aligned(old(lctx)) ==> lock_id_set_aligned(final(lctx)),
            old(lctx).cpu_lock_map().index(cpu_id).lock_id == old(self).spec_index(cpu_id).lock_id(),
            final(self).inv(),
            final(self).entries_unchanged_except(old(self), cpu_id),
            final(self).spec_index(cpu_id).view().is_init(),
            final(self).spec_index(cpu_id).view().view().wf(),
            final(self).spec_index(cpu_id).view().locking_thread() == old(self).spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(cpu_id).view().being_killed() == old(self).spec_index(cpu_id).view().being_killed(),
            final(self).spec_index(cpu_id).view().view_rodata() == old(self).spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(cpu_id).view().view_ghost() == old(self).spec_index(cpu_id).view().view_ghost(),
            final(self).typed_lock_map_aligned(old(lctx).cpu_lock_map().insert(cpu_id, TypedHeldLock { lock_id: final(self).spec_index(cpu_id).lock_id(), mode: TypedLockMode::Write }), final(lctx).thread_id()),
            final(self).spec_index(cpu_id).view().view().view().state is Running,
            final(self).spec_index(cpu_id).view().view().view().owning_container == old(self).spec_index(cpu_id).view().view().view().owning_container,
            final(self).spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            final(self).spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            final(self).spec_index(cpu_id).view().view().view().current_pagetable == Some(pagetable_ptr),
            final(self).spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            final(self).spec_index(cpu_id).view().view().view().current_pcid == pcid,
            final(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap() == old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr, pagetable_ptr })),
            final(self).spec_index(cpu_id).view().view().view().container_depth == old(self).spec_index(cpu_id).view().view().view().container_depth,
            final(self).spec_index(cpu_id).view().view().view().process_depth == process_depth,
    {
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        let dirty = cpu.tlb_dirty_bitmap.index(pcid);
        let flush = match dirty {
            Some(entry) => entry.process_ptr != process_ptr || entry.pagetable_ptr != pagetable_ptr,
            None => false,
        };
        cpu.cr3_pcid.write(cpu_id, cr3, pcid, flush, tlb, Tracked(&mut *lctx));
        cpu.state = CpuState::Running;
        cpu.current_process = Some(process_ptr);
        cpu.current_thread = Some(thread_ptr);
        cpu.current_pagetable = Some(pagetable_ptr);
        cpu.process_depth = process_depth;
        cpu.tlb_dirty_bitmap.update(pcid, Some(ProcessPageTablePair { process_ptr, pagetable_ptr }));
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
        self.view().state is Running
    }
    
    open spec fn lock_major_2_predicate(&self) -> bool {
        self.view().state is Idle
    }
    
    open spec fn lock_major_3_predicate(&self) -> bool {
        self.view().state is Off
    }
    
    open spec fn lock_major_default_predicate(&self) -> bool {
        true
    }
    
}

impl LockOwnerIdTrait for Cpu {
    open spec fn container_depth(&self) -> LockOwnerId {
        if self.view().state is Off { LockOwnerId::NotApp } else { LockOwnerId::Some(self.view().container_depth) }
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        if self.view().current_process is Some { LockOwnerId::Some(self.view().process_depth) } else { LockOwnerId::NotApp }
    }
}

}

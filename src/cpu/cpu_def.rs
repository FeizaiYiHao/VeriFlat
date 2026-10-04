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
    /// Ghost record of whether the hardware cpu is halted; set when publishing Off, cleared by the woken cpu.
    hw_halted: Ghost<bool>,
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
    pub hw_halted: bool,
}

pub ghost struct CpuU {
    pub lock_state: LockStateU,
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
    fn new_quiescent(
        owning_container: RwLockContainerPtr,
        container_depth: usize,
        state: CpuState,
        default_cr3: PageTableRoot,
    ) -> (ret: Self)
        requires
            state is Idle || state is Off,
            page_ptr_valid(default_cr3),
        ensures
            ret.inv(),
            ret.view().owning_container == owning_container,
            ret.view().container_depth == container_depth,
            ret.view().state == state,
            ret.view().current_process is None,
            ret.view().current_thread is None,
            ret.view().current_pagetable is None,
            ret.view().current_cr3 == default_cr3,
            ret.view().current_pcid == KERNEL_DEFAULT_PCID,
            ret.view().hw_halted == (state is Off),
            forall|pcid: Pcid|
                #![trigger ret.tlb_dirty_bitmap().spec_index(pcid)]
                pcid_valid(pcid)
                ==> ret.tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        Self {
            owning_container,
            state,
            current_process: None,
            current_thread: None,
            current_pagetable: None,
            cr3_pcid: CpuCr3Pcid::new(default_cr3, KERNEL_DEFAULT_PCID),
            tlb_dirty_bitmap: BitMap::new_with_init_value(None),
            container_depth,
            process_depth: 0,
            hw_halted: Ghost(state is Off),
        }
    }

    pub fn new_idle(
        owning_container: RwLockContainerPtr,
        container_depth: usize,
        default_cr3: PageTableRoot,
    ) -> (ret: Self)
        requires
            page_ptr_valid(default_cr3),
        ensures
            ret.inv(),
            ret.view().owning_container == owning_container,
            ret.view().container_depth == container_depth,
            ret.view().state is Idle,
            ret.view().current_process is None,
            ret.view().current_thread is None,
            ret.view().current_pagetable is None,
            ret.view().current_cr3 == default_cr3,
            ret.view().current_pcid == KERNEL_DEFAULT_PCID,
            forall|pcid: Pcid|
                #![trigger ret.tlb_dirty_bitmap().spec_index(pcid)]
                pcid_valid(pcid)
                ==> ret.tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        Self::new_quiescent(owning_container, container_depth, CpuState::Idle, default_cr3)
    }

    pub fn new_off(
        owning_container: RwLockContainerPtr,
        container_depth: usize,
        default_cr3: PageTableRoot,
    ) -> (ret: Self)
        requires
            page_ptr_valid(default_cr3),
        ensures
            ret.inv(),
            ret.view().owning_container == owning_container,
            ret.view().container_depth == container_depth,
            ret.view().state is Off,
            ret.view().current_process is None,
            ret.view().current_thread is None,
            ret.view().current_pagetable is None,
            ret.view().current_cr3 == default_cr3,
            ret.view().current_pcid == KERNEL_DEFAULT_PCID,
            forall|pcid: Pcid|
                #![trigger ret.tlb_dirty_bitmap().spec_index(pcid)]
                pcid_valid(pcid)
                ==> ret.tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        Self::new_quiescent(owning_container, container_depth, CpuState::Off, default_cr3)
    }

    pub fn new_boot_array(
        owning_container: RwLockContainerPtr,
        default_cr3: PageTableRoot,
    ) -> (ret: CpuLockedArray)
        requires
            0 < NUM_CPUS,
            page_ptr_valid(default_cr3),
        ensures
            ret.inv(),
            forall|cpu_id: CpuId|
                #![trigger ret.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id)
                ==> {
                    &&& ret.spec_index(cpu_id).view().inv()
                    &&& !ret.spec_index(cpu_id).view().locked()
                    &&& ret.spec_index(cpu_id).view().view()
                        .view().owning_container == owning_container
                    &&& ret.spec_index(cpu_id).view().view()
                        .view().container_depth == 0
                    &&& ret.spec_index(cpu_id).view().view()
                        .view().state == if cpu_id == 0 {
                            CpuState::Idle
                        } else {
                            CpuState::Off
                        }
                    &&& ret.spec_index(cpu_id).view().view()
                        .view().current_cr3 == default_cr3
                    &&& ret.spec_index(cpu_id).view().view()
                        .view().current_pcid == KERNEL_DEFAULT_PCID
                },
    {
        let mut cpus:
            Array<RwLock<Cpu, (), (), CPU_HAS_KILL_STATE>, NUM_CPUS>
                = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                0 <= cpu_id <= NUM_CPUS,
                cpus.wf(),
                page_ptr_valid(default_cr3),
                forall|old_cpu: CpuId|
                    #![trigger cpus.spec_index(old_cpu)]
                    old_cpu < cpu_id
                    ==> {
                        &&& cpus.spec_index(old_cpu).inv()
                        &&& !cpus.spec_index(old_cpu).locked()
                        &&& cpus.spec_index(old_cpu).view()
                            .view().owning_container == owning_container
                        &&& cpus.spec_index(old_cpu).view()
                            .view().container_depth == 0
                        &&& cpus.spec_index(old_cpu).view()
                            .view().state == if old_cpu == 0 {
                                CpuState::Idle
                            } else {
                                CpuState::Off
                            }
                        &&& cpus.spec_index(old_cpu).view()
                            .view().current_cr3 == default_cr3
                        &&& cpus.spec_index(old_cpu).view()
                            .view().current_pcid == KERNEL_DEFAULT_PCID
                    },
            decreases NUM_CPUS - cpu_id,
        {
            let cpu = if cpu_id == 0 {
                Self::new_idle(owning_container, 0, default_cr3)
            } else {
                Self::new_off(owning_container, 0, default_cr3)
            };
            cpus.set(cpu_id, RwLock::new_unlocked(cpu, (), Ghost(())));
            cpu_id = cpu_id + 1;
        }
        LockedArray::from_array(cpus)
    }

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
            hw_halted: self.hw_halted.view(),
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

    pub open spec fn spec_current_pcid(&self) -> Pcid { self.view().current_pcid }

    pub fn flush_current_tlb(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, tlb: &mut CpuTLB, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(tlb).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(self).view().current_cr3 == cr3,
            old(self).view().current_pcid == pcid,
            lctx.kernel_view_locking_state() is Release,
        ensures
            *final(self) == *old(self),
            final(tlb).inv(),
            forall|c: CpuId, p: Pcid| #![trigger final(tlb).spec_index((c, p))] #![trigger old(tlb).spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(tlb).spec_index((c, p)) == old(tlb).spec_index((c, p)),
            final(tlb).spec_index((cpu_id, pcid)).is_empty(),
            final(tlb).view() == old(tlb).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
    {
        self.cr3_pcid.flush_current(cpu_id, cr3, pcid, tlb, Tracked(lctx));
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

    pub fn publish_idle_from_off(&mut self)
        requires old(self).wf(), old(self).view().state is Off,
        ensures final(self).wf(), final(self).view() == (CpuView { state: CpuState::Idle, ..old(self).view() }),
    {
        self.state = CpuState::Idle;
    }

    /// The woken cpu records that its hardware runs again; the software state is untouched.
    pub fn clear_hw_halted(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).view() == (CpuView { hw_halted: false, ..old(self).view() }),
    { self.hw_halted = Ghost(false); }

    /// Publish Off from Idle with an empty dirty map; the caller has flushed every non-default PCID of this cpu.
    pub fn publish_off_from_idle(&mut self)
        requires old(self).wf(), old(self).view().state is Idle,
        ensures
            final(self).wf(),
            final(self).view() == (CpuView { state: CpuState::Off, tlb_dirty_bitmap: final(self).view().tlb_dirty_bitmap, hw_halted: true, ..old(self).view() }),
            forall|pcid: Pcid| #![trigger final(self).tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) ==> final(self).tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        self.state = CpuState::Off;
        self.tlb_dirty_bitmap = BitMap::new_with_init_value(None);
        self.hw_halted = Ghost(true);
    }
}

impl CpuLockedArray {
    pub fn block_current(&mut self, cpu_id: CpuId, default_cr3: PageTableRoot, tlb: &mut CpuTLB, needflush: &mut PcidNeedFlushArray, published: &mut CpuPublishedArray, needflush_perm: Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, cpu_lock_perm: Tracked<&LockPerm>)
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
            old(needflush).typed_lock_map_aligned(old(lctx).pcid_needflush_lock_map(), old(lctx).thread_id()),
            typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
            old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).inv(),
            needflush_perm.view().state() is WriteLock,
            needflush_perm.view().thread_id() == old(lctx).thread_id(),
            needflush_perm.view().lock_id() == old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread()->Write_lock_id,
            old(published)[cpu_id as int].owner_cpu() == cpu_id,
        ensures
            pcid_needflush_wf(*old(needflush)) ==> pcid_needflush_wf(*final(needflush)),
            cpu_published_wf(*old(published), *old(self), *old(needflush)) ==> cpu_published_wf(*final(published), *final(self), *final(needflush)),
            final(published)[cpu_id as int].inv(),
            final(published)[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID),
            final(published)[cpu_id as int].owner_cpu() == old(published)[cpu_id as int].owner_cpu(),
            forall|c: CpuId| #![trigger final(published)[c as int]] #![trigger old(published)[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> final(published)[c as int] == old(published)[c as int],
            final(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view() == (PcidNeedFlush { needflush: false, ..old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view() }),
            final(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).is_init(),
            final(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() == old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread(),
            final(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view_ghost() == old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view_ghost(),
            final(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view_rodata() == old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view_rodata(),
            final(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).being_killed() == old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).being_killed(),
            final(needflush).typed_lock_map_aligned(final(lctx).pcid_needflush_lock_map(), final(lctx).thread_id()),
            forall|c: CpuId, p: Pcid| #![trigger final(needflush).spec_index(c, p)] #![trigger old(needflush).spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != KERNEL_DEFAULT_PCID) ==> final(needflush).spec_index(c, p) == old(needflush).spec_index(c, p),
            final(tlb).inv(),
            final(tlb).view() == if old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush { old(tlb).view().insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { old(tlb).view() },
            forall|c: CpuId, p: Pcid|
                #![trigger final(tlb).spec_index((c, p))]
                #![trigger old(tlb).spec_index((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) ==> final(tlb).spec_index((c, p)) == if old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush && c == cpu_id && p == KERNEL_DEFAULT_PCID { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old(tlb).spec_index((c, p)) },
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
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
        let pending = needflush.borrow_typed(cpu_id, KERNEL_DEFAULT_PCID, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm).needflush;
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        cpu.cr3_pcid.write(cpu_id, default_cr3, KERNEL_DEFAULT_PCID, pending, tlb, Tracked(&mut *lctx));
        cpu.current_process = None;
        cpu.current_thread = None;
        cpu.current_pagetable = None;
        cpu.state = CpuState::Idle;
        published[cpu_id].store(default_cr3, KERNEL_DEFAULT_PCID, Tracked(&*lctx));
        let entry = needflush.borrow_mut_typed(cpu_id, KERNEL_DEFAULT_PCID, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm);
        entry.set(false);
        proof {
            assert(needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id())) by { reveal(LockedArray2D::typed_lock_map_aligned); };
            assert(pcid_needflush_wf(*old(needflush)) ==> pcid_needflush_wf(*needflush)) by { reveal(pcid_needflush_wf); };
            assert(cpu_published_wf(*old(published), *old(self), *old(needflush)) ==> cpu_published_wf(*published, *self, *needflush)) by { reveal(cpu_published_wf); };
        }
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
        needflush: &mut PcidNeedFlushArray,
        published: &mut CpuPublishedArray,
        needflush_perm: Tracked<&LockPerm>,
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
            old(needflush).typed_lock_map_aligned(old(lctx).pcid_needflush_lock_map(), old(lctx).thread_id()),
            typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
            old(needflush).spec_index(cpu_id, pcid).inv(),
            needflush_perm.view().state() is WriteLock,
            needflush_perm.view().thread_id() == old(lctx).thread_id(),
            needflush_perm.view().lock_id() == old(needflush).spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
            old(published)[cpu_id as int].owner_cpu() == cpu_id,
        ensures
            pcid_needflush_wf(*old(needflush)) ==> pcid_needflush_wf(*final(needflush)),
            cpu_published_wf(*old(published), *old(self), *old(needflush)) ==> cpu_published_wf(*final(published), *final(self), *final(needflush)),
            final(published)[cpu_id as int].inv(),
            final(published)[cpu_id as int].view() == (cr3, pcid),
            final(published)[cpu_id as int].owner_cpu() == old(published)[cpu_id as int].owner_cpu(),
            forall|c: CpuId| #![trigger final(published)[c as int]] #![trigger old(published)[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> final(published)[c as int] == old(published)[c as int],
            final(needflush).spec_index(cpu_id, pcid).view() == (PcidNeedFlush { needflush: false, ..old(needflush).spec_index(cpu_id, pcid).view() }),
            final(needflush).spec_index(cpu_id, pcid).view().index() == old(needflush).spec_index(cpu_id, pcid).view().index(),
            final(needflush).spec_index(cpu_id, pcid).is_init(),
            final(needflush).spec_index(cpu_id, pcid).locking_thread() == old(needflush).spec_index(cpu_id, pcid).locking_thread(),
            final(needflush).spec_index(cpu_id, pcid).view_ghost() == old(needflush).spec_index(cpu_id, pcid).view_ghost(),
            final(needflush).spec_index(cpu_id, pcid).view_rodata() == old(needflush).spec_index(cpu_id, pcid).view_rodata(),
            final(needflush).spec_index(cpu_id, pcid).being_killed() == old(needflush).spec_index(cpu_id, pcid).being_killed(),
            final(needflush).typed_lock_map_aligned(final(lctx).pcid_needflush_lock_map(), final(lctx).thread_id()),
            forall|c: CpuId, p: Pcid| #![trigger final(needflush).spec_index(c, p)] #![trigger old(needflush).spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(needflush).spec_index(c, p) == old(needflush).spec_index(c, p),
            final(tlb).inv(),
            forall|other_cpu: CpuId, other_pcid: Pcid|
                #![trigger final(tlb).spec_index((other_cpu, other_pcid))]
                #![trigger old(tlb).spec_index((other_cpu, other_pcid))]
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) ==> {
                    let entry = old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let flush = old(needflush).spec_index(cpu_id, pcid).view().needflush || (entry is Some && (entry.unwrap().process_ptr != process_ptr || entry.unwrap().pagetable_ptr != pagetable_ptr));
                    final(tlb).spec_index((other_cpu, other_pcid)) == if flush && other_cpu == cpu_id && other_pcid == pcid { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old(tlb).spec_index((other_cpu, other_pcid)) }
                },
            {
                let entry = old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let flush = old(needflush).spec_index(cpu_id, pcid).view().needflush || (entry is Some && (entry.unwrap().process_ptr != process_ptr || entry.unwrap().pagetable_ptr != pagetable_ptr));
                &&& (!flush ==> *final(tlb) == *old(tlb))
                &&& final(tlb).view() == if flush { old(tlb).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { old(tlb).view() }
            },
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
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
            final(self).spec_index(cpu_id).view().view().view() == (CpuView { state: CpuState::Running, current_process: Some(process_ptr), current_thread: Some(thread_ptr), current_pagetable: Some(pagetable_ptr), current_cr3: cr3, current_pcid: pcid, process_depth, tlb_dirty_bitmap: final(self).spec_index(cpu_id).view().view().view().tlb_dirty_bitmap, ..old(self).spec_index(cpu_id).view().view().view() }),
            final(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap() == old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr, pagetable_ptr })),
    {
        let pending = needflush.borrow_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm).needflush;
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        let dirty = cpu.tlb_dirty_bitmap.index(pcid);
        let flush = pending || match dirty {
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
        published[cpu_id].store(cr3, pcid, Tracked(&*lctx));
        let entry = needflush.borrow_mut_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm);
        entry.set(false);
        proof {
            assert(needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id())) by { reveal(LockedArray2D::typed_lock_map_aligned); };
            assert(pcid_needflush_wf(*old(needflush)) ==> pcid_needflush_wf(*needflush)) by { reveal(pcid_needflush_wf); };
            assert(cpu_published_wf(*old(published), *old(self), *old(needflush)) ==> cpu_published_wf(*published, *self, *needflush)) by { reveal(cpu_published_wf); };
        }
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

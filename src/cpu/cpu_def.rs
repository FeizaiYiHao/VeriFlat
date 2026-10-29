use vstd::prelude::*;
use crate::*;
use super::cpu_cr3_pcid::CpuCr3Pcid;
use super::cpu_def_eof::*;
verus! {
#[derive(Clone, Copy)]
pub enum CpuState {
    Running,
    Idle,
    Off,
}

#[derive(Clone, Copy, Debug)]
pub struct ProcessPageTablePair {
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
    /// This cpu's kernel-call permission while the cpu is outside a kernel step; inside one it sits in the local context.
    kernel_call_perm: Tracked<Option<KernelCallPerm>>,
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
    pub lock_state: LockStateU,
    pub owning_container: RwLockContainerPtr,
    pub state: CpuState,
    pub current_process: Option<RwLockProcessPtr>,
    pub current_thread: Option<RwLockThreadPtr>,
    pub killed: bool,
    pub op: CpuOpState,
}

impl Cpu {
    fn new_quiescent(owning_container: RwLockContainerPtr, container_depth: usize, state: CpuState, default_cr3: PageTableRoot, cpu_id: CpuId) -> (ret: Self)
        requires
            state is Idle || state is Off,
            page_ptr_valid(default_cr3),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            ret.kernel_call_perm() == Some(cpu_id),
            ret.inv(),
            ret.view().owning_container == owning_container,
            ret.view().container_depth == container_depth,
            ret.view().state == state,
            ret.view().current_process is None,
            ret.view().current_thread is None,
            ret.view().current_pagetable is None,
            ret.view().current_cr3 == default_cr3,
            ret.view().current_pcid == KERNEL_DEFAULT_PCID,
            forall|pcid: Pcid| #![trigger ret.tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) ==> ret.tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        Self {
            owning_container, state, current_process: None, current_thread: None, current_pagetable: None,
            cr3_pcid: CpuCr3Pcid::new(default_cr3, KERNEL_DEFAULT_PCID), tlb_dirty_bitmap: BitMap::new_with_init_value(None),
            container_depth, process_depth: 0, kernel_call_perm: Tracked(Some(KernelCallPerm::new_boot(cpu_id))),
        }
    }

    pub fn new_idle(owning_container: RwLockContainerPtr, container_depth: usize, default_cr3: PageTableRoot, cpu_id: CpuId) -> (ret: Self)
        requires
            page_ptr_valid(default_cr3),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            ret.kernel_call_perm() == Some(cpu_id),
            ret.inv(),
            ret.view().owning_container == owning_container,
            ret.view().container_depth == container_depth,
            ret.view().state is Idle,
            ret.view().current_process is None,
            ret.view().current_thread is None,
            ret.view().current_pagetable is None,
            ret.view().current_cr3 == default_cr3,
            ret.view().current_pcid == KERNEL_DEFAULT_PCID,
            forall|pcid: Pcid| #![trigger ret.tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) ==> ret.tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        Self::new_quiescent(owning_container, container_depth, CpuState::Idle, default_cr3, cpu_id)
    }

    pub fn new_off(owning_container: RwLockContainerPtr, container_depth: usize, default_cr3: PageTableRoot, cpu_id: CpuId) -> (ret: Self)
        requires
            page_ptr_valid(default_cr3),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            ret.kernel_call_perm() == Some(cpu_id),
            ret.inv(),
            ret.view().owning_container == owning_container,
            ret.view().container_depth == container_depth,
            ret.view().state is Off,
            ret.view().current_process is None,
            ret.view().current_thread is None,
            ret.view().current_pagetable is None,
            ret.view().current_cr3 == default_cr3,
            ret.view().current_pcid == KERNEL_DEFAULT_PCID,
            forall|pcid: Pcid| #![trigger ret.tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) ==> ret.tlb_dirty_bitmap().spec_index(pcid) is None,
    {
        Self::new_quiescent(owning_container, container_depth, CpuState::Off, default_cr3, cpu_id)
    }

    pub fn new_boot_array(owning_container: RwLockContainerPtr, default_cr3: PageTableRoot) -> (ret: CpuLockedArray)
        requires
            0 < NUM_CPUS,
            page_ptr_valid(default_cr3),
        ensures
            ret.inv(),
            forall|cpu_id: CpuId|
                #![trigger ret.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> {
                    &&& ret.spec_index(cpu_id).view().inv()
                    &&& !ret.spec_index(cpu_id).view().locked()
                    &&& !ret.spec_index(cpu_id).view().being_killed()
                    &&& ret.spec_index(cpu_id).view().view_ghost() is None
                    &&& ret.spec_index(cpu_id).view().view().kernel_call_perm() == Some(cpu_id)
                    &&& ret.spec_index(cpu_id).view().view().view().owning_container == owning_container
                    &&& ret.spec_index(cpu_id).view().view().view().container_depth == 0
                    &&& ret.spec_index(cpu_id).view().view().view().state == if cpu_id == 0 { CpuState::Idle } else { CpuState::Off }
                    &&& ret.spec_index(cpu_id).view().view().view().current_cr3 == default_cr3
                    &&& ret.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID
                },
    {
        let mut cpus: Array<RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>, NUM_CPUS> = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                0 <= cpu_id <= NUM_CPUS,
                cpus.wf(),
                page_ptr_valid(default_cr3),
                forall|old_cpu: CpuId|
                    #![trigger cpus.spec_index(old_cpu)]
                    old_cpu < cpu_id ==> {
                        &&& cpus.spec_index(old_cpu).inv()
                        &&& !cpus.spec_index(old_cpu).locked()
                        &&& !cpus.spec_index(old_cpu).being_killed()
                        &&& cpus.spec_index(old_cpu).view_ghost() is None
                        &&& cpus.spec_index(old_cpu).view().kernel_call_perm() == Some(old_cpu)
                        &&& cpus.spec_index(old_cpu).view().view().owning_container == owning_container
                        &&& cpus.spec_index(old_cpu).view().view().container_depth == 0
                        &&& cpus.spec_index(old_cpu).view().view().state == if old_cpu == 0 { CpuState::Idle } else { CpuState::Off }
                        &&& cpus.spec_index(old_cpu).view().view().current_cr3 == default_cr3
                        &&& cpus.spec_index(old_cpu).view().view().current_pcid == KERNEL_DEFAULT_PCID
                    },
            decreases NUM_CPUS - cpu_id,
        {
            let cpu = if cpu_id == 0 { Self::new_idle(owning_container, 0, default_cr3, cpu_id) } else { Self::new_off(owning_container, 0, default_cr3, cpu_id) };
            cpus.set(cpu_id, RwLock::new_unlocked(cpu, (), Ghost(None)));
            cpu_id = cpu_id + 1;
        }
        LockedArray::from_array(cpus)
    }

    pub closed spec fn view(&self) -> CpuView {
        CpuView {
            owning_container: self.owning_container, state: self.state, current_process: self.current_process, current_thread: self.current_thread,
            current_pagetable: self.current_pagetable, current_cr3: self.cr3_pcid.cr3(), current_pcid: self.cr3_pcid.pcid(),
            tlb_dirty_bitmap: self.tlb_dirty_bitmap, container_depth: self.container_depth, process_depth: self.process_depth,
        }
    }

    /// The cpu whose kernel-call permission this object holds; `None` while that cpu is inside a kernel step.
    pub closed spec fn kernel_call_perm(&self) -> Option<CpuId> {
        match self.kernel_call_perm.view() { Some(perm) => Some(perm.cpu_id()), None => None }
    }

    /// Hands this object's kernel-call permission to the cpu entering a kernel step.
    pub(crate) proof fn take_kernel_call_perm(tracked &mut self) -> (tracked ret: KernelCallPerm)
        requires
            old(self).kernel_call_perm() is Some,
        ensures
            Some(ret.cpu_id()) == old(self).kernel_call_perm(),
            final(self).kernel_call_perm() is None,
            final(self).view() == old(self).view(),
            final(self).cr3_matches_hardware() == old(self).cr3_matches_hardware(),
    { self.kernel_call_perm.borrow_mut().tracked_take() }

    /// Takes back the kernel-call permission of cpu `cpu_id`, which this object holds outside that cpu's kernel steps.
    pub(crate) proof fn put_kernel_call_perm(tracked &mut self, cpu_id: CpuId, tracked perm: KernelCallPerm)
        requires
            old(self).kernel_call_perm() is None,
            perm.cpu_id() == cpu_id,
        ensures
            final(self).kernel_call_perm() == Some(cpu_id),
            final(self).view() == old(self).view(),
            final(self).cr3_matches_hardware() == old(self).cr3_matches_hardware(),
    {
        let tracked mut slot = Some(perm);
        vstd::modes::tracked_swap(self.kernel_call_perm.borrow_mut(), &mut slot);
    }

    pub open spec fn spec_state(&self) -> CpuState { self.view().state }

    #[verifier(when_used_as_spec(spec_state))]
    pub fn state(&self) -> (ret: CpuState)
        ensures
            ret == self.state(),
    {
        self.state
    }

    pub open spec fn spec_owning_container(&self) -> RwLockContainerPtr { self.view().owning_container }

    #[verifier(when_used_as_spec(spec_owning_container))]
    pub fn owning_container(&self) -> (ret: RwLockContainerPtr)
        ensures
            ret == self.owning_container(),
    {
        self.owning_container
    }

    pub open spec fn spec_current_process(&self) -> Option<RwLockProcessPtr> { self.view().current_process }

    #[verifier(when_used_as_spec(spec_current_process))]
    pub fn current_process(&self) -> (ret: Option<RwLockProcessPtr>)
        ensures
            ret == self.current_process(),
    {
        self.current_process
    }

    /// Depth of the current process; the concrete process owner this cpu requests for a dynamic container lock.
    pub fn process_depth(&self) -> (ret: usize)
        ensures
            ret == self.view().process_depth,
    {
        self.process_depth
    }

    pub open spec fn spec_current_thread(&self) -> Option<RwLockThreadPtr> { self.view().current_thread }

    #[verifier(when_used_as_spec(spec_current_thread))]
    pub fn current_thread(&self) -> (ret: Option<RwLockThreadPtr>)
        ensures
            ret == self.current_thread(),
    {
        self.current_thread
    }

    /// Flushes this cpu's current `(cpu_id, pcid)`; the walker may refill it at once with present leaves of the table the
    /// cpu runs, as `k` records it.
    pub fn flush_current_tlb(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, tlb: &mut CpuTLB, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(tlb).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(self).view().current_cr3 == cr3,
            old(self).view().current_pcid == pcid,
            lctx.kernel_view_locking_state() is Release,
            old(self).view().current_pagetable matches Some(ptr) ==> k.pt_mp.dom().contains(ptr) && k.pt_mp.spec_index(ptr).view().cr3 == cr3,
        ensures
            *final(self) == *old(self),
            final(tlb).inv(),
            forall|c: CpuId, p: Pcid| #![trigger final(tlb).spec_index((c, p))] #![trigger old(tlb).spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(tlb).spec_index((c, p)) == old(tlb).spec_index((c, p)),
            final(tlb).view() == old(tlb).view().insert((cpu_id, pcid), final(tlb).spec_index((cpu_id, pcid))),
            match old(self).view().current_pagetable {
                Some(ptr) => single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(tlb).spec_index((cpu_id, pcid)), pagetable_c(k.pt_mp, k.pt_lower.view(), ptr)),
                None => final(tlb).spec_index((cpu_id, pcid)).is_empty(),
            },
    {
        self.cr3_pcid.flush_current(cpu_id, cr3, pcid, tlb, Ghost(k), Ghost(self.view().current_pagetable), Tracked(lctx));
    }

    /// The cpu's exec copy of (cr3, pcid) matches the physical register whenever the cpu is unlocked.
    pub closed spec fn cr3_matches_hardware(&self) -> bool { self.cr3_pcid.wf() }

    pub open spec fn wf(&self) -> bool {
        &&& self.cr3_matches_hardware()
        &&& self.view().state is Off ==> (self.view().current_process is None && self.view().current_thread is None)
        &&& self.view().state is Idle ==> (self.view().current_process is None && self.view().current_thread is None)
        &&& (self.view().state is Off ==> forall|pcid: Pcid| #![trigger self.tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> self.tlb_dirty_bitmap().spec_index(pcid) is None)
        &&& self.view().state is Running ==> (self.view().current_process is Some && self.view().current_thread is Some)
        &&& self.view().current_process is None == self.view().current_thread is None
        &&& self.view().current_process is None == self.view().current_pagetable is None
        &&& self.view().tlb_dirty_bitmap.inv()
    }

    pub open spec fn tlb_dirty_bitmap(&self) -> Map<Pcid, Option<ProcessPageTablePair>> { self.view().tlb_dirty_bitmap.view() }

    pub fn transfer_off_cpu_to_container(&mut self, container: RwLockContainerPtr, depth: usize)
        requires
            old(self).wf(),
            old(self).view().state is Off,
        ensures
            final(self).wf(),
            final(self).view() == (CpuView { owning_container: container, container_depth: depth, ..old(self).view() }),
            final(self).kernel_call_perm() == old(self).kernel_call_perm(),
    {
        self.owning_container = container;
        self.container_depth = depth;
    }

    /// Moves an Idle cpu to `container` at `depth`; it stays Idle with no current process or thread.
    pub fn transfer_idle_cpu_to_container(&mut self, container: RwLockContainerPtr, depth: usize)
        requires
            old(self).wf(),
            old(self).view().state is Idle,
        ensures
            final(self).wf(),
            final(self).view() == (CpuView { owning_container: container, container_depth: depth, ..old(self).view() }),
            final(self).kernel_call_perm() == old(self).kernel_call_perm(),
    {
        self.owning_container = container;
        self.container_depth = depth;
    }

    pub fn publish_idle_from_off(&mut self)
        requires
            old(self).wf(),
            old(self).view().state is Off,
        ensures
            final(self).wf(),
            final(self).view() == (CpuView { state: CpuState::Idle, ..old(self).view() }),
            final(self).kernel_call_perm() == old(self).kernel_call_perm(),
    {
        self.state = CpuState::Idle;
    }

    /// Publish Off from Idle with an empty dirty map; the caller has flushed every non-default PCID of this cpu.
    pub fn publish_off_from_idle(&mut self)
        requires
            old(self).wf(),
            old(self).view().state is Idle,
        ensures
            final(self).wf(),
            final(self).view() == (CpuView { state: CpuState::Off, tlb_dirty_bitmap: final(self).view().tlb_dirty_bitmap, ..old(self).view() }),
            forall|pcid: Pcid| #![trigger final(self).tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) ==> final(self).tlb_dirty_bitmap().spec_index(pcid) is None,
            final(self).kernel_call_perm() == old(self).kernel_call_perm(),
    {
        self.state = CpuState::Off;
        self.tlb_dirty_bitmap = BitMap::new_with_init_value(None);
    }
}

impl CpuLockedArray {
    /// TCB: write-lock the own cpu `cpu_id` unless a killer marked it, and enter its kernel step. When the lock is granted
    /// the cpu clears its interrupt flag under the lock guard; the lock then records the cpu as holder, the cpu's
    /// kernel-call permission moves from the cpu object into the local context, and its running state becomes InStep. A
    /// marked cpu returns `None` at once and nothing changes.
    #[verifier::external_body]
    pub fn wlock_own_cpu_enter_step(&mut self, cpu_id: CpuId, Tracked(cpu_op): Tracked<&mut CpuOpArray>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            0 <= cpu_id < NUM_CPUS,
            cpu_id == old(lctx).cpu_id(),
            !old(self).spec_index(cpu_id).view().locked() ==> old(self).spec_index(cpu_id).view().view().kernel_call_perm() == Some(cpu_id),
            !(old(self).spec_index(cpu_id).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(cpu_id).view().view_rodata().process_source() is Dynamic),
            wlock_requires(old(self).spec_index(cpu_id).view(), old(lctx)),
            !old(self).spec_index(cpu_id).view().being_killed() ==> old(lctx).lock_id_acyclic(old(self).lock_id_by_index(cpu_id)),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).entries_unchanged_except(old(self), cpu_id),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            (ret is None) == old(self).spec_index(cpu_id).view().being_killed(),
            ret is None ==> *final(self) == *old(self) && *final(lctx) == *old(lctx) && *final(cpu_op) == *old(cpu_op),
            ret is Some ==> {
                let pre = old(self).spec_index(cpu_id).view();
                let post = final(self).spec_index(cpu_id).view();
                let perm = ret->Some_0.view();
                &&& post.wlocked_by(final(lctx))
                &&& post.locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: perm.lock_id() }
                &&& post.inv()
                &&& post.view().view() == pre.view().view()
                &&& post.view().wf() == pre.view().wf()
                &&& post.view().kernel_call_perm() is None
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() == Some(cpu_id)
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
                &&& pre.locked() == false
                &&& perm.state() is WriteLock
                &&& post.locking_thread()->Write_lock_id == perm.lock_id()
                &&& perm.ordering_lock_id() == old(self).lock_id_by_index(cpu_id)
                &&& perm.thread_id() == final(lctx).thread_id()
            },
            ret is Some ==> lock_ensures(old(lctx), final(lctx), old(self).lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
            ret is Some ==> final(lctx).kernel_call_perm() == Some(cpu_id),
            ret is Some ==> final(cpu_op).view() == old(cpu_op).view().update(cpu_id as int, CpuOpState::InStep),
    {
        let ret = self.wlock_unless_killed_cli(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
        if ret.is_none() {
            return None;
        }
        let Tracked(perm) = ret.unwrap();
        self.set_ghost(cpu_id, Ghost(Some(cpu_id)), Tracked(&*lctx), Tracked(&perm));
        let cpu = self.borrow_mut(cpu_id, Tracked(&*lctx), Tracked(&perm));
        proof {
            let tracked token = cpu.take_kernel_call_perm();
            lctx.put_kernel_call_perm(Some(token));
            cpu_op.enter_step(cpu_id);
        }
        Some(Tracked(perm))
    }

    /// TCB: leave the kernel step of the own cpu `cpu_id` and release its lock. The cpu's running state becomes the resting
    /// state its scheduling state implies, its kernel-call permission moves from the local context back into the cpu object
    /// (it is there by linearity: only `wlock_own_cpu_enter_step` moves it in), the holder record is cleared, the cpu's
    /// pending running-to-idle request is dropped, and the cpu sets its interrupt flag after the release.
    #[verifier::external_body]
    pub fn exit_step_wunlock_own_cpu(&mut self, cpu_id: CpuId, Tracked(cpu_op): Tracked<&mut CpuOpArray>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            0 <= cpu_id < NUM_CPUS,
            cpu_id == old(lctx).cpu_id(),
            old(cpu_op).view()[cpu_id as int] is InStep,
            old(self).spec_index(cpu_id).view().view_ghost() == Some(cpu_id),
            !(old(self).spec_index(cpu_id).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(cpu_id).view().view_rodata().process_source() is Dynamic),
            old(self).spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).entries_unchanged_except(old(self), cpu_id),
            final(self).lock_id_by_index(cpu_id) == old(self).lock_id_by_index(cpu_id),
            ({
                let pre = old(self).spec_index(cpu_id).view();
                let post = final(self).spec_index(cpu_id).view();
                &&& post.locking_thread() == RwLockState::None
                &&& post.inv()
                &&& post.view().view() == pre.view().view()
                &&& post.view().wf() == pre.view().wf()
                &&& post.view().kernel_call_perm() == Some(cpu_id)
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() is None
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
            }),
            final(lctx).kernel_call_perm() is None,
            unlock_ensures(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id), old(self).lock_id_by_index(cpu_id)),
            final(cpu_op).view() == old(cpu_op).view().update(cpu_id as int, cpu_op_after_step(old(self).spec_index(cpu_id).view().view().view().state)),
    {
        let Tracked(lock_perm) = lock_perm;
        let cpu = self.borrow_mut(cpu_id, Tracked(&*lctx), Tracked(&lock_perm));
        proof {
            cpu_op.exit_step(cpu_id, cpu.state);
            let tracked slot = lctx.take_kernel_call_perm();
            cpu.put_kernel_call_perm(cpu_id, slot.tracked_unwrap());
        }
        self.set_ghost(cpu_id, Ghost(None), Tracked(&*lctx), Tracked(&lock_perm));
        unsafe { super::cpu_ipi::veriflat_clear_running_to_idle_pending(); }
        self.wunlock_sti(cpu_id, Tracked(&mut *lctx), Tracked(lock_perm), Ghost(KernelObjId::Cpu(cpu_id)));
    }

    pub fn block_current(&mut self, cpu_id: CpuId, default_cr3: PageTableRoot, tlb: &mut CpuTLB, needflush: &mut PcidNeedFlushArray, hw_cr3_pcid: &mut CpuHwCr3PcidArray, needflush_perm: Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, cpu_lock_perm: Tracked<&LockPerm>)
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
            old(hw_cr3_pcid)[cpu_id as int].owner_cpu() == cpu_id,
        ensures
            pcid_needflush_wf(*old(needflush)) ==> pcid_needflush_wf(*final(needflush)),
            cpu_hw_cr3_pcid_wf(*old(hw_cr3_pcid), *old(self), *old(needflush)) ==> cpu_hw_cr3_pcid_wf(*final(hw_cr3_pcid), *final(self), *final(needflush)),
            final(hw_cr3_pcid)[cpu_id as int].inv(),
            final(hw_cr3_pcid)[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID),
            final(hw_cr3_pcid)[cpu_id as int].owner_cpu() == old(hw_cr3_pcid)[cpu_id as int].owner_cpu(),
            forall|c: CpuId| #![trigger final(hw_cr3_pcid)[c as int]] #![trigger old(hw_cr3_pcid)[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> final(hw_cr3_pcid)[c as int] == old(hw_cr3_pcid)[c as int],
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
                index_valid(NUM_CPUS, c) && pcid_valid(p) ==>
                    final(tlb).spec_index((c, p)) == if old(needflush).spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush && c == cpu_id && p == KERNEL_DEFAULT_PCID { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } }
                    else { old(tlb).spec_index((c, p)) },
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
            final(self).spec_index(cpu_id).view().killer_info() == old(self).spec_index(cpu_id).view().killer_info(),
            final(self).spec_index(cpu_id).view().view_rodata() == old(self).spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(cpu_id).view().view_ghost() == old(self).spec_index(cpu_id).view().view_ghost(),
            final(self).typed_lock_map_aligned(old(lctx).cpu_lock_map().insert(cpu_id, TypedHeldLock { lock_id: final(self).spec_index(cpu_id).lock_id(), mode: TypedLockMode::Write }), final(lctx).thread_id()),
            final(self).spec_index(cpu_id).view().view().view() == (CpuView { state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None, current_cr3: default_cr3, current_pcid: KERNEL_DEFAULT_PCID, ..old(self).spec_index(cpu_id).view().view().view() }),
            final(self).spec_index(cpu_id).view().view().kernel_call_perm() == old(self).spec_index(cpu_id).view().view().kernel_call_perm(),
    {
        let pending = needflush.borrow_typed(cpu_id, KERNEL_DEFAULT_PCID, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm).needflush;
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        cpu.cr3_pcid.write(cpu_id, default_cr3, KERNEL_DEFAULT_PCID, pending, tlb, Ghost(arbitrary()), Ghost(None), Tracked(&mut *lctx));
        cpu.current_process = None;
        cpu.current_thread = None;
        cpu.current_pagetable = None;
        cpu.state = CpuState::Idle;
        hw_cr3_pcid[cpu_id].store(default_cr3, KERNEL_DEFAULT_PCID, Tracked(&*lctx));
        let entry = needflush.borrow_mut_typed(cpu_id, KERNEL_DEFAULT_PCID, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm);
        entry.set(false);
        proof {
            assert(needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id())) by { reveal(LockedArray2D::typed_lock_map_aligned); };
            block_current_eof(*old(self), *self, *old(needflush), *needflush, *old(hw_cr3_pcid), *hw_cr3_pcid, cpu_id, default_cr3);
            let flushed = tlb.spec_index((cpu_id, KERNEL_DEFAULT_PCID));
            if pending { assert(flushed.tlb_4k =~= Map::empty() && flushed.tlb_2m =~= Map::empty() && flushed.tlb_1g =~= Map::empty()); }
        }
    }

    /// Force the remote cpu `cpu_id`, which this thread write-holds, from running to idle: mark the cpu for `killer_info`,
    /// make it load the default page table with the default PCID, unmark it, and leave it idle. Its TLB entries, PCID flush
    /// flags, and dirty bitmap stay as they are. The running-to-idle IPI uses the target's kernel-call permission, which
    /// stays in the cpu object because the target is outside a kernel step while this thread holds its lock.
    pub fn ipi_remote_running_to_idle(
        &mut self, cpu_id: CpuId, default_cr3: PageTableRoot, killer_info: KillerInfo, hw_cr3_pcid: &mut CpuHwCr3PcidArray, Tracked(cpu_op): Tracked<&mut CpuOpArray>,
        Tracked(lctx): Tracked<&mut LocalContext>, cpu_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(self).spec_index(cpu_id).view().view().kernel_call_perm() == Some(cpu_id),
            !old(self).spec_index(cpu_id).view().being_killed(),
            !(old(cpu_op).view()[cpu_id as int] is InStep),
            page_ptr_valid(default_cr3),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != old(lctx).cpu_id(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).typed_lock_map_aligned(old(lctx).cpu_lock_map(), old(lctx).thread_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(self).spec_index(cpu_id).view().is_init(),
            old(self).spec_index(cpu_id).view().view().wf(),
            old(self).spec_index(cpu_id).view().view().view().state is Running,
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(self).spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(hw_cr3_pcid)[cpu_id as int].owner_cpu() == cpu_id,
        ensures
            final(hw_cr3_pcid)[cpu_id as int].inv(),
            final(hw_cr3_pcid)[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID),
            final(hw_cr3_pcid)[cpu_id as int].owner_cpu() == old(hw_cr3_pcid)[cpu_id as int].owner_cpu(),
            forall|c: CpuId| #![trigger final(hw_cr3_pcid)[c as int]] #![trigger old(hw_cr3_pcid)[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> final(hw_cr3_pcid)[c as int] == old(hw_cr3_pcid)[c as int],
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
            final(self).spec_index(cpu_id).view().killer_info() == old(self).spec_index(cpu_id).view().killer_info(),
            final(self).spec_index(cpu_id).view().view_rodata() == old(self).spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(cpu_id).view().view_ghost() == old(self).spec_index(cpu_id).view().view_ghost(),
            final(self).typed_lock_map_aligned(old(lctx).cpu_lock_map().insert(cpu_id, TypedHeldLock { lock_id: final(self).spec_index(cpu_id).lock_id(), mode: TypedLockMode::Write }), final(lctx).thread_id()),
            final(self).spec_index(cpu_id).view().view().view() == (CpuView { state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None, current_cr3: default_cr3, current_pcid: KERNEL_DEFAULT_PCID, ..old(self).spec_index(cpu_id).view().view().view() }),
            final(self).spec_index(cpu_id).view().view().kernel_call_perm() == old(self).spec_index(cpu_id).view().view().kernel_call_perm(),
            final(cpu_op).view() == old(cpu_op).view().update(cpu_id as int, CpuOpState::Idle),
    {
        proof { lctx.enter_kernel_view_release(); }
        assert(self.spec_index(cpu_id).view().wlocked_by(&*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        self.mark_kill(cpu_id, Tracked(&*lctx), killer_info);
        let ghost target_lock = self.spec_index(cpu_id).view();
        assert(self.typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        hw_cr3_pcid[cpu_id].ipi_remote_running_to_idle_raw(&mut cpu.cr3_pcid, cpu_id, default_cr3, Tracked(&mut *cpu_op), Tracked(cpu.kernel_call_perm.borrow().tracked_borrow()),
            Ghost(target_lock), Tracked(&*lctx));
        self.unkill(cpu_id, Tracked(&*lctx));
        assert(self.typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        cpu.current_process = None;
        cpu.current_thread = None;
        cpu.current_pagetable = None;
        cpu.state = CpuState::Idle;
    }

    /// Wake the remote cpu `cpu_id`, which this thread write-holds right after publishing it Idle from Off, out of
    /// `wait_until_online` with the wake-up IPI; the IPI uses the target's kernel-call permission in the cpu object.
    pub fn wake_remote(&self, cpu_id: CpuId, Tracked(cpu_op): Tracked<&mut CpuOpArray>, Tracked(lctx): Tracked<&LocalContext>, cpu_lock_perm: Tracked<&LockPerm>)
        requires
            self.inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != lctx.cpu_id(),
            lctx.kernel_view_locking_state() is Release,
            self.typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id()),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            self.spec_index(cpu_id).view().is_init(),
            self.spec_index(cpu_id).view().view().kernel_call_perm() == Some(cpu_id),
            self.spec_index(cpu_id).view().view().view().state is Idle,
            old(cpu_op).view()[cpu_id as int] is Off,
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == self.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            final(cpu_op).view() == old(cpu_op).view().update(cpu_id as int, CpuOpState::Idle),
    {
        let cpu = self.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(lctx), cpu_lock_perm);
        ipi_wake(cpu_id, Tracked(&mut *cpu_op), Tracked(cpu.kernel_call_perm.borrow().tracked_borrow()), Tracked(lctx));
    }

    /// Select a thread on this running or idle CPU without changing containers.
    pub fn switch_to_thread(
        &mut self, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, cr3: PageTableRoot,
        pcid: Pcid, process_depth: usize, tlb: &mut CpuTLB, needflush: &mut PcidNeedFlushArray, hw_cr3_pcid: &mut CpuHwCr3PcidArray, Ghost(k): Ghost<KernelK>,
        needflush_perm: Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, cpu_lock_perm: Tracked<&LockPerm>,
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
            old(hw_cr3_pcid)[cpu_id as int].owner_cpu() == cpu_id,
            k.pt_mp.dom().contains(pagetable_ptr),
            k.pt_mp.spec_index(pagetable_ptr).view().cr3 == cr3,
        ensures
            pcid_needflush_wf(*old(needflush)) ==> pcid_needflush_wf(*final(needflush)),
            cpu_hw_cr3_pcid_wf(*old(hw_cr3_pcid), *old(self), *old(needflush)) ==> cpu_hw_cr3_pcid_wf(*final(hw_cr3_pcid), *final(self), *final(needflush)),
            final(hw_cr3_pcid)[cpu_id as int].inv(),
            final(hw_cr3_pcid)[cpu_id as int].view() == (cr3, pcid),
            final(hw_cr3_pcid)[cpu_id as int].owner_cpu() == old(hw_cr3_pcid)[cpu_id as int].owner_cpu(),
            forall|c: CpuId| #![trigger final(hw_cr3_pcid)[c as int]] #![trigger old(hw_cr3_pcid)[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> final(hw_cr3_pcid)[c as int] == old(hw_cr3_pcid)[c as int],
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
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) && (other_cpu != cpu_id || other_pcid != pcid)
                    ==> final(tlb).spec_index((other_cpu, other_pcid)) == old(tlb).spec_index((other_cpu, other_pcid)),
            {
                let entry = old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let flush = old(needflush).spec_index(cpu_id, pcid).view().needflush || (entry is Some && (entry.unwrap().process_ptr != process_ptr || entry.unwrap().pagetable_ptr != pagetable_ptr));
                &&& (!flush ==> *final(tlb) == *old(tlb))
                &&& final(tlb).view() == if flush { old(tlb).view().insert((cpu_id, pcid), final(tlb).spec_index((cpu_id, pcid))) } else { old(tlb).view() }
                &&& flush ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(tlb).spec_index((cpu_id, pcid)), pagetable_c(k.pt_mp, k.pt_lower.view(), pagetable_ptr))
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
            final(self).spec_index(cpu_id).view().killer_info() == old(self).spec_index(cpu_id).view().killer_info(),
            final(self).spec_index(cpu_id).view().view_rodata() == old(self).spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(cpu_id).view().view_ghost() == old(self).spec_index(cpu_id).view().view_ghost(),
            final(self).typed_lock_map_aligned(old(lctx).cpu_lock_map().insert(cpu_id, TypedHeldLock { lock_id: final(self).spec_index(cpu_id).lock_id(), mode: TypedLockMode::Write }), final(lctx).thread_id()),
            final(self).spec_index(cpu_id).view().view().view() == (CpuView { state: CpuState::Running, current_process: Some(process_ptr), current_thread: Some(thread_ptr),
                current_pagetable: Some(pagetable_ptr), current_cr3: cr3, current_pcid: pcid, process_depth, tlb_dirty_bitmap: final(self).spec_index(cpu_id).view().view().view().tlb_dirty_bitmap,
                ..old(self).spec_index(cpu_id).view().view().view() }),
            final(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap() == old(self).spec_index(cpu_id).view().view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr, pagetable_ptr })),
            final(self).spec_index(cpu_id).view().view().kernel_call_perm() == old(self).spec_index(cpu_id).view().view().kernel_call_perm(),
    {
        let pending = needflush.borrow_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm).needflush;
        let cpu = self.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_lock_perm);
        let dirty = cpu.tlb_dirty_bitmap.index(pcid);
        let flush = pending || match dirty {
            Some(entry) => entry.process_ptr != process_ptr || entry.pagetable_ptr != pagetable_ptr,
            None => false,
        };
        cpu.cr3_pcid.write(cpu_id, cr3, pcid, flush, tlb, Ghost(k), Ghost(Some(pagetable_ptr)), Tracked(&mut *lctx));
        cpu.state = CpuState::Running;
        cpu.current_process = Some(process_ptr);
        cpu.current_thread = Some(thread_ptr);
        cpu.current_pagetable = Some(pagetable_ptr);
        cpu.process_depth = process_depth;
        cpu.tlb_dirty_bitmap.update(pcid, Some(ProcessPageTablePair { process_ptr, pagetable_ptr }));
        hw_cr3_pcid[cpu_id].store(cr3, pcid, Tracked(&*lctx));
        let entry = needflush.borrow_mut_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(&*lctx), needflush_perm);
        entry.set(false);
        proof {
            assert(needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id())) by { reveal(LockedArray2D::typed_lock_map_aligned); };
            switch_to_thread_eof(*old(self), *self, *old(needflush), *needflush, *old(hw_cr3_pcid), *hw_cr3_pcid, cpu_id, cr3, pcid);
        }
    }
}

impl LockInvTrait for Cpu {
    open spec fn inv(&self) -> bool {
        &&& self.wf()
    }
}

impl LockMajorTrait for Cpu {
    open spec fn lock_major_1(&self) -> LockMajorId { CPU_LOCK_MAJOR_RUNNING }
    open spec fn lock_major_2(&self) -> LockMajorId { CPU_LOCK_MAJOR_IDLE }
    open spec fn lock_major_3(&self) -> LockMajorId { CPU_LOCK_MAJOR_OFF }
    open spec fn lock_major_default(&self) -> LockMajorId { PAGE_TABLE_LOCK_MAJOR }
    open spec fn lock_major_1_predicate(&self) -> bool { self.view().state is Running }
    open spec fn lock_major_2_predicate(&self) -> bool { self.view().state is Idle }
    open spec fn lock_major_3_predicate(&self) -> bool { self.view().state is Off }
    open spec fn lock_major_default_predicate(&self) -> bool { true }
}

impl LockOwnerIdTrait for Cpu {
    open spec fn container_depth(&self) -> LockOwnerId {
        if self.view().state is Off { LockOwnerId::None } else { LockOwnerId::Some(self.view().container_depth) }
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        if self.view().current_process is Some { LockOwnerId::Some(self.view().process_depth) } else { LockOwnerId::None }
    }
}
}

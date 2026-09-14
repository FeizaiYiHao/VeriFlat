use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::schedule_switch_unchanged_objects_and_entries_transition_framing;
use super::syscall_schedule_eof::schedule_switch_eof;

verus! {
pub enum ScheduleResult {
    Off,
    Idle,
    Continue,
    /// The trap-return layer encodes this pending IPC result in the restored registers.
    Switched { thread_ptr: RwLockThreadPtr, syscall_return: Option<RetValueType> },
}

/// Timer entry for a user context or the idle loop. Kernel execution is not
/// preemptible; the entry layer binds `lctx` to this CPU and restores `pt_regs`.
pub fn syscall_schedule(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    pt_regs: &mut Registers,
) -> (ret: ScheduleResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(steps).steps.len() == 0,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(steps).steps.len() == if ret is Switched { 1nat } else { 0nat },
        (ret is Off) == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        (ret is Switched) == {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let scheduler_ptr = old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler;
            let queue = old(krnl).sched_mp.spec_index(scheduler_ptr).view().queue.view();
            &&& !(cpu.state is Off)
            &&& (cpu.current_process is Some ==> !old(krnl).prc_mp.spec_index(cpu.current_process.unwrap()).being_killed() && !old(krnl).thr_mp.spec_index(cpu.current_thread.unwrap()).being_killed())
            &&& queue.len() > 0
            &&& !old(krnl).thr_mp.spec_index(queue[0]).being_killed()
        },
        ret is Off ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        ret is Idle ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Idle,
        ret is Continue ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !(ret is Switched) ==> {
            &&& *final(pt_regs) == *old(pt_regs)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
        },
        !(ret is Switched) ==> kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        ret is Switched ==> final(steps).steps[0].old_u == kernel_k_to_kernel_u(*old(krnl)) && final(steps).steps[0].new_u == kernel_k_to_kernel_u(*final(krnl)),
        forall|other_cpu: CpuId|
            #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
        ret is Switched ==> {
            let next = ret->Switched_thread_ptr;
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let scheduler_ptr = old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler;
            let queue = old(krnl).sched_mp.spec_index(scheduler_ptr).view().queue.view();
            &&& queue.len() > 0
            &&& next == queue[0]
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(next)
            &&& final(krnl).thr_mp.spec_index(next).view().state == (ThreadState::RUNNING { cpu_id })
            &&& *final(pt_regs) == *old(krnl).thr_mp.spec_index(next).view().trap_frame.get_some_0()
            &&& ret->Switched_syscall_return == old(krnl).thr_mp.spec_index(next).view().error_code
            &&& final(krnl).thr_mp.spec_index(next).view().error_code is None
            &&& final(krnl).sched_mp.spec_index(scheduler_ptr).view().queue.view() == match cpu.current_thread { Some(ptr) => queue.skip(1).push(ptr), None => queue.skip(1) }
            &&& (cpu.current_thread is Some ==> {
                let prev = cpu.current_thread.unwrap();
                &&& final(krnl).thr_mp.spec_index(prev).view().state is SCHEDULED
                &&& *final(krnl).thr_mp.spec_index(prev).view().trap_frame.get_some_0() == *old(pt_regs)
            })
        },
{
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let state = cpu.state();
    let container_ptr = cpu.owning_container();
    let current_process = cpu.current_process();
    let current_thread = cpu.current_thread();
    assert(steps.snap_shot.cpu_array[cpu_id as int].current_thread == current_thread) by { krnl.cpu_arr.lemma_view_index(cpu_id); };
    if let CpuState::Off = state {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
        return ScheduleResult::Off;
    }
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
            &&& (current_process is Some ==> krnl.prc_mp.dom().contains(current_process.unwrap()))
            &&& current_process is Some == current_thread is Some
            &&& (current_process is Some ==> state is Running)
            &&& (current_process is Some ==> krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().owning_container == container_ptr)
            &&& (current_thread is Some ==> {
                let ptr = current_thread.unwrap();
                &&& krnl.thr_mp.dom().contains(ptr)
                &&& krnl.thr_mp.spec_index(ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(ptr).view().owning_proc == current_process.unwrap()
                &&& krnl.thr_mp.spec_index(ptr).view().owning_container == container_ptr
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view().owned_threads.view().contains(ptr)
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view().owned_threads.view().len() != 0
            })
        }) by { reveal(container_cpu_wf); reveal(container_perms_wf); reveal(thread_cpu_wf); reveal(process_cpu_wf); reveal(process_thread_wf); };
    }
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let mut process_lock_perm: Option<Tracked<LockPerm>> = None;
    let mut current_thread_lock_perm: Option<Tracked<LockPerm>> = None;
    if let Some(process_ptr) = current_process {
        let res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
        if !res.0 {
            release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
            return ScheduleResult::Continue;
        }
        process_lock_perm = res.1;
        let thread_ptr = current_thread.unwrap();
        let res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
        if !res.0 {
            release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, process_lock_perm.unwrap(), Tracked(cpu_lock_perm));
            return ScheduleResult::Continue;
        }
        current_thread_lock_perm = res.1;
    }
    assert(krnl.sched_mp.dom().contains(scheduler_ptr)) by { reveal(container_scheduler_wf); };
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));
    assert({
        &&& krnl.sched_mp.perms_wf()
        &&& krnl.sched_mp.spec_index(scheduler_ptr).view().inv()
        &&& krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().len() == krnl.sched_mp.spec_index(scheduler_ptr).view().queue.len()
        &&& krnl.sched_mp.spec_index(scheduler_ptr).view().owning_container == container_ptr
        &&& (current_thread is Some ==> !krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(current_thread.unwrap()))
    }) by { reveal(scheduler_perms_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(LinkedList::wf_value_list); };
    let scheduler = krnl.sched_mp.borrow_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
    let mut next: Option<(RwLockThreadPtr, usize, Tracked<LockPerm>)> = None;
    if scheduler.queue.len() != 0 {
        let (node_addr, thread_ptr) = scheduler.queue.peek_head();
        assert(krnl.thr_mp.dom().contains(thread_ptr) && krnl.thr_mp.spec_index(thread_ptr).view().state is SCHEDULED && krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr) by { reveal(container_thread_scheduler_wf); };
        let res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
        if res.0 { next = Some((thread_ptr, node_addr, res.1.unwrap())); }
    }
    let ret;
    if let Some((next_thread, next_node, next_perm)) = next {
        let tracked next_lock_perm = next_perm.get();
        let thread = krnl.thr_mp.borrow_typed(next_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&next_lock_perm));
        let next_process = thread.owning_proc;
        assert(krnl.prc_mp.dom().contains(next_process) && !krnl.prc_mp.spec_index(next_process).view().zombie && krnl.prc_mp.spec_index(next_process).is_init() && krnl.prc_mp.view().spec_index(next_process).is_init() && krnl.prc_mp.view().spec_index(next_process).addr() == next_process) by { reveal(process_thread_wf); reveal(process_perms_wf); };
        let process = krnl.prc_mp.borrow_rodata(next_process).borrow();
        let next_pagetable = process.pagetable;
        let cr3 = process.cr3;
        let pcid = process.pcid;
        let depth = process.depth;
        assert(page_ptr_valid(cr3) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(process_perms_wf); reveal(pagetable_perms_wf); reveal(process_pcid_allocator_wf); reveal(PageTable::table_pages_wf); };
        assert(next_node == krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()) by {
            reveal(container_thread_scheduler_wf);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_value_list);
            krnl.sched_mp.spec_index(scheduler_ptr).view().queue.lemma_value_addr_unique(next_node, krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr());
        };
        let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
        let ghost before_switch = *krnl;
        krnl.cpu_arr.switch_to_thread(cpu_id, next_process, next_thread, next_pagetable, cr3, pcid, depth, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));
        proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), before_switch.cpu_arr.lock_id_by_index(cpu_id), krnl.cpu_arr.lock_id_by_index(cpu_id)); }
        let scheduler = krnl.sched_mp.borrow_mut_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
        let (_, node_perm) = scheduler.queue.pop_head();
        if let Some(prev) = current_thread {
            let ghost old_prev_lock_id = krnl.thr_mp.lock_id_by_key(prev);
            let prev_perm = current_thread_lock_perm.as_ref().unwrap();
            let previous = krnl.thr_mp.borrow_mut_typed(prev, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(prev_perm.borrow()));
            let (addr, perm) = previous.running_to_scheduled(prev, pt_regs);
            let scheduler = krnl.sched_mp.borrow_mut_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
            scheduler.enqueue_scheduled_thread(prev, addr, perm);
            proof { lctx.update_lock_id(KernelObjId::Thread(prev), old_prev_lock_id, krnl.thr_mp.lock_id_by_key(prev)); }
        }
        let target = krnl.thr_mp.borrow_mut_typed(next_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&next_lock_perm));
        let syscall_return = target.scheduled_to_running(cpu_id, node_perm, pt_regs);
        proof {
            lctx.update_lock_id(KernelObjId::Thread(next_thread), before_switch.thr_mp.lock_id_by_key(next_thread), krnl.thr_mp.lock_id_by_key(next_thread));
            assert(krnl.inv()) by {
                assert(schedule_switch_unchanged_objects_and_entries_transition_framing(before_switch, *krnl, cpu_id, scheduler_ptr, next_thread, *old(pt_regs))) by { reveal(schedule_switch_unchanged_objects_and_entries_transition_framing); };
                schedule_switch_eof(before_switch, *krnl, cpu_id, scheduler_ptr, next_thread, *old(pt_regs));
            };
        }
        krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
        krnl.wunlock_thread(next_thread, Tracked(&mut *lctx), Tracked(next_lock_perm));
        ret = ScheduleResult::Switched { thread_ptr: next_thread, syscall_return };
    } else {
        ret = if let CpuState::Idle = state { ScheduleResult::Idle } else { ScheduleResult::Continue };
    }
    krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    if let Some(perm) = current_thread_lock_perm { krnl.wunlock_thread(current_thread.unwrap(), Tracked(&mut *lctx), perm); }
    if let Some(perm) = process_lock_perm { krnl.wunlock_process(current_process.unwrap(), Tracked(&mut *lctx), perm); }
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    ret
}
}

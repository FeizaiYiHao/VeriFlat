use vstd::prelude::*;
use crate::*;
use super::syscall_schedule::ScheduleResult;

verus! {
/// The result of `syscall_schedule` from the state at entry: an Off cpu stays Off; a cpu whose running
/// process and thread, if any, are alive switches to the live head of its container's scheduler queue
/// and carries that thread's pending IPC result; otherwise an Idle cpu stays Idle and a running cpu
/// continues.
pub open spec fn schedule_syscall_result(pre: KernelU, cpu_id: CpuId) -> ScheduleResult {
    let cpu = pre.cpu_array[cpu_id as int];
    let queue = pre.container_map[cpu.owning_container].scheduler;
    if cpu.state is Off { ScheduleResult::Off }
    else if (cpu.current_process is Some ==> !pre.process_map[cpu.current_process->Some_0].killed && !pre.thread_map[cpu.current_thread->Some_0].killed)
        && queue.len() > 0 && !pre.thread_map[queue[0]].killed {
        ScheduleResult::Switched { thread_ptr: queue[0], syscall_return: pre.thread_map[queue[0]].error_code }
    } else if cpu.state is Idle { ScheduleResult::Idle }
    else { ScheduleResult::Continue }
}

#[verifier::opaque]
/// Switches the CPU to the scheduler queue head, optionally requeues the
/// previous thread, and updates the affected PCID publication and TLB state.
pub open spec fn scheduler_context_switch_transition(
    pre: KernelK, post: KernelK, cpu_id: CpuId,
    scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr,
    entry_regs: Registers,
) -> bool {
    let cpu_before = pre.cpu_arr.spec_index(cpu_id).view();
    let cpu_after = post.cpu_arr.spec_index(cpu_id).view();
    let old_cpu = cpu_before.view().view();
    let new_cpu = cpu_after.view().view();
    let previous = old_cpu.current_thread;
    let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
    let target = pre.prc_mp.spec_index(next_process).view_rodata().view();
    let pcid = target.pcid;
    let dirty = cpu_before.view().tlb_dirty_bitmap().spec_index(pcid);
    let flush = pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush
        || (dirty is Some && (dirty.unwrap().process_ptr != next_process || dirty.unwrap().pagetable_ptr != target.pagetable));
    let scheduler_before = pre.sched_mp.spec_index(scheduler_ptr);
    let scheduler_after = post.sched_mp.spec_index(scheduler_ptr);
    let queue_before = scheduler_before.view().queue;
    let queue_after = scheduler_after.view().queue;
    let next_node = pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr();
    let needflush_before = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let needflush_after = post.pcid_needflush.spec_index(cpu_id, pcid);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& !(old_cpu.state is Off)
    &&& pre.thr_mp.dom().contains(next_thread)
    &&& pre.prc_mp.dom().contains(next_process)
    &&& pre.sched_mp.dom().contains(scheduler_ptr)
    &&& pre.ctn_mp.dom().contains(old_cpu.owning_container)
    &&& pcid_valid(pcid)
    &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
    &&& scheduler_before.view().owning_container == old_cpu.owning_container
    &&& pre.thr_mp.spec_index(next_thread).view().owning_container == old_cpu.owning_container
    &&& pre.ctn_mp.spec_index(old_cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
    &&& queue_before.view().len() > 0
    &&& queue_before.view()[0] == next_thread
    &&& (previous is Some ==> {
        let prev = previous.unwrap();
        &&& prev != next_thread
        &&& pre.thr_mp.dom().contains(prev)
        &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
    })
    &&& post == (KernelK {
        cpu_arr: post.cpu_arr,
        pcid_needflush: post.pcid_needflush,
        cpu_published: post.cpu_published,
        sched_mp: post.sched_mp,
        thr_mp: post.thr_mp,
        cpu_tlb: post.cpu_tlb,
        ..pre
    })
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& (forall|c: CpuId|
        #![trigger pre.cpu_arr.spec_index(c)]
        #![trigger post.cpu_arr.spec_index(c)]
        index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_arr.spec_index(c) == pre.cpu_arr.spec_index(c))
    &&& cpu_after.is_init() == cpu_before.is_init()
    &&& cpu_after.view_rodata() == cpu_before.view_rodata()
    &&& cpu_after.view_ghost() == cpu_before.view_ghost()
    &&& cpu_after.being_killed() == cpu_before.being_killed()
    &&& cpu_after.locking_thread() == cpu_before.locking_thread()
    &&& new_cpu == (CpuView {
        state: CpuState::Running, current_process: Some(next_process),
        current_thread: Some(next_thread), current_pagetable: Some(target.pagetable),
        current_cr3: target.cr3, current_pcid: pcid, process_depth: target.depth,
        tlb_dirty_bitmap: new_cpu.tlb_dirty_bitmap, ..old_cpu
    })
    &&& cpu_after.view().tlb_dirty_bitmap() == cpu_before.view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr: next_process, pagetable_ptr: target.pagetable }))
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& (forall|ptr: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(ptr)]
        #![trigger post.thr_mp.spec_index(ptr)]
        pre.thr_mp.dom().contains(ptr) ==> {
            let before = pre.thr_mp.spec_index(ptr);
            let after = post.thr_mp.spec_index(ptr);
            &&& post.thr_mp.view().spec_index(ptr).is_init() == pre.thr_mp.view().spec_index(ptr).is_init()
            &&& post.thr_mp.view().spec_index(ptr).addr() == pre.thr_mp.view().spec_index(ptr).addr()
            &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
            &&& after.view().endpoint_descriptors == before.view().endpoint_descriptors
            &&& (ptr != next_thread && previous != Some(ptr) ==> after == before)
            &&& (ptr == next_thread || previous == Some(ptr) ==> {
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.locking_thread() == before.locking_thread()
                &&& after.view() == (Thread {
                    state: if ptr == next_thread { ThreadState::RUNNING { cpu_id } } else { ThreadState::SCHEDULED },
                    error_code: None, trap_frame: after.view().trap_frame, temp_alloc_cache_1g: after.view().temp_alloc_cache_1g,
                    scheduler_linkedlist_node: after.view().scheduler_linkedlist_node, ..before.view()
                })
                &&& after.view().scheduler_linkedlist_node.addr() == before.view().scheduler_linkedlist_node.addr()
                &&& after.view().scheduler_linkedlist_node.is_init() == (ptr == next_thread)
                &&& (ptr == next_thread ==> after.view().trap_frame.is_none())
                &&& (previous == Some(ptr) ==> after.view().trap_frame.is_some() && *after.view().trap_frame.get_some_0() == entry_regs)
            })
        })
    &&& post.sched_mp.dom() == pre.sched_mp.dom()
    &&& (forall|ptr: RwLockSchedulerPtr|
        #![trigger pre.sched_mp.spec_index(ptr)]
        #![trigger post.sched_mp.spec_index(ptr)]
        pre.sched_mp.dom().contains(ptr) ==> {
            &&& post.sched_mp.view().spec_index(ptr).is_init() == pre.sched_mp.view().spec_index(ptr).is_init()
            &&& post.sched_mp.view().spec_index(ptr).addr() == pre.sched_mp.view().spec_index(ptr).addr()
            &&& (ptr != scheduler_ptr ==> post.sched_mp.spec_index(ptr) == pre.sched_mp.spec_index(ptr))
        })
    &&& scheduler_after.is_init() == scheduler_before.is_init()
    &&& scheduler_after.view_rodata() == scheduler_before.view_rodata()
    &&& scheduler_after.view_ghost() == scheduler_before.view_ghost()
    &&& scheduler_after.being_killed() == scheduler_before.being_killed()
    &&& scheduler_after.locking_thread() == scheduler_before.locking_thread()
    &&& scheduler_after.view() == (Scheduler { queue: queue_after, ..scheduler_before.view() })
    &&& queue_after.container_depth == queue_before.container_depth
    &&& queue_after.lock_minor() == queue_before.lock_minor()
    &&& queue_after.view() == match previous { Some(prev) => queue_before.view().skip(1).push(prev), None => queue_before.view().skip(1) }
    &&& (previous is Some ==> !queue_before.map().remove(next_node).dom().contains(pre.thr_mp.spec_index(previous.unwrap()).view().scheduler_linkedlist_node.addr()))
    &&& queue_after.length as int == queue_before.length as int - 1 + if previous is Some { 1int } else { 0int }
    &&& queue_after.map() == match previous {
        Some(prev) => queue_before.map().remove(next_node).insert(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr(), prev),
        None => queue_before.map().remove(next_node),
    }
    &&& queue_after.dom() == match previous {
        Some(prev) => queue_before.dom().remove(next_node).insert(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr()),
        None => queue_before.dom().remove(next_node),
    }
    &&& needflush_after.view().index() == needflush_before.view().index()
    &&& needflush_after.is_init() == needflush_before.is_init()
    &&& needflush_after.view_rodata() == needflush_before.view_rodata()
    &&& needflush_after.view_ghost() == needflush_before.view_ghost()
    &&& needflush_after.being_killed() == needflush_before.being_killed()
    &&& needflush_after.locking_thread() == needflush_before.locking_thread()
    &&& needflush_after.view() == (PcidNeedFlush { needflush: false, ..needflush_before.view() })
    &&& (forall|c: CpuId, p: Pcid|
        #![trigger pre.pcid_needflush.spec_index(c, p)]
        #![trigger post.pcid_needflush.spec_index(c, p)]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
    &&& post.cpu_published[cpu_id as int].owner_cpu() == pre.cpu_published[cpu_id as int].owner_cpu()
    &&& post.cpu_published[cpu_id as int].view() == (target.cr3, pcid)
    &&& (forall|c: CpuId|
        #![trigger pre.cpu_published[c as int]]
        #![trigger post.cpu_published[c as int]]
        index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_published[c as int] == pre.cpu_published[c as int])
    &&& post.cpu_tlb.view() == if flush {
        pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    } else { pre.cpu_tlb.view() }
    &&& (forall|c: CpuId, p: Pcid|
        #![trigger pre.cpu_tlb.spec_index((c, p))]
        #![trigger post.cpu_tlb.spec_index((c, p))]
        index_valid(NUM_CPUS, c) && pcid_valid(p) ==> post.cpu_tlb.spec_index((c, p)) == if flush && c == cpu_id && p == pcid {
            SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
        } else { pre.cpu_tlb.spec_index((c, p)) })
}

/// The PCID whose `(cpu_id, pcid)` TLB entry the switch to `next_thread` flushes, if any.
pub open spec fn schedule_flushed_pcid(pre: KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr) -> Option<Pcid> {
    let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
    let target = pre.prc_mp.spec_index(next_process).view_rodata().view();
    let pcid = target.pcid;
    let dirty = pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
    if pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush
        || (dirty is Some && (dirty.unwrap().process_ptr != next_process || dirty.unwrap().pagetable_ptr != target.pagetable)) {
        Some(pcid)
    } else { None }
}

/// User-visible precondition of the scheduler switch step on `cpu_id`; the cpu, the next thread, and
/// any current thread and process are unlocked.
#[verifier::opaque]
pub open spec fn schedule_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let next_thread = container.scheduler[0];
    let next = old_u.thread_map.spec_index(next_thread);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& container.scheduler.len() > 0
    &&& old_u.thread_map.dom().contains(next_thread)
    &&& next.lock_state is Unlocked
    &&& !next.killed
    &&& next.state is SCHEDULED
    &&& next.owning_container == cpu.owning_container
    &&& old_u.process_map.dom().contains(next.owning_proc)
    &&& cpu.current_process is Some == cpu.current_thread is Some
    &&& (cpu.current_thread is Some ==> {
        let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
        &&& cpu.current_thread.unwrap() != next_thread
        &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
        &&& prev.lock_state is Unlocked
        &&& !prev.killed
        &&& prev.state == (ThreadState::RUNNING { cpu_id })
        &&& prev.owning_proc == cpu.current_process.unwrap()
        &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
        &&& old_u.process_map.spec_index(cpu.current_process.unwrap()).lock_state is Unlocked
        &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
    })
}

/// User-visible scheduler switch step: `cpu_id` runs the head of its container's scheduler,
/// the previous thread is requeued at the tail, and at most one PCID TLB entry is flushed.
pub open spec fn schedule_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, entry_regs: Registers, flushed_pcid: Option<Pcid>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    kernel_u_context_switch_changed(old_u, new_u, cpu_id, old_u.container_map.spec_index(cpu.owning_container).scheduler[0], entry_regs, flushed_pcid)
}

/// Complete trace of one scheduling call, including its unchanged lock modes.
#[verifier::opaque]
pub open spec fn schedule_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, switched: bool, flushed_pcid: Option<Pcid>) -> bool {
    if switched {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& schedule_step_pre(pre, cpu_id)
        &&& schedule_step(pre, post, cpu_id, regs, flushed_pcid)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
}

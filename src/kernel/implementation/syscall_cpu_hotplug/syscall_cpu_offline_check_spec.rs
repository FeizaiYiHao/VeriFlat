use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_offline_check::OfflineCheckResult;

verus! {
/// The result of `cpu_offline_check` from the state where it decides, the entry for an early Continue and otherwise the
/// snapshot after the hold under the held cpu lock: a cpu a killer marked, a clear request bit, a cpu set a killer
/// marked, or a killed running process or thread continue to the scheduler; otherwise the cpu goes Off.
pub open spec fn cpu_offline_check_result(pre: KernelU, cpu_id: CpuId) -> OfflineCheckResult {
    let cpu = pre.cpu_array[cpu_id as int];
    if cpu.killed || !pre.container_map[cpu.owning_container].cpu_offline_requests[cpu_id as int] || pre.container_map[cpu.owning_container].cpu_set_killed
        || (cpu.current_process is Some && (pre.process_map[cpu.current_process->Some_0].killed || pre.thread_map[cpu.current_thread->Some_0].killed)) {
        OfflineCheckResult::Continue
    } else { OfflineCheckResult::Off }
}

/// K-internal label: a running cpu flushes its default-PCID TLB entry while going Off exactly when the
/// entry's needflush mark is pending; an idle cpu leaves it alone.
pub open spec fn cpu_offline_check_flushed_default_pcid(pre: KernelK, cpu_id: CpuId) -> bool {
    pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush
}

/// Operation-state summary of the committed offline of `cpu_id` under every lock the check acquired: the
/// running thread, if any, is requeued at the tail of shard `cpu_id` of `scheduler_ptr`, the cpu publishes the default page
/// table and goes Off with an empty dirty map, its TLB entries are flushed, its slot in `cpu_set_ptr` is
/// closed, and its request cell in `flags_ptr` is cleared.
#[verifier::opaque]
pub(super) open spec fn cpu_went_off_eof_transition_framing(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
    cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers,
) -> bool {
    let cpu_before = pre.cpu_arr.spec_index(cpu_id).view();
    let cpu_after = post.cpu_arr.spec_index(cpu_id).view();
    let old_cpu = cpu_before.view().view();
    let new_cpu = cpu_after.view().view();
    let previous = old_cpu.current_thread;
    let flush_default = old_cpu.state is Running && pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush;
    let scheduler_before = pre.sched_mp.spec_index(scheduler_ptr);
    let scheduler_after = post.sched_mp.spec_index(scheduler_ptr);
    let shard_before = scheduler_before.shards.spec_index(cpu_id).view();
    let shard_after = scheduler_after.shards.spec_index(cpu_id).view();
    let queue_before = shard_before.view().queue;
    let queue_after = shard_after.view().queue;
    let needflush_before = pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID);
    let needflush_after = post.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID);
    let cpu_set_before = pre.cpu_set_mp.spec_index(cpu_set_ptr);
    let cpu_set_after = post.cpu_set_mp.spec_index(cpu_set_ptr);
    let table_before = pre.cpu_offline_mp.spec_index(flags_ptr);
    let table_after = post.cpu_offline_mp.spec_index(flags_ptr);
    let cell_before = table_before.flags.spec_index(cpu_id).view();
    let cell_after = table_after.flags.spec_index(cpu_id).view();
    &&& post == (KernelK {
        cpu_arr: post.cpu_arr, pcid_needflush: post.pcid_needflush, cpu_hw_cr3_pcid: post.cpu_hw_cr3_pcid, cpu_tlb: post.cpu_tlb,
        sched_mp: post.sched_mp, thr_mp: post.thr_mp, cpu_set_mp: post.cpu_set_mp, cpu_offline_mp: post.cpu_offline_mp, ..pre
    })
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& (forall|c: CpuId| #![trigger pre.cpu_arr.spec_index(c)] #![trigger post.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_arr.spec_index(c) == pre.cpu_arr.spec_index(c))
    &&& cpu_after.is_init() == cpu_before.is_init()
    &&& cpu_after.view_rodata() == cpu_before.view_rodata()
    &&& cpu_after.view_ghost() == cpu_before.view_ghost()
    &&& cpu_after.being_killed() == cpu_before.being_killed()
    &&& cpu_after.killer_info() == cpu_before.killer_info()
    &&& cpu_after.locking_thread() == cpu_before.locking_thread()
    &&& cpu_after.view().kernel_call_perm() == cpu_before.view().kernel_call_perm()
    &&& new_cpu == (CpuView {
        state: CpuState::Off, current_process: None, current_thread: None, current_pagetable: None, current_cr3: pre.dflt_pt.view().cr3,
        current_pcid: KERNEL_DEFAULT_PCID, tlb_dirty_bitmap: new_cpu.tlb_dirty_bitmap, ..old_cpu
    })
    &&& (forall|pcid: Pcid| #![trigger cpu_after.view().tlb_dirty_bitmap().spec_index(pcid)] pcid_valid(pcid) ==> cpu_after.view().tlb_dirty_bitmap().spec_index(pcid) is None)
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& (forall|ptr: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(ptr)] #![trigger post.thr_mp.spec_index(ptr)] pre.thr_mp.dom().contains(ptr) ==> {
        let before = pre.thr_mp.spec_index(ptr);
        let after = post.thr_mp.spec_index(ptr);
        &&& post.thr_mp.view().spec_index(ptr).is_init() == pre.thr_mp.view().spec_index(ptr).is_init()
        &&& post.thr_mp.view().spec_index(ptr).addr() == pre.thr_mp.view().spec_index(ptr).addr()
        &&& (previous != Some(ptr) ==> after == before)
        &&& (previous == Some(ptr) ==> {
            &&& after.is_init() == before.is_init()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.view_ghost() == before.view_ghost()
            &&& after.being_killed() == before.being_killed()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.view() == (Thread { state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: after.view().trap_frame, scheduler_linkedlist_node: after.view().scheduler_linkedlist_node, ..before.view() })
            &&& after.view().scheduler_linkedlist_node.addr() == before.view().scheduler_linkedlist_node.addr()
            &&& !after.view().scheduler_linkedlist_node.is_init()
            &&& after.view().trap_frame.is_some()
            &&& *after.view().trap_frame.get_some_0() == entry_regs
        })
    })
    &&& post.sched_mp.unchanged_except(&pre.sched_mp, scheduler_ptr)
    &&& scheduler_after.owning_container == scheduler_before.owning_container
    &&& scheduler_after.shards.entries_unchanged_except(&scheduler_before.shards, cpu_id)
    &&& shard_after.is_init() == shard_before.is_init()
    &&& shard_after.view_rodata() == shard_before.view_rodata()
    &&& shard_after.view_ghost() == shard_before.view_ghost()
    &&& shard_after.being_killed() == shard_before.being_killed()
    &&& shard_after.locking_thread() == shard_before.locking_thread()
    &&& queue_after.view() == match previous { Some(prev) => queue_before.view().push(prev), None => queue_before.view() }
    &&& queue_after.length as int == queue_before.length as int + if previous is Some { 1int } else { 0int }
    &&& queue_after.map() == match previous { Some(prev) => queue_before.map().insert(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr(), prev), None => queue_before.map() }
    &&& queue_after.dom() == match previous { Some(prev) => queue_before.dom().insert(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr()), None => queue_before.dom() }
    &&& needflush_after.view().index() == needflush_before.view().index()
    &&& needflush_after.is_init() == needflush_before.is_init()
    &&& needflush_after.view_rodata() == needflush_before.view_rodata()
    &&& needflush_after.view_ghost() == needflush_before.view_ghost()
    &&& needflush_after.being_killed() == needflush_before.being_killed()
    &&& needflush_after.locking_thread() == needflush_before.locking_thread()
    &&& needflush_after.view() == (PcidNeedFlush { needflush: !(old_cpu.state is Running) && needflush_before.view().needflush, ..needflush_before.view() })
    &&& (forall|c: CpuId, p: Pcid| #![trigger pre.pcid_needflush.spec_index(c, p)] #![trigger post.pcid_needflush.spec_index(c, p)]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != KERNEL_DEFAULT_PCID) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == pre.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu()
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].inv()
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].view() == (pre.dflt_pt.view().cr3, KERNEL_DEFAULT_PCID)
    &&& (forall|c: CpuId| #![trigger pre.cpu_hw_cr3_pcid[c as int]] #![trigger post.cpu_hw_cr3_pcid[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_hw_cr3_pcid[c as int] == pre.cpu_hw_cr3_pcid[c as int])
    &&& (forall|c: CpuId, p: Pcid| #![trigger pre.cpu_tlb.spec_index((c, p))] #![trigger post.cpu_tlb.spec_index((c, p))]
        index_valid(NUM_CPUS, c) && pcid_valid(p) ==> if c == cpu_id && (p != KERNEL_DEFAULT_PCID || flush_default) {
            post.cpu_tlb.spec_index((c, p)).is_empty()
        } else { post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p)) })
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom()
    &&& (forall|ptr: RwLockCpuSetPtr| #![trigger pre.cpu_set_mp.spec_index(ptr)] #![trigger post.cpu_set_mp.spec_index(ptr)] pre.cpu_set_mp.dom().contains(ptr) ==> {
        &&& (ptr != cpu_set_ptr ==> post.cpu_set_mp.spec_index(ptr) == pre.cpu_set_mp.spec_index(ptr))
    })
    &&& cpu_set_after.is_init() == cpu_set_before.is_init()
    &&& cpu_set_after.view_rodata() == cpu_set_before.view_rodata()
    &&& cpu_set_after.view_ghost() == cpu_set_before.view_ghost()
    &&& cpu_set_after.being_killed() == cpu_set_before.being_killed()
    &&& cpu_set_after.locking_thread() == cpu_set_before.locking_thread()
    &&& cpu_set_after.view() == (CpuSet { owned_cpus: cpu_set_after.view().owned_cpus, ..cpu_set_before.view() })
    &&& cpu_set_after.view().owned_cpus.view() == cpu_set_before.view().owned_cpus.view()
    &&& cpu_set_after.view().owned_cpus.closed_view() == cpu_set_before.view().owned_cpus.closed_view().insert(cpu_id)
    &&& post.cpu_offline_mp.unchanged_except(&pre.cpu_offline_mp, flags_ptr)
    &&& table_after.owning_container == table_before.owning_container
    &&& table_after.container_depth == table_before.container_depth
    &&& table_after.flags.entries_unchanged_except(&table_before.flags, cpu_id)
    &&& !cell_after.view().requested
    &&& cell_after.view().index() == cell_before.view().index()
    &&& cell_after.is_init() == cell_before.is_init()
    &&& cell_after.view_rodata() == cell_before.view_rodata()
    &&& cell_after.view_ghost() == cell_before.view_ghost()
    &&& cell_after.being_killed() == cell_before.being_killed()
    &&& cell_after.locking_thread() == cell_before.locking_thread()
    &&& cpu_offline_requests_of(table_after) == cpu_offline_requests_of(table_before).update(cpu_id as int, false)
}

/// User-visible precondition of the hold step on `cpu_id`: the live, non-Off cpu is unlocked and its container's
/// request bit for the cpu is set.
#[verifier::opaque]
pub open spec fn cpu_offline_check_hold_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array.len() == NUM_CPUS
    &&& cpu.lock_state is Unlocked
    &&& !cpu.killed
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.container_map.spec_index(cpu.owning_container).cpu_offline_requests[cpu_id as int]
}

/// Holding write-locks cpu `cpu_id` across the boundary before the recheck, inside its kernel step, and changes nothing
/// else.
#[verifier::opaque]
pub open spec fn cpu_offline_check_hold_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    new_u == (KernelU { cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }), ..old_u })
}

/// Releasing happens with cpu `cpu_id` write-locked since the hold step.
#[verifier::opaque]
pub open spec fn cpu_offline_check_release_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array.len() == NUM_CPUS
    &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
}

/// Releasing unlocks cpu `cpu_id`, which leaves its kernel step for the resting state of its scheduling state, and changes
/// nothing else, when the recheck continues to the scheduler.
#[verifier::opaque]
pub open spec fn cpu_offline_check_release_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    new_u == (KernelU { cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }), ..old_u })
}

/// User-visible precondition of the offline step on `cpu_id`: the non-Off cpu is write-locked since the hold step, its
/// container's cpu-set lock is unlocked, the container's request bit for the cpu is set, and the running thread and
/// process, if any, are live and unlocked.
#[verifier::opaque]
pub open spec fn cpu_offline_check_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& container.cpu_set_lock is Unlocked
    &&& container.cpu_offline_requests[cpu_id as int]
    &&& cpu.current_process is Some == cpu.current_thread is Some
    &&& (cpu.current_thread is Some ==> {
        let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
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

/// User-visible offline step: `cpu_id` goes Off, its running thread is requeued at the tail, its
/// container's request bit is cleared, and its TLB entries are flushed.
pub open spec fn cpu_offline_check_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, entry_regs: Registers, flushed_default_pcid: bool) -> bool {
    kernel_u_cpu_went_off_changed(old_u, new_u, cpu_id, entry_regs, flushed_default_pcid)
}

/// The partial trace after holding from the entry state `pre`: the single hold step.
#[verifier::opaque]
pub open spec fn cpu_offline_check_trace_after_hold(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& cpu_offline_check_hold_step_pre(pre, cpu_id)
    &&& cpu_offline_check_hold_step(pre, trace[0].new_u, cpu_id)
}

/// Complete trace of one offline check from the entry state `pre`. A check whose entry cpu is killed, already Off, or
/// not requested continues without a step. Otherwise it records the hold step from `pre` and, from the decision state
/// after the boundary, where unheld objects may have changed, either the release step or the offline step to `post`.
#[verifier::opaque]
pub open spec fn cpu_offline_check_entry_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, went_off: bool, flushed_default_pcid: bool) -> bool {
    if cpu_offline_check_hold_step_pre(pre, cpu_id) {
        &&& trace.len() == 2
        &&& trace[0].old_u == pre
        &&& cpu_offline_check_hold_step(pre, trace[0].new_u, cpu_id)
        &&& trace[1].new_u == post
        &&& went_off ==> cpu_offline_check_step_pre(trace[1].old_u, cpu_id) && cpu_offline_check_step(trace[1].old_u, post, cpu_id, regs, flushed_default_pcid)
        &&& !went_off ==> cpu_offline_check_release_step_pre(trace[1].old_u, cpu_id) && cpu_offline_check_release_step(trace[1].old_u, post, cpu_id)
    } else {
        &&& !went_off
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

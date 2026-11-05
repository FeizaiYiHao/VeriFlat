use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_new_endpoint` from the state at entry, in the implementation's check order:
/// a cpu no longer Running or marked by a killer, a killed container, a container write-held by a live owner below the
/// running process's depth, a zombie container, a killed process or caller, an occupied descriptor, and a caller without 4K quota.
pub open spec fn new_endpoint_syscall_result(pre: KernelU, cpu_id: CpuId, ep_idx: EndpointIdx) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let container = pre.container_map[cpu.owning_container];
    let process = pre.process_map[cpu.current_process->Some_0];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if container.killed { RetValueType::ErrorContainerKilled }
    else if container.lock_process_owner is Some && container.lock_process_owner->Some_0 < LockOwnerId::Some(process.depth) { RetValueType::ErrorContainerLockOrderConflict }
    else if container.zombie { RetValueType::ErrorContainerZombie }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.endpoint_descriptors[ep_idx as int] is Some { RetValueType::ErrorIpcEndpointTargetInUse }
    else if thread.quota_4k == 0 { RetValueType::ErrorNoQuota }
    else { RetValueType::Success }
}

/// The cpu runs a live thread of a live process inside its live container; the thread has no syscall in
/// progress, an empty descriptor at `ep_idx`, and one 4K quota to fund the endpoint's page. The
/// cpu, the container, the process, and the thread are unlocked.
#[verifier::opaque]
pub open spec fn new_endpoint_enter_step_pre(old_u: KernelU, cpu_id: CpuId, ep_idx: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& edp_idx_valid(ep_idx)
    &&& cpu.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(ctn_ptr)
    &&& old_u.container_map.spec_index(ctn_ptr).lock_state is Unlocked
    &&& !old_u.container_map.spec_index(ctn_ptr).killed
    &&& !old_u.container_map.spec_index(ctn_ptr).zombie
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(prc_ptr).killed
    &&& thread.lock_state is Unlocked
    &&& thread.owning_container == ctn_ptr
    &&& thread.endpoint_descriptors[ep_idx as int] is None
    &&& thread.quota_4k >= 1
}

/// Entering write-locks the cpu, the container under the running process's depth, the process, and the thread, and
/// records `ep_idx` in the thread's progress.
#[verifier::opaque]
pub open spec fn new_endpoint_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, ep_idx: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    let locked = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
        container_map: old_u.container_map.insert(ctn_ptr, ContainerU {
            lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(old_u.process_map.spec_index(prc_ptr).depth)), ..old_u.container_map.spec_index(ctn_ptr)
        }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..old_u.process_map.spec_index(prc_ptr) }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..old_u.thread_map.spec_index(thrd_ptr) }),
        ..old_u
    };
    new_u == (KernelU { thread_map: locked.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::NewEndpoint { slot: ep_idx }), ..locked.thread_map[thrd_ptr] }), ..locked })
}

/// Finishing runs while the running thread records an endpoint creation at a valid index and holds the
/// cpu, its container, its process, and itself.
#[verifier::opaque]
pub open spec fn new_endpoint_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(ctn_ptr)
    &&& old_u.container_map.spec_index(ctn_ptr).lock_state is WriteLocked
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is NewEndpoint
    &&& edp_idx_valid(thread.syscall_progress->Some_0->NewEndpoint_slot)
}

/// One 4K quota of the running thread funds a new empty, unlocked receive endpoint of its container,
/// installed at the recorded descriptor. The caller's progress is cleared and its locks are released.
#[verifier::opaque]
pub open spec fn new_endpoint_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    let ep_idx = old_u.thread_map.spec_index(thrd_ptr).syscall_progress->Some_0->NewEndpoint_slot;
    kernel_u_new_endpoint_changed(KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        container_map: old_u.container_map.insert(ctn_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map.spec_index(ctn_ptr) }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map.spec_index(prc_ptr) }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thrd_ptr) }),
        ..old_u
    }, new_u, ctn_ptr, thrd_ptr, ep_idx, new_u.thread_map.spec_index(thrd_ptr).endpoint_descriptors[ep_idx as int]->Some_0)
}

/// The partial trace after entering: one enter step from `pre`.
#[verifier::opaque]
pub open spec fn new_endpoint_trace_after_enter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, ep_idx: EndpointIdx) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& new_endpoint_enter_step_pre(pre, cpu_id, ep_idx)
    &&& new_endpoint_enter_step(pre, trace[0].new_u, cpu_id, ep_idx)
}

/// Complete trace of the call: the enter and finish steps on success, a stutter otherwise.
#[verifier::opaque]
pub open spec fn new_endpoint_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, ep_idx: EndpointIdx, success: bool) -> bool {
    if success {
        &&& trace.len() == 2
        &&& trace[0].old_u == pre
        &&& new_endpoint_enter_step_pre(pre, cpu_id, ep_idx)
        &&& new_endpoint_enter_step(pre, trace[0].new_u, cpu_id, ep_idx)
        &&& trace[1].new_u == post
        &&& new_endpoint_finish_step_pre(trace[1].old_u, cpu_id)
        &&& new_endpoint_finish_step(trace[1].old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

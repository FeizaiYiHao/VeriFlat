use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
#[cfg(verus_keep_ghost)]
use crate::kernel::kernel_step_spec::kernel_u_new_thread_changed;

verus! {
/// The result of `syscall_new_thread` and `syscall_new_thread_with_endpoint` from the state at entry,
/// in the implementation's check order: a killed process or caller, a caller without 4K quota, and an
/// empty shared descriptor.
/// A cpu no longer Running or marked by a killer returns CpuIdle first.
pub open spec fn new_thread_syscall_result(pre: KernelU, cpu_id: CpuId, ep_idx: Option<EndpointIdx>) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if pre.process_map[cpu.current_process->Some_0].killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.quota_4k == 0 { RetValueType::ErrorNoQuota }
    else if ep_idx is Some && thread.endpoint_descriptors[ep_idx->Some_0 as int] is None { RetValueType::Error }
    else { RetValueType::Success }
}

/// The cpu runs a live thread of a live process inside its container; the thread has no syscall in
/// progress and one 4K quota to fund the new thread's page, and a present `ep_idx` names a
/// live descriptor. The cpu, the process, the thread, and that endpoint are unlocked.
#[verifier::opaque]
pub open spec fn new_thread_enter_step_pre(old_u: KernelU, cpu_id: CpuId, ep_idx: Option<EndpointIdx>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let ep_ptr = thread.endpoint_descriptors[ep_idx->Some_0 as int]->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(prc_ptr).killed
    &&& thread.lock_state is Unlocked
    &&& thread.owning_container == cpu.owning_container
    &&& thread.quota_4k >= 1
    &&& (ep_idx is Some ==> {
        &&& edp_idx_valid(ep_idx->Some_0)
        &&& thread.endpoint_descriptors[ep_idx->Some_0 as int] is Some
        &&& old_u.endpoint_map.dom().contains(ep_ptr)
        &&& old_u.endpoint_map.spec_index(ep_ptr).lock_state is Unlocked
    })
}

/// Entering write-locks the cpu, the process, the thread, and the endpoint at `ep_idx`, and
/// records `regs` and `ep_idx` in the thread's progress.
#[verifier::opaque]
pub open spec fn new_thread_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, ep_idx: Option<EndpointIdx>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let locked = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..old_u.process_map.spec_index(prc_ptr) }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..thread }),
        endpoint_map: match ep_idx {
            Some(i) => old_u.endpoint_map.insert(thread.endpoint_descriptors[i as int]->Some_0, EndpointU { lock_state: LockStateU::WriteLocked, ..old_u.endpoint_map.spec_index(thread.endpoint_descriptors[i as int]->Some_0) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    new_u == (KernelU { thread_map: locked.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::NewThread { regs, endpoint_index: ep_idx }), ..locked.thread_map[thrd_ptr] }), ..locked })
}

/// Finishing runs while the running thread records a thread creation with a valid endpoint index and
/// holds the cpu, its process, itself, and the recorded endpoint.
#[verifier::opaque]
pub open spec fn new_thread_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let ep_idx = thread.syscall_progress->Some_0->NewThread_endpoint_index;
    let ep_ptr = thread.endpoint_descriptors[ep_idx->Some_0 as int]->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is NewThread
    &&& (ep_idx is Some ==> {
        &&& edp_idx_valid(ep_idx->Some_0)
        &&& old_u.endpoint_map.dom().contains(ep_ptr)
        &&& old_u.endpoint_map.spec_index(ep_ptr).lock_state is WriteLocked
    })
}

/// One 4K quota of the running thread funds a new scheduled thread of its process with the recorded
/// registers and endpoint; the new thread joins the container's thread set and scheduler, the
/// process's thread list, and the endpoint's owner set. The caller's progress is cleared and its
/// locks are released.
#[verifier::opaque]
pub open spec fn new_thread_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let endpoint = match progress->NewThread_endpoint_index { Some(i) => thread.endpoint_descriptors[i as int], None => None };
    kernel_u_new_thread_changed(KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map.spec_index(prc_ptr) }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..thread }),
        endpoint_map: match endpoint {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    }, new_u, prc_ptr, thrd_ptr, cpu.owning_container, cpu_id, new_u.process_map.spec_index(prc_ptr).owned_threads.last(), progress->NewThread_regs, endpoint, None)
}

/// The partial trace after entering: one enter step from `pre`.
#[verifier::opaque]
pub open spec fn new_thread_trace_after_enter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, regs: Registers, ep_idx: Option<EndpointIdx>) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& new_thread_enter_step_pre(pre, cpu_id, ep_idx)
    &&& new_thread_enter_step(pre, trace[0].new_u, cpu_id, regs, ep_idx)
}

/// Complete trace of the call: the enter and finish steps on success, a stutter otherwise.
#[verifier::opaque]
pub open spec fn new_thread_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, ep_idx: Option<EndpointIdx>, success: bool) -> bool {
    if success {
        &&& trace.len() == 2
        &&& trace[0].old_u == pre
        &&& new_thread_enter_step_pre(pre, cpu_id, ep_idx)
        &&& new_thread_enter_step(pre, trace[0].new_u, cpu_id, regs, ep_idx)
        &&& trace[1].new_u == post
        &&& new_thread_finish_step_pre(trace[1].old_u, cpu_id)
        &&& new_thread_finish_step(trace[1].old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

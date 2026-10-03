use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
/// The result of `syscall_new_thread` and `syscall_new_thread_with_endpoint` from the state at entry,
/// in the implementation's check order: a killed process or caller, a caller without 4K quota, and an
/// empty shared descriptor.
pub open spec fn new_thread_syscall_result(pre: KernelU, cpu_id: CpuId, endpoint_index: Option<EndpointIdx>) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    if pre.process_map[cpu.current_process->Some_0].killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.quota_4k == 0 { RetValueType::ErrorNoQuota }
    else if endpoint_index is Some && thread.endpoint_descriptors[endpoint_index->Some_0 as int] is None { RetValueType::Error }
    else { RetValueType::Success }
}

/// The cpu runs a live thread of a live process inside its container; the thread has no syscall in
/// progress and one 4K quota to fund the new thread's page, and a present `endpoint_index` names a
/// live descriptor. The cpu, the process, the thread, and that endpoint are unlocked.
#[verifier::opaque]
pub open spec fn new_thread_enter_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: Option<EndpointIdx>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index->Some_0 as int]->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(process_ptr).killed
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.owning_proc == process_ptr
    &&& thread.owning_container == cpu.owning_container
    &&& thread.quota_4k >= 1
    &&& (endpoint_index is Some ==> {
        &&& edp_idx_valid(endpoint_index->Some_0)
        &&& thread.endpoint_descriptors[endpoint_index->Some_0 as int] is Some
        &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
        &&& old_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
    })
}

/// Entering write-locks the cpu, the process, the thread, and the endpoint at `endpoint_index`, and
/// records `regs` and `endpoint_index` in the thread's progress.
#[verifier::opaque]
pub open spec fn new_thread_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let locked = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..cpu }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..old_u.process_map.spec_index(process_ptr) }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..thread }),
        endpoint_map: match endpoint_index {
            Some(i) => old_u.endpoint_map.insert(thread.endpoint_descriptors[i as int]->Some_0, EndpointU {
                lock_state: LockStateU::WriteLocked, ..old_u.endpoint_map.spec_index(thread.endpoint_descriptors[i as int]->Some_0)
            }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    new_u == (KernelU {
        thread_map: locked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::NewThread { regs, endpoint_index }), ..locked.thread_map[thread_ptr] }),
        ..locked
    })
}

/// Finishing runs while the running thread records a thread creation with a valid endpoint index and
/// holds the cpu, its process, itself, and the recorded endpoint.
#[verifier::opaque]
pub open spec fn new_thread_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let endpoint_index = thread.syscall_progress->Some_0->NewThread_endpoint_index;
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index->Some_0 as int]->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.process_map.spec_index(process_ptr).lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is NewThread
    &&& (endpoint_index is Some ==> {
        &&& edp_idx_valid(endpoint_index->Some_0)
        &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
        &&& old_u.endpoint_map.spec_index(endpoint_ptr).lock_state is WriteLocked
    })
}

/// One 4K quota of the running thread funds a new scheduled thread of its process with the recorded
/// registers and endpoint; the new thread joins the container's thread set and scheduler, the
/// process's thread list, and the endpoint's owner set. The caller's progress is cleared and its
/// locks are released.
#[verifier::opaque]
pub open spec fn new_thread_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let progress = thread.syscall_progress->Some_0;
    let endpoint = match progress->NewThread_endpoint_index { Some(i) => thread.endpoint_descriptors[i as int], None => None };
    kernel_u_new_thread_changed(KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..cpu }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map.spec_index(process_ptr) }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..thread }),
        endpoint_map: match endpoint {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    }, new_u, process_ptr, thread_ptr, cpu.owning_container, new_u.process_map.spec_index(process_ptr).owned_threads.last(), progress->NewThread_regs, endpoint, None)
}

/// The partial trace after entering: one enter step from `pre`.
#[verifier::opaque]
pub open spec fn new_thread_trace_after_enter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& new_thread_enter_step_pre(pre, cpu_id, endpoint_index)
    &&& new_thread_enter_step(pre, trace[0].new_u, cpu_id, regs, endpoint_index)
}

/// Complete trace of the call: the enter and finish steps on success, a stutter otherwise.
#[verifier::opaque]
pub open spec fn new_thread_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>, success: bool,
) -> bool {
    if success {
        &&& trace.len() == 2
        &&& trace[0].old_u == pre
        &&& new_thread_enter_step_pre(pre, cpu_id, endpoint_index)
        &&& new_thread_enter_step(pre, trace[0].new_u, cpu_id, regs, endpoint_index)
        &&& trace[1].new_u == post
        &&& new_thread_finish_step_pre(trace[1].old_u, cpu_id)
        &&& new_thread_finish_step(trace[1].old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

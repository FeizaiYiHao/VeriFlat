use vstd::prelude::*;
use crate::*;

verus! {
/// The running thread and process are alive, the thread runs on `cpu_id` inside the cpu's
/// container and process, and it has one 4K quota to fund the new thread's page.
pub open spec fn new_thread_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !old_u.process_map.spec_index(process_ptr).killed
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.owning_proc == process_ptr
    &&& thread.owning_container == cpu.owning_container
    &&& thread.quota_4k >= 1
}

/// The running thread additionally holds a live endpoint descriptor at `endpoint_index`.
pub open spec fn new_thread_with_endpoint_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    &&& new_thread_step_pre(old_u, cpu_id)
    &&& edp_idx_valid(endpoint_index)
    &&& thread.endpoint_descriptors[endpoint_index as int] is Some
    &&& old_u.endpoint_map.dom().contains(thread.endpoint_descriptors[endpoint_index as int]->Some_0)
}

/// One 4K quota of the running thread funds the new scheduled thread `new_thread_ptr` of the
/// running process, which joins the container's thread set and scheduler, the process's thread
/// list, and the owner set of the optional initial endpoint.
pub open spec fn new_thread_step(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, initial_endpoint: Option<RwLockEndpointPtr>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let process = old_u.process_map.spec_index(process_ptr);
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let new_thread = ThreadU {
        lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED, caller: None, callee: None,
        owning_container: cpu.owning_container, owning_proc: process_ptr, quota_4k: 0, quota_2m: 0, quota_1g: 0,
        endpoint_descriptors: Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { initial_endpoint } else { None }),
        blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: None, trap_frame: Some(initial_regs),
        syscall_progress: None, killed: false,
    };
    &&& !old_u.thread_map.dom().contains(new_thread_ptr)
    &&& new_u == (KernelU {
        endpoint_map: match initial_endpoint {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU {
                owning_threads: old_u.endpoint_map.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)), ..old_u.endpoint_map.spec_index(e)
            }),
            None => old_u.endpoint_map,
        },
        container_map: old_u.container_map.insert(cpu.owning_container, ContainerU {
            owned_threads: container.owned_threads.insert(new_thread_ptr), scheduler: container.scheduler.push(new_thread_ptr), ..container
        }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, ..thread }).insert(new_thread_ptr, new_thread),
        ..old_u
    })
}
} // verus!

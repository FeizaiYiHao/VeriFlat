use vstd::prelude::*;
use crate::*;

verus! {
/// The running process and its container exist, are alive, and can move `alloc_amount` 4K quota
/// from the container to the process without overflow.
pub open spec fn alloc_quota_4k_step_pre(old_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let container_ptr = cpu.owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& !old_u.container_map.spec_index(container_ptr).killed
    &&& old_u.container_map.spec_index(container_ptr).quota_4k >= alloc_amount
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !old_u.process_map.spec_index(process_ptr).killed
    &&& old_u.process_map.spec_index(process_ptr).quota_4k + alloc_amount <= usize::MAX
    &&& alloc_amount > 0
}

/// The container's 4K quota decreases by `alloc_amount` and the running process's increases by it.
pub open spec fn alloc_quota_4k_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let process = old_u.process_map.spec_index(cpu.current_process->Some_0);
    new_u == (KernelU {
        container_map: old_u.container_map.insert(cpu.owning_container, ContainerU { quota_4k: (container.quota_4k - alloc_amount) as usize, ..container }),
        process_map: old_u.process_map.insert(cpu.current_process->Some_0, ProcessU { quota_4k: (process.quota_4k + alloc_amount) as usize, ..process }),
        ..old_u
    })
}
} // verus!

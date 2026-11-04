use vstd::prelude::*;
use crate::*;

verus! {
/// Every cpu a container owns names it as owner, carries its depth, is in the closed part of its cpu set iff it is Off,
/// and runs only that container's processes and threads; every cpu's owner lists it in its cpu set.
// Proof dependencies (confirmed for container creation): container_cpu_set_wf.
#[verifier::opaque]
pub open spec fn container_cpu_wf(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, cpu_arr: CpuLockedArray) -> bool {
    // Container -> owned cpus.
    &&& forall|c: RwLockContainerPtr, cpu_id: CpuId|
        #![trigger cpu_set_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().cpu_set).view().owned_cpus.view().contains(cpu_id)]
        #![trigger cpu_set_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().cpu_set).view().owned_cpus.closed_view().contains(cpu_id)]
        #![trigger ctn_mp.spec_index(c), cpu_arr.spec_index(cpu_id)]
        ctn_mp.dom().contains(c)
            && cpu_set_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().cpu_set).view().owned_cpus.view().contains(cpu_id)
            ==> {
                let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
                let owned_cpus = cpu_set_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().cpu_set).view().owned_cpus;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.owning_container == c
                // an owned cpu is in the closed part of the set iff it is Off
                &&& owned_cpus.closed_view().contains(cpu_id) == (cpu.state is Off)
                &&& cpu.current_process is Some ==> ctn_mp.spec_index(c).view_ghost().owned_processes.contains(cpu.current_process.unwrap())
                &&& cpu.current_thread is Some ==> ctn_mp.spec_index(c).view_ghost().owned_threads.contains(cpu.current_thread.unwrap())
            }
    // Cpu -> owning container.
    &&& forall|cpu_id: CpuId|
        #![trigger cpu_arr.spec_index(cpu_id).view().view().view().owning_container]
        index_valid(NUM_CPUS, cpu_id) ==> {
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            &&& ctn_mp.dom().contains(cpu.owning_container)
            &&& cpu_set_mp.spec_index(ctn_mp.spec_index(cpu.owning_container).view_rodata().view().cpu_set).view().owned_cpus.view().contains(cpu_id)
            &&& ctn_mp.spec_index(cpu.owning_container).view_rodata().view().depth == cpu.container_depth
        }
}

pub proof fn container_cpu_wf_cpu_at(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, cpu_arr: CpuLockedArray, cpu_id: CpuId)
    requires
        container_cpu_wf(ctn_mp, cpu_set_mp, cpu_arr),
    ensures
        index_valid(NUM_CPUS, cpu_id) ==> ({
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let ctn_ptr = cpu.owning_container;
            let owned_cpus = cpu_set_mp.spec_index(ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view().owned_cpus;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& owned_cpus.view().contains(cpu_id)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth == cpu.container_depth
            &&& owned_cpus.closed_view().contains(cpu_id) == (cpu.state is Off)
            &&& cpu.current_process is Some ==> ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.contains(cpu.current_process.unwrap())
            &&& cpu.current_thread is Some ==> ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.contains(cpu.current_thread.unwrap())
        }),
{ reveal(container_cpu_wf); }

pub proof fn container_cpu_wf_container_at(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, cpu_arr: CpuLockedArray, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId)
    requires
        container_cpu_wf(ctn_mp, cpu_set_mp, cpu_arr),
    ensures
        ctn_mp.dom().contains(ctn_ptr) && cpu_set_mp.spec_index(ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view().owned_cpus.view().contains(cpu_id) ==> ({
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let owned_cpus = cpu_set_mp.spec_index(ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view().owned_cpus;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.owning_container == ctn_ptr
            &&& owned_cpus.closed_view().contains(cpu_id) == (cpu.state is Off)
            &&& cpu.current_process is Some ==> ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.contains(cpu.current_process.unwrap())
            &&& cpu.current_thread is Some ==> ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.contains(cpu.current_thread.unwrap())
        }),
{ reveal(container_cpu_wf); }
}

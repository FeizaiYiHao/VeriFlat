use vstd::prelude::*;
use crate::*;

verus! {

    /// Container owned Cpu only runs processes and threads of the container
    /// Container cpu bidirectionally points to each other
    #[verifier::opaque]
    pub open spec fn container_cpu_wf(container_perms: ContainerLockedMap, cpu_array:CpuLockedArray) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr, cpu_i: CpuId|
            #![trigger container_perms.spec_index(c_ptr).view().owned_cpus.view().contains(cpu_i)]
            container_perms.dom().contains(c_ptr)
            &&
            container_perms.spec_index(c_ptr).view().owned_cpus.view().contains(cpu_i)
            ==>
            {
                index_valid(NUM_CPUS, cpu_i)
                &&
                cpu_array.spec_index(cpu_i).view().view().owning_container == c_ptr
                &&
                cpu_array.spec_index(cpu_i).view().view().current_process is Some ==>
                container_perms.spec_index(c_ptr).view().owned_processes.contains(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap())
                &&
                cpu_array.spec_index(cpu_i).view().view().current_thread is Some ==>
                container_perms.spec_index(c_ptr).view_ghost().owned_threads.contains(cpu_array.spec_index(cpu_i).view().view().current_thread.unwrap())
            }
        &&&
        forall|cpu_i:CpuId|
            #![trigger cpu_array.spec_index(cpu_i).view().view().owning_container]
            index_valid(NUM_CPUS, cpu_i)
            ==>
            {
                &&&
                container_perms.dom().contains(cpu_array.spec_index(cpu_i).view().view().owning_container)
                &&&
                container_perms.spec_index((cpu_array.spec_index(cpu_i).view().view().owning_container)).view().owned_cpus.view().contains(cpu_i)
                &&&
                container_perms.spec_index((cpu_array.spec_index(cpu_i).view().view().owning_container)).view_rodata().view().depth
                    ==
                    cpu_array.spec_index(cpu_i).view().view().container_depth
            }
    }
}

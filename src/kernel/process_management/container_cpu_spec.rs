use vstd::prelude::*;
use crate::*;

verus! {

    pub proof fn container_cpu_wf_proof()
        ensures
            forall|container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), CONTAINER_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, (), (), NUM_CPUS, CPU_HAS_KILL_STATE>|
                container_cpu_wf(container_perms, cpu_array) <==> container_cpu_wf_inner(container_perms, cpu_array)
    {}

    pub closed spec fn container_cpu_wf(container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), CONTAINER_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, (), (), NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        container_cpu_wf_inner(container_perms, cpu_array)
    }

    /// Container owned Cpu only runs processes and threads of the container
    /// Container cpu bidirectly points to each other
    pub open spec fn container_cpu_wf_inner(container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), CONTAINER_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, (), (), NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr, cpu_i: CpuId|
            #![trigger container_perms.spec_index(c_ptr).view().owned_cpus.view().contains(cpu_i)]
            container_perms.dom().contains(c_ptr)
            &&
            container_perms.spec_index(c_ptr).view().owned_cpus.view().contains(cpu_i)
            ==>
            {
                cpu_array.spec_index(cpu_i).view().view().owning_container == c_ptr
                &&
                cpu_array.spec_index(cpu_i).view().view().current_process is Some ==>
                container_perms.spec_index(c_ptr).view().owned_processes.contains(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap())
                &&
                cpu_array.spec_index(cpu_i).view().view().current_thread is Some ==>
                container_perms.spec_index(c_ptr).view().owned_threads.contains(cpu_array.spec_index(cpu_i).view().view().current_thread.unwrap())
            }
        &&&
        forall|cpu_i:CpuId|
            #![trigger cpu_array.spec_index(cpu_i).view().view().owning_container]
            cpu_id_valid(cpu_i)
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
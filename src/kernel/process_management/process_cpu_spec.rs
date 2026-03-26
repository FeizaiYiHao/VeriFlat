use vstd::prelude::*;
use crate::*;

verus! {
   pub proof fn process_cpu_wf_proof()
        ensures
            forall|process_perms: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>|
                process_cpu_wf(process_perms, cpu_array) <==> process_cpu_wf_inner(process_perms, cpu_array)
    {}

    pub closed spec fn process_cpu_wf(process_perms: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        process_cpu_wf_inner(process_perms, cpu_array)
    }
    pub open spec fn process_cpu_wf_inner(process_perms: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        &&&
        forall|cpu_i:CpuId|
            #![trigger cpu_array.spec_index(cpu_i).view().view().current_process]
            cpu_id_valid(cpu_i) 
            ==>
            {
                &&&
                cpu_array.spec_index(cpu_i).view().wlocked() == false && cpu_array.spec_index(cpu_i).view().view().current_process is Some
                ==> 
                process_perms.dom().contains(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap())
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_process is Some && process_perms.dom().contains(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap())
                ==>
                write_locked_by_same_thread(cpu_array.spec_index(cpu_i).view(), process_perms.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()))
                ||
                {
                    &&&
                    cpu_array.spec_index(cpu_i).view().view().current_pagetable ==  process_perms.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()).view().pagetable
                    &&&
                    cpu_array.spec_index(cpu_i).view().view().current_pcid ==  process_perms.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()).view().pcid
                }
            }
    }

}
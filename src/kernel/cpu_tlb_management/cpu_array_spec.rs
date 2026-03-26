use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn cpu_array_wf(cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        &&&
        cpu_array.inv()
        &&&
        forall|cpu_i:CpuId|
            #![auto]
            cpu_id_valid(cpu_i)
            ==>{
                |||
                cpu_array[cpu_i]@.wlocked()
                |||
                cpu_array[cpu_i]@.inv()
            }
    }
}
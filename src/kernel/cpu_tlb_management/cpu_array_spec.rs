use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn cpu_array_wf(cpu_array: LockedArray<Cpu, (), NUM_CPUS, CPU_HAS_KILL_STATE>, kernel_pagetable: PageTable<PT_TYPE>) -> bool {
        &&&
        cpu_array.inv()
        &&&
        forall|cpu_i:CpuId|
            #![auto]
            cpu_id_valid(cpu_i)
            ==>{
                &&&
                cpu_array[cpu_i]@.inv()
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_process is None ==> cpu_array.spec_index(cpu_i).view().view().current_cr3 == kernel_pagetable.cr3
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_process is None ==> cpu_array.spec_index(cpu_i).view().view().current_pcid == KERNEL_DEFAULT_PCID
            }
    }
}
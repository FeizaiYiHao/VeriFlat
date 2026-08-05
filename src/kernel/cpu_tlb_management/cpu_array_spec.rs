use vstd::prelude::*;
use crate::*;
verus! {
    #[verifier::opaque]
    pub open spec fn cpu_array_wf(cpu_array: CpuLockedArray, kernel_pagetable: PageTable<PT_TYPE>) -> bool {
        &&&
        cpu_array.inv()
        &&&
        forall|cpu_i:CpuId|
            #![auto]
            cpu_id_valid(cpu_i)
            ==>{
                &&&
                cpu_array.spec_index(cpu_i).view().inv()
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_process is None ==> cpu_array.spec_index(cpu_i).view().view().current_cr3 == kernel_pagetable.cr3
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_process is None ==> cpu_array.spec_index(cpu_i).view().view().current_pcid == KERNEL_DEFAULT_PCID
            }
    }
}
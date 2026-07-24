use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_cpu_wf(process_map: ProcessLockedMap, cpu_array:CpuLockedArray) -> bool {
        &&&
        forall|cpu_i:CpuId|
            #![trigger cpu_array.spec_index(cpu_i).view().view().current_process]
            #![trigger cpu_array.spec_index(cpu_i).view().view().current_pagetable]
            cpu_id_valid(cpu_i) 
            &&
            cpu_array.spec_index(cpu_i).view().view().current_process is Some
            ==> 
            {
                &&&
                process_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap())
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_pagetable ==  process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()).view().pagetable
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_pcid ==  process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()).view().pcid
                &&&
                cpu_array.spec_index(cpu_i).view().view().process_depth ==  process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()).view_rodata().view().depth
                &&&
                cpu_array.spec_index(cpu_i).view().view().owning_container == process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()).view_rodata().view().owning_container
                &&&
                cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[cpu_array.spec_index(cpu_i).view().view().current_pcid].unwrap().process_ptr == cpu_array.spec_index(cpu_i).view().view().current_process.unwrap()
                &&&
                cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[cpu_array.spec_index(cpu_i).view().view().current_pcid].unwrap().pagetable_ptr == cpu_array.spec_index(cpu_i).view().view().current_pagetable
                
            }

    }

}

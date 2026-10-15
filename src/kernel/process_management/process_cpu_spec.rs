use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_cpu_wf(process_map: ProcessLockedMap, cpu_array:CpuLockedArray) -> bool {
        &&& forall|cpu_i:CpuId|
            #![trigger cpu_array.spec_index(cpu_i).view().view().view().current_process]
            #![trigger cpu_array.spec_index(cpu_i).view().view().view().current_pagetable]
            index_valid(NUM_CPUS, cpu_i) && cpu_array.spec_index(cpu_i).view().view().view().current_process is Some ==> {
                &&& process_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap())
                &&& !process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()).view().zombie
                &&& cpu_array.spec_index(cpu_i).view().view().view().current_pagetable == Some(process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()).view().pagetable)
                &&& cpu_array.spec_index(cpu_i).view().view().view().current_pcid == process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()).view().pcid
                &&& cpu_array.spec_index(cpu_i).view().view().view().current_cr3 == process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()).view_rodata().view().cr3
                &&& cpu_array.spec_index(cpu_i).view().view().view().process_depth == process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()).view_rodata().view().depth
                &&& cpu_array.spec_index(cpu_i).view().view().view().owning_container == process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()).view_rodata().view().owning_container
                &&& cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_pcid) is Some
                &&& cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_pcid).unwrap().process_ptr == cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap()
                &&& Some(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_pcid).unwrap().pagetable_ptr) == cpu_array.spec_index(cpu_i).view().view().view().current_pagetable
            }
    }

    pub proof fn process_cpu_wf_at(process_map: ProcessLockedMap, cpu_array: CpuLockedArray, cpu_i: CpuId)
        requires
            process_cpu_wf(process_map, cpu_array),
        ensures
            index_valid(NUM_CPUS, cpu_i) && cpu_array.spec_index(cpu_i).view().view().view().current_process is Some ==> ({
                let p_ptr = cpu_array.spec_index(cpu_i).view().view().view().current_process.unwrap();
                &&& process_map.dom().contains(p_ptr)
                &&& !process_map.spec_index(p_ptr).view().zombie
                &&& cpu_array.spec_index(cpu_i).view().view().view().current_pagetable == Some(process_map.spec_index(p_ptr).view().pagetable)
                &&& cpu_array.spec_index(cpu_i).view().view().view().current_pcid == process_map.spec_index(p_ptr).view().pcid
                &&& cpu_array.spec_index(cpu_i).view().view().view().current_cr3 == process_map.spec_index(p_ptr).view_rodata().view().cr3
                &&& cpu_array.spec_index(cpu_i).view().view().view().process_depth == process_map.spec_index(p_ptr).view_rodata().view().depth
                &&& cpu_array.spec_index(cpu_i).view().view().view().owning_container == process_map.spec_index(p_ptr).view_rodata().view().owning_container
                &&& cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_pcid) is Some
                &&& cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_pcid).unwrap().process_ptr == p_ptr
                &&& Some(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(cpu_array.spec_index(cpu_i).view().view().view().current_pcid).unwrap().pagetable_ptr) == cpu_array.spec_index(cpu_i).view().view().view().current_pagetable
            }),
    { reveal(process_cpu_wf); }
}

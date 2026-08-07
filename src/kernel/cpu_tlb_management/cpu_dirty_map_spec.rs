use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn cpu_dirty_map_wf(container_map: ContainerLockedMap, process_map: ProcessLockedMap, 
        cpu_array:CpuLockedArray, tlb: CpuTLB, pagetable_map: PageTableLockedMap) -> bool
    {
        &&&
        cpu_dirty_map_contains_container_processes(container_map, cpu_array)
        &&&
        cpu_dirty_map_proc_pcid_match(process_map, cpu_array)
        &&&
        cpu_not_in_dirty_map_imply_not_in_tlb(cpu_array, tlb)
        &&&
        cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map, cpu_array)
    }

    #[verifier::opaque]
    pub open spec fn cpu_dirty_map_contains_container_processes(container_map: ContainerLockedMap, cpu_array:CpuLockedArray) -> bool 
        recommends
            container_cpu_wf(container_map, cpu_array),
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid)]
            #![trigger cpu_id_valid(cpu_i), pcid_valid(pcid)]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            ==>
            container_map.spec_index(cpu_array.spec_index(cpu_i).view().view().owning_container).view().owned_processes.contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr)
    }

    #[verifier::opaque]
    pub open spec fn cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map: PageTableLockedMap, cpu_array:CpuLockedArray) -> bool 
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
        #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid)]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            ==>
            pagetable_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr)
            &&
            pagetable_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr).view().pcid_value() == pcid
    }

    #[verifier::opaque]
    pub open spec fn cpu_not_in_dirty_map_imply_not_in_tlb(cpu_array: CpuLockedArray, tlb: CpuTLB) -> bool {
        &&&
        forall|cpu_id:CpuId, pcid: Pcid|
            #![auto]
            cpu_id_valid(cpu_id) && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && tlb.spec_index((cpu_id, pcid)).is_empty() == false
            ==>
            cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
    }

    #[verifier::opaque]
    pub open spec fn cpu_dirty_map_proc_pcid_match(process_map: ProcessLockedMap, cpu_array: CpuLockedArray) -> bool 
        recommends
            process_cpu_wf(process_map, cpu_array)
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid)]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            ==>
            {
                &&&  
                process_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr)
                &&&
                process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr).view().pcid == pcid
                &&&
                process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr).view().pagetable
                    == cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr
            }
    }
}

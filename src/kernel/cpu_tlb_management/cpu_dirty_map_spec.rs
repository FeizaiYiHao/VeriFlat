use vstd::prelude::*;
use crate::*;
verus! {
    // Proof dependency: closure across container ownership updates needs
    // `container_cpu_wf` to relate each CPU to its owning container.
    pub open spec fn cpu_dirty_map_wf(container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, process_map: ProcessLockedMap,
        cpu_array:CpuLockedArray, tlb: CpuTLB, pagetable_map: PageTableLockedMap, needflush: PcidNeedFlushArray) -> bool
    {
        &&&
        cpu_dirty_map_contains_container_processes(container_map, cpu_set_map, cpu_array, needflush, tlb)
        &&&
        cpu_dirty_map_proc_pcid_match(process_map, cpu_array, needflush, tlb)
        &&&
        cpu_not_in_dirty_map_imply_not_in_tlb(cpu_array, tlb)
        &&&
        cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map, cpu_array, needflush, tlb)
    }

    #[verifier::opaque]
    pub open spec fn cpu_dirty_map_contains_container_processes(container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, cpu_array:CpuLockedArray, needflush: PcidNeedFlushArray, tlb: CpuTLB) -> bool
        recommends
            container_cpu_wf(container_map, cpu_set_map, cpu_array),
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid)]
            #![trigger index_valid(NUM_CPUS, cpu_i), pcid_valid(pcid)]
            index_valid(NUM_CPUS, cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && ((!needflush.spec_index(cpu_i, pcid).view().needflush && !tlb.spec_index((cpu_i, pcid)).is_empty()) || cpu_array.spec_index(cpu_i).view().view().view().current_pcid == pcid)
            ==>
            container_map.spec_index(cpu_array.spec_index(cpu_i).view().view().view().owning_container).view().owned_processes.contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr)
    }

    #[verifier::opaque]
    pub open spec fn cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map: PageTableLockedMap, cpu_array:CpuLockedArray, needflush: PcidNeedFlushArray, tlb: CpuTLB) -> bool
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
        #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid)]
            index_valid(NUM_CPUS, cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && ((!needflush.spec_index(cpu_i, pcid).view().needflush && !tlb.spec_index((cpu_i, pcid)).is_empty()) || cpu_array.spec_index(cpu_i).view().view().view().current_pcid == pcid)
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
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && tlb.spec_index((cpu_id, pcid)).is_empty() == false
            ==>
            cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
    }

    #[verifier::opaque]
    pub open spec fn cpu_dirty_map_proc_pcid_match(process_map: ProcessLockedMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, tlb: CpuTLB) -> bool
        recommends
            process_cpu_wf(process_map, cpu_array)
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid)]
            index_valid(NUM_CPUS, cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && ((!needflush.spec_index(cpu_i, pcid).view().needflush && !tlb.spec_index((cpu_i, pcid)).is_empty()) || cpu_array.spec_index(cpu_i).view().view().view().current_pcid == pcid)
            ==>
            {
                &&&  
                process_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr)
                &&& !process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr).view().zombie
                &&&
                process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr).view().pcid == pcid
                &&&
                process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().process_ptr).view().pagetable
                    == cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr
            }
    }
}

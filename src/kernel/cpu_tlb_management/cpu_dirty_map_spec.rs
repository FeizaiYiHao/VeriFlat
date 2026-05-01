use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn cpu_dirty_map_wf(container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>, process_map: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, 
        cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB, pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>) -> bool
    {
        &&&
        cpu_dirty_map_contains_container_processes(container_perms, cpu_array)
        &&&
        cpu_dirty_map_proc_pcid_match(process_map, cpu_array)
        &&&
        cpu_not_in_dirty_map_imply_not_in_tlb(cpu_array, tlb)
        &&&
        cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map, cpu_array)
    }

    pub proof fn cpu_dirty_map_contains_container_processes_proof()
        ensures
            forall|container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>|
                cpu_dirty_map_contains_container_processes(container_perms, cpu_array) <==> cpu_dirty_map_contains_container_processes_inner(container_perms, cpu_array)
    {} 
    pub closed spec fn cpu_dirty_map_contains_container_processes(container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool
    {
        cpu_dirty_map_contains_container_processes_inner(container_perms, cpu_array)
    }

    pub open spec fn cpu_dirty_map_contains_container_processes_inner(container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool 
        recommends
            container_cpu_wf_inner(container_perms, cpu_array),
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid]]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid] is Some
            ==>
            container_perms.spec_index(cpu_array.spec_index(cpu_i).view().view().owning_container).view().owned_processes.contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().process_ptr)
    }

    pub proof fn cpu_dirty_map_contains_pagetable_pcid_match_proof()
        ensures 
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>|
                cpu_dirty_map_contains_pagetable_pcid_match_inner(pagetable_map, cpu_array) <==> cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map, cpu_array)     
    {}
    pub closed spec fn cpu_dirty_map_contains_pagetable_pcid_match(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool 
    {   
        cpu_dirty_map_contains_pagetable_pcid_match_inner(pagetable_map, cpu_array)
    }
    pub open spec fn cpu_dirty_map_contains_pagetable_pcid_match_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, cpu_array:LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool 
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
        #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid]]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid] is Some
            ==>
            pagetable_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().pagetable_ptr)
            &&
            pagetable_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().pagetable_ptr).view().pcid_or_ioid() == pcid
    }
    pub proof fn cpu_not_in_dirty_map_imply_not_in_tlb_proof()
        ensures
            forall| cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB |
                cpu_not_in_dirty_map_imply_not_in_tlb(cpu_array, tlb) == cpu_not_in_dirty_map_imply_not_in_tlb_inner(cpu_array, tlb)
    {}

    pub closed spec fn cpu_not_in_dirty_map_imply_not_in_tlb(cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB) -> bool {
        cpu_not_in_dirty_map_imply_not_in_tlb_inner(cpu_array, tlb)
    }

    pub open spec fn cpu_not_in_dirty_map_imply_not_in_tlb_inner(cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB) -> bool {
        &&&
        forall|cpu_id:CpuId, pcid: Pcid|
            #![auto]
            cpu_id_valid(cpu_id) && pcid_valid(pcid)
            ==>{
                &&&
                (cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()[pcid] is Some) == (tlb.spec_index((cpu_id, pcid)).is_empty() == false)
            }
    }

    pub proof fn cpu_dirty_map_proc_pcid_match_proof()
        ensures
            forall|process_map: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>|
                cpu_dirty_map_proc_pcid_match_inner(process_map, cpu_array) == cpu_dirty_map_proc_pcid_match(process_map, cpu_array)
    {}
    pub closed spec fn cpu_dirty_map_proc_pcid_match(process_map: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        cpu_dirty_map_proc_pcid_match_inner(process_map, cpu_array)
    }

    pub open spec fn cpu_dirty_map_proc_pcid_match_inner(process_map: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool 
        recommends
            process_cpu_wf_inner(process_map, cpu_array)
    {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid]]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid] is Some
            ==>
            {
                &&&  
                process_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().process_ptr) 
                &&&
                process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().process_ptr).view().pcid == pcid
                &&&
                process_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().process_ptr).view().pagetable 
                    == cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap().pagetable_ptr
            }
    }
}
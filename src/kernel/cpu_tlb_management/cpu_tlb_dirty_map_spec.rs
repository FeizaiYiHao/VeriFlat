use vstd::prelude::*;
use crate::*;
verus! {
    pub proof fn cpu_dirty_tlb_map_wf_proof()
        ensures
            forall| cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB |
                cpu_dirty_tlb_map_wf(cpu_array, tlb) == cpu_dirty_tlb_map_wf_inner(cpu_array, tlb)
    {}

    pub closed spec fn cpu_dirty_tlb_map_wf(cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB) -> bool {
        cpu_dirty_tlb_map_wf_inner(cpu_array, tlb)
    }

    pub open spec fn cpu_dirty_tlb_map_wf_inner(cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>, tlb: CpuTLB) -> bool {
        &&&
        forall|cpu_id:CpuId|
            #![auto]
            cpu_id_valid(cpu_id) && cpu_array.spec_index(cpu_id).view().wlocked() == false
            ==>
            cpu_id_valid(cpu_id) && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()[cpu_array.spec_index(cpu_id).view().view().current_pcid]
                == Some(cpu_array.spec_index(cpu_id).view().view().current_pagetable)
        &&&
        forall|cpu_id:CpuId, pcid: Pcid|
            #![auto]
            cpu_id_valid(cpu_id) && pcid_valid(pcid)
            &&
            cpu_array.spec_index(cpu_id).view().wlocked() == false
            ==>
            (cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()[pcid] is Some) == (tlb.spec_index((cpu_id, pcid)).is_empty() == false)
    }
}
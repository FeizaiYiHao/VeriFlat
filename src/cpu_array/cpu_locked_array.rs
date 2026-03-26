use vstd::prelude::*;
use crate::*;

verus! {

pub struct LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>{
    pub cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>,
    pub tlb: CpuTLB,
} 

impl LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>{
    pub open spec fn get_cpu(&self, cpu_id:CpuId) -> RwLock<Cpu, CPU_HAS_KILL_STATE>
        recommends
            cpu_id_valid(cpu_id),
            self.inv(),
    {
        self.cpu_array[cpu_id]@
    }
    pub open spec fn get_tlb(&self, cpu_id:CpuId, pcid: Pcid) -> SingleTLB
        recommends
            cpu_id_valid(cpu_id),
            usize_in_range::<PCID_MAX>(pcid),
            self.inv(),
    {
        self.tlb.spec_index((cpu_id, pcid))
    }
    pub open spec fn inv(&self) -> bool{
        &&&
        self.cpu_array.inv()
        &&&
        self.locked_or_inv()
        &&&
        self.tlb.inv()
        &&&
        self.cpu_dirty_map_wf()
    }
    pub open spec fn locked_or_inv(&self) -> bool{
        &&&
        forall|cpu_id:CpuId|
            #![auto]
            cpu_id_valid(cpu_id)
            ==>{
                |||
                self.cpu_array.spec_index(cpu_id).view().wlocked()
                |||
                self.cpu_array.spec_index(cpu_id).inv()
            }
    }
    pub open spec fn cpu_dirty_map_wf(&self) -> bool{
        &&&
        forall|cpu_id:CpuId, pcid: Pcid|
            #![auto]
            cpu_id_valid(cpu_id) && usize_in_range::<PCID_MAX>(pcid)
            &&
            self.tlb.spec_index((cpu_id, pcid)).is_empty() == false
            ==>
            self.cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()[pcid] is Some
    }
}

}
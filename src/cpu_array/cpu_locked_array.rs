use vstd::prelude::*;
use crate::*;

verus! {

pub struct CpuArray{
    pub cpu_array: LockedArray<Cpu, NUM_CPUS>,
    pub tlb: CPUTLB,
} 

impl CpuArray{
    pub open spec fn get_cpu(&self, cpu_id:CpuId) -> RwLock<Cpu, false>
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
        self.cpus_wf()
        &&&
        self.tlb.inv()
        &&&
        self.cpu_drity_map_wf()
    }
    pub open spec fn cpus_wf(&self) -> bool{
        &&&
        forall|cpu_id:CpuId|
            #![auto]
            cpu_id_valid(cpu_id)
            ==>
            self.cpu_array.spec_index(cpu_id).inv()
    }
    pub open spec fn cpu_drity_map_wf(&self) -> bool{
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
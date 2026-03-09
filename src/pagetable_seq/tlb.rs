use vstd::prelude::*;

use super::super::*;

verus! {

pub ghost struct SingleTLB{
    pub tlb_4k: Map<VAddr, MapEntry>,
    pub tlb_2m: Map<VAddr, MapEntry>,
    pub tlb_1g: Map<VAddr, MapEntry>,
}

impl SingleTLB{
    pub open spec fn tlb_4k(&self) -> Map<VAddr, MapEntry> {
        self.tlb_4k
    }
    pub open spec fn tlb_2m(&self) -> Map<VAddr, MapEntry>{
        self.tlb_2m
    }
    pub open spec fn tlb_1g(&self) -> Map<VAddr, MapEntry>{
        self.tlb_1g
    }

    pub open spec fn is_empty(&self) -> bool{
        &&&
        self.tlb_4k().dom() == Set::<VAddr>::empty()
    }
}
 
pub struct CPUTLB{
    pub cpu_tlbs: Ghost<Seq<Seq<SingleTLB>>>,
}

impl CPUTLB{
    pub closed spec fn view(&self) -> Seq<Seq<SingleTLB>>{
        self.cpu_tlbs@
    }
    pub open spec fn inv(&self) -> bool{
        &&&
        self@.len() == NUM_CPUS  
        &&&
        forall|cpu_id:CpuId|
            #![auto]
            cpu_id_valid(cpu_id)
            ==>
            self[cpu_id].len() == PCID_MAX      
    }


    pub open spec fn tlb_va_wf(&self) -> bool{
        &&&
        forall|cpu_id: CpuId, pcid:Pcid, va:VAddr|
            #![auto]
            cpu_id_valid(cpu_id) && pcid_valid(pcid)
            ==>
            {
                &&&
                self[cpu_id][pcid as int].tlb_4k().contains_key(va) ==> va_4k_valid(va)
                &&&
                self[cpu_id][pcid as int].tlb_2m().contains_key(va) ==> va_2m_valid(va)
                &&&
                self[cpu_id][pcid as int].tlb_1g().contains_key(va) ==> va_1g_valid(va)
            }
    }
    // pub open spec fn disjoint_cpu_has_no_tlb_entry(&self) -> bool{
    //     &&&
    //     forall|cpu_id:CpuId|
    //         ![auto]
    //         self.active_cpus()@.contains(cpu_id)
    //         ==>
    //         self[cpu_id].is_empty()
    // }
    pub open spec fn spec_index(&self, index: CpuId) -> Seq<SingleTLB>
        recommends 
            cpu_id_valid(index),
    {
        self@[index as int]
    }

    pub open spec fn flush_tlb_4k_ensures(new:&Self, old:&Self, cpu_id: CpuId, pcid:Pcid, va: VAddr) -> bool{
        &&&
        no_change_except(new@, old@, cpu_id)
        &&&
        forall|pcid_i:Pcid|
            #![auto]
            pcid_valid(pcid_i) && pcid_i != pcid
            ==>
            no_change_except(new[cpu_id], old[cpu_id], pcid_i)
        &&&
        new[cpu_id][pcid as int].tlb_4k() == old[cpu_id][pcid as int].tlb_4k().remove(va)
        &&&
        new[cpu_id][pcid as int].tlb_2m() == old[cpu_id][pcid as int].tlb_2m()
        &&&
        new[cpu_id][pcid as int].tlb_1g() == old[cpu_id][pcid as int].tlb_1g()
    }

    #[verifier(external_body)]
    pub fn flush_tlb_4k(&mut self, cpu_id: CpuId, pcid:Pcid, va: VAddr)
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
            pcid_valid(pcid),
            va_4k_valid(va),
        ensures
            self.inv(),
            Self::flush_tlb_4k_ensures(self, old(self), cpu_id, pcid, va),
    {

    }
}

}
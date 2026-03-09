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
}


pub struct CPUTLB{
    pub cpu_tlbs: Ghost<Seq<SingleTLB>>,
    pcid: Pcid,
}

impl CPUTLB{
    pub closed spec fn view(&self) -> Seq<SingleTLB>{
        self.cpu_tlbs@
    }
    pub open spec fn wf(&self) -> bool{
        &&&
        self@.len() == NUM_CPUS        
        &&&
        pcid_valid(self.pcid()) 
    }
    pub open spec fn tlb_va_wf(&self) -> bool{
        &&&
        forall|cpu_id: CpuId, va:VAddr|
        cpu_id_valid(cpu_id) ==>
        {
            &&&
            self[cpu_id].tlb_4k().contains_key(va) ==> va_4k_valid(va)
            &&&
            self[cpu_id].tlb_2m().contains_key(va) ==> va_2m_valid(va)
            &&&
            self[cpu_id].tlb_1g().contains_key(va) ==> va_1g_valid(va)
        }
    }

    pub closed spec fn pcid(&self) -> Pcid{
        self.pcid
    }
    pub open spec fn spec_index(&self, index: CpuId) -> SingleTLB
        recommends 
            cpu_id_valid(index),
    {
        self@[index as int]
    }

    #[verifier(external_body)]
    pub fn flush_tlb_4k(&mut self, cpu_id: CpuId, pcid:Pcid, va: VAddr)
        requires
            old(self).wf(),
            pcid == old(self).pcid(),
            cpu_id_valid(cpu_id),
            va_4k_valid(va),
        ensures
            self.wf(),
            no_change_except(self@, old(self)@, cpu_id),
            self[cpu_id].tlb_4k() == old(self)[cpu_id].tlb_4k().remove(va),
            self[cpu_id].tlb_2m() == old(self)[cpu_id].tlb_2m(),
            self[cpu_id].tlb_1g() == old(self)[cpu_id].tlb_1g(),
    {

    }
}

}
use vstd::prelude::*;

use crate::*;

verus! {

pub ghost struct SingleTLB{
    pub tlb_4k: Map<VAddr, TLBEntry>,
    pub tlb_2m: Map<VAddr, TLBEntry>,
    pub tlb_1g: Map<VAddr, TLBEntry>,
}

impl SingleTLB{
    pub open spec fn tlb_4k(&self) -> Map<VAddr, TLBEntry> {
        self.tlb_4k
    }
    pub open spec fn tlb_2m(&self) -> Map<VAddr, TLBEntry>{
        self.tlb_2m
    }
    pub open spec fn tlb_1g(&self) -> Map<VAddr, TLBEntry>{
        self.tlb_1g
    }

    pub open spec fn is_empty(&self) -> bool{
        &&&
        self.tlb_4k().dom() == Set::<VAddr>::empty()
        &&&
        self.tlb_2m().dom() == Set::<VAddr>::empty()
        &&&
        self.tlb_1g().dom() == Set::<VAddr>::empty()
    }
}
 
pub struct CpuTLB{
    pub cpu_tlbs: Ghost<Map<(CpuId, Pcid), SingleTLB>>,
}

impl CpuTLB{
    pub closed spec fn view(&self) -> Map<(CpuId, Pcid), SingleTLB>{
        self.cpu_tlbs@
    }
    pub open spec fn spec_index(&self, index: (CpuId, Pcid) ) -> SingleTLB
        recommends 
            cpu_id_valid(index.0),
            usize_in_range::<PCID_MAX>(index.1)
    {
        self@[(index.0, index.1)]
    }
    pub closed spec fn inv(&self) -> bool{
        &&&
        self@.len() == NUM_CPUS  
        &&&
        forall|cpu_id: CpuId, pcid: Pcid|
            #![auto]
            self@.dom().contains((cpu_id, pcid)) 
            <==>
            cpu_id_valid(cpu_id) && usize_in_range::<PCID_MAX>(pcid)
    }
    // pub open spec fn disjoint_cpu_has_no_tlb_entry(&self) -> bool{
    //     &&&
    //     forall|cpu_id:CpuId|
    //         ![auto]
    //         self.active_cpus()@.contains(cpu_id)
    //         ==>
    //         self[cpu_id].is_empty()
    // }

    // pub open spec fn flush_tlb_4k_ensures(new:&Self, old:&Self, cpu_id: CpuId, pcid:Pcid, va: VAddr) -> bool{
    //     &&&
    //     no_change_except(new@, old@, cpu_id)
    //     &&&
    //     forall|pcid_i:Pcid|
    //         #![auto]
    //         usize_in_range(pcid_i) && pcid_i != pcid
    //         ==>
    //         no_change_except(new[cpu_id], old[cpu_id], pcid_i)
    //     &&&
    //     new[(cpu_id, pcid)].tlb_4k() == old[(cpu_id, pcid)].tlb_4k().remove(va)
    //     &&&
    //     new[(cpu_id, pcid)].tlb_2m() == old[(cpu_id, pcid)].tlb_2m()
    //     &&&
    //     new[(cpu_id, pcid)].tlb_1g() == old[(cpu_id, pcid)].tlb_1g()
    // }

    // #[verifier(external_body)]
    // pub fn flush_tlb_4k(&mut self, cpu_id: CpuId, pcid:Pcid, va: VAddr)
    //     requires
    //         old(self).inv(),
    //         cpu_id_valid(cpu_id),
    //         usize_in_range::<PCID_MAX>(pcid),
    //         va_4k_valid(va),
    //     ensures
    //         self.inv(),
    //         Self::flush_tlb_4k_ensures(self, old(self), cpu_id, pcid, va),
    // {

    // }
}

}

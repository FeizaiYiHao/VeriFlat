use vstd::prelude::*;

use crate::*;

verus! {

pub open spec fn spec_tlb_entry_equal_to_map_entry(tlb_entry:TLBEntry, map_entry: MapEntry) -> bool{
    &&&
    tlb_entry.addr == map_entry.addr
    &&&
    tlb_entry.execute_disable == map_entry.execute_disable
    &&&
    tlb_entry.write == map_entry.write
}

/// if the pagetable is locked, the TLB can have entry in which the entry is not present
/// otherwise TLB has to be a strict submap.
pub open spec fn single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_tlb: SingleTLB, pagetable: RwLock<PageTable, PAGE_TABLE_HAS_KILL_STATE>) -> bool
{
    &&&
    forall|va: VAddr|
        #![auto]
        va_4k_valid(va) && pagetable@.mapping_4k().dom().contains(va)
        ==>
        {
            |||
            cpu_tlb.tlb_4k().dom().contains(va) == false
            |||
            pagetable.wlocked() ||  pagetable@.mapping_4k()[va].present ==> spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_4k()[va], pagetable@.mapping_4k()[va])
        }
    &&&
    forall|va: VAddr|
        #![auto]
        va_2m_valid(va) && pagetable@.mapping_2m().dom().contains(va)
        ==>
        {
            |||
            cpu_tlb.tlb_2m().dom().contains(va) == false
            |||
            pagetable.wlocked() ||  pagetable@.mapping_2m()[va].present ==> spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_2m()[va], pagetable@.mapping_2m()[va])
        }
    &&&
    forall|va: VAddr|
        #![auto]
        va_1g_valid(va) && pagetable@.mapping_1g().dom().contains(va)
        ==>
        {
            |||
            cpu_tlb.tlb_1g().dom().contains(va) == false
            |||
            pagetable.wlocked() ||  pagetable@.mapping_1g()[va].present ==> spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_1g()[va], pagetable@.mapping_1g()[va])
        }
}

pub open spec fn single_cpu_tlb_subset_of_pagetable(cpu_pcid_tlbs: Seq<SingleTLB>, pagetable: RwLock<PageTable, PAGE_TABLE_HAS_KILL_STATE>) -> bool
    recommends
        cpu_pcid_tlbs.len() == PCID_MAX,
        pagetable@.pcid is Some,
{
    &&&
    cpu_pcid_tlbs.len() == PCID_MAX
    &&&
    pagetable@.pcid is Some
    &&&
    single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_pcid_tlbs[pagetable@.pcid.unwrap() as int], pagetable)
}

pub open spec fn tlb_subset_of_pagetable(cpu_tlb: Seq<Seq<SingleTLB>>, pagetable: RwLock<PageTable, PAGE_TABLE_HAS_KILL_STATE>) -> bool
        recommends
        cpu_tlb.len() == NUM_CPUS,
        forall|cpu_id:CpuId|
            #![auto] 
            cpu_id_valid(cpu_id)
            ==>
            cpu_tlb[cpu_id as int].len() == PCID_MAX,
        pagetable@.pcid is Some,
    {
        &&&
        forall|cpu_id:CpuId|
            #![auto] 
            cpu_id_valid(cpu_id)
            ==>
            single_cpu_tlb_subset_of_pagetable(cpu_tlb[cpu_id as int], pagetable)
    }

}

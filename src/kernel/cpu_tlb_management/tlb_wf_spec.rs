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

    /// For each va in the tlb
    /// The pagetable must have that va regardless if the pagetable is Acquired, and the pagetable must resolve to the same va. This is to prevent the physical page being used by other meanings.
    /// If the pagetable is Acquired, the va can have present bit unset, so that the tlb will not load this entry
    pub open spec fn single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_tlb: SingleTLB, pagetable: RwLock<PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>) -> bool
    {
        &&&
        forall|va: VAddr|
            #![trigger pagetable@.mapping_4k().dom().contains(va)]
            #![trigger cpu_tlb.tlb_4k()[va]]
            va_4k_valid(va) && cpu_tlb.tlb_4k().dom().contains(va) 
            ==>
            pagetable@.mapping_4k().dom().contains(va)
            && 
            pagetable.wlocked() == false ==> pagetable@.mapping_4k()[va].present
            &&
            spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_4k()[va], pagetable@.mapping_4k()[va])
        &&&
        forall|va: VAddr|
            #![trigger pagetable@.mapping_2m().dom().contains(va)]
            #![trigger cpu_tlb.tlb_2m()[va]]
            va_2m_valid(va) && cpu_tlb.tlb_4k().dom().contains(va) 
            ==>
            pagetable@.mapping_2m().dom().contains(va)
            && 
            pagetable.wlocked() == false ==> pagetable@.mapping_2m()[va].present
            &&
            spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_2m()[va], pagetable@.mapping_2m()[va])
        &&&
        forall|va: VAddr|
            #![trigger pagetable@.mapping_1g().dom().contains(va)]
            #![trigger cpu_tlb.tlb_1g()[va]]
            va_1g_valid(va) && cpu_tlb.tlb_1g().dom().contains(va) 
            ==>
            pagetable@.mapping_1g().dom().contains(va)
            && 
            pagetable.wlocked() == false ==> pagetable@.mapping_1g()[va].present
            &&
            spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_1g()[va], pagetable@.mapping_1g()[va])
    }

    /// There is no lock involved. This has to be true all the time.
    #[verifier::opaque]
    pub open spec fn tlb_wf_spec(cpu_tlb: CpuTLB, pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, (), (), (), NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        &&&
        forall|cpu_id:CpuId, pcid:Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            cpu_id_valid(cpu_id)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_tlb.spec_index((cpu_id, pcid)).is_empty() == false
            ==>
            single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), pagetable_map.spec_index(cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()[pcid].unwrap().pagetable_ptr))
    }
}

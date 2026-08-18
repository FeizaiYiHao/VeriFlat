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

    /// Every cached translation remains backed by the same kernel page-table
    /// mapping. The hardware present bit may already be clear while an old TLB
    /// entry awaits invalidation; this invariant does not encode that state
    /// through the page-table lock.
    pub open spec fn single_cpu_single_pcid_tlb_subset_of_pagetable(
        cpu_tlb: SingleTLB,
        pagetable: PageTable<PT_TYPE>,
    ) -> bool
    {
        &&&
        forall|va: VAddr|
            #![trigger pagetable.mapping_4k().dom().contains(va)]
            #![trigger cpu_tlb.tlb_4k().spec_index(va)]
            cpu_tlb.tlb_4k().dom().contains(va)
            ==>
            pagetable.mapping_4k().dom().contains(va)
            && spec_tlb_entry_equal_to_map_entry(
                cpu_tlb.tlb_4k().spec_index(va),
                pagetable.mapping_4k().spec_index(va),
            )
        &&&
        forall|va: VAddr|
            #![trigger pagetable.mapping_2m().dom().contains(va)]
            #![trigger cpu_tlb.tlb_2m().spec_index(va)]
            cpu_tlb.tlb_2m().dom().contains(va)
            ==>
            pagetable.mapping_2m().dom().contains(va)
            && spec_tlb_entry_equal_to_map_entry(
                cpu_tlb.tlb_2m().spec_index(va),
                pagetable.mapping_2m().spec_index(va),
            )
        &&&
        forall|va: VAddr|
            #![trigger pagetable.mapping_1g().dom().contains(va)]
            #![trigger cpu_tlb.tlb_1g().spec_index(va)]
            cpu_tlb.tlb_1g().dom().contains(va)
            ==>
            pagetable.mapping_1g().dom().contains(va)
            && spec_tlb_entry_equal_to_map_entry(
                cpu_tlb.tlb_1g().spec_index(va),
                pagetable.mapping_1g().spec_index(va),
            )
    }

    /// There is no lock involved. This has to be true all the time.
    #[verifier::opaque]
    pub open spec fn tlb_wf_spec(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, cpu_array: CpuLockedArray) -> bool {
        &&&
        forall|cpu_id:CpuId, pcid:Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_tlb.spec_index((cpu_id, pcid)).is_empty() == false
            ==>
            {
                let dirty_entry = cpu_array.spec_index(cpu_id).view().view()
                    .tlb_dirty_bitmap().spec_index(pcid);
                &&& dirty_entry is Some
                &&& pagetable_map.dom().contains(dirty_entry.unwrap().pagetable_ptr)
                &&& single_cpu_single_pcid_tlb_subset_of_pagetable(
                    cpu_tlb.spec_index((cpu_id, pcid)),
                    pagetable_map.spec_index(dirty_entry.unwrap().pagetable_ptr).view(),
                )
            }
    }
}

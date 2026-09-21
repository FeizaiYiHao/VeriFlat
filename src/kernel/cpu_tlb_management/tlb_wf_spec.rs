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

    /// Kernel mappings retain the backing records of translations awaiting
    /// invalidation, including entries whose hardware present bit is clear.
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

    pub open spec fn single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb: SingleTLB, pagetable: PageTable<PT_TYPE>) -> bool {
        &&& single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_tlb, pagetable)
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_4k().spec_index(va)] #![trigger pagetable.mapping_4k().spec_index(va)] cpu_tlb.tlb_4k().dom().contains(va) ==> pagetable.mapping_4k().spec_index(va).present
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_2m().spec_index(va)] #![trigger pagetable.mapping_2m().spec_index(va)] cpu_tlb.tlb_2m().dom().contains(va) ==> pagetable.mapping_2m().spec_index(va).present
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_1g().spec_index(va)] #![trigger pagetable.mapping_1g().spec_index(va)] cpu_tlb.tlb_1g().dom().contains(va) ==> pagetable.mapping_1g().spec_index(va).present
    }

    /// Unlock obligation over all non-exempt CPU/PCID associations of this table.
    pub open spec fn pagetable_tlb_entries_present(cpu_tlb: CpuTLB, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, pagetable_ptr: RwLockPageTableRoot, pagetable: PageTable<PT_TYPE>) -> bool {
        forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid)
            && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable_ptr
            ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), pagetable)
    }

    /// Non-present backing mappings require the page-table write lock.
    /// Inactive, marked PCIDs remain exempt until their next activation flush.
    #[verifier::opaque]
    pub open spec fn tlb_wf_spec(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray) -> bool {
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
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid)
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
                &&& !pagetable_map.spec_index(dirty_entry.unwrap().pagetable_ptr).wlocked() ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), pagetable_map.spec_index(dirty_entry.unwrap().pagetable_ptr).view())
            }
    }
}

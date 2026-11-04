use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn spec_tlb_entry_equal_to_map_entry(tlb_entry:TLBEntry, map_entry: MapEntry) -> bool {
        &&& tlb_entry.addr == map_entry.addr
        &&& tlb_entry.execute_disable == map_entry.execute_disable
        &&& tlb_entry.write == map_entry.write
    }

    /// A cached translation names the frame, write and execute-disable bits of the page-table entry `e`.
    pub open spec fn spec_tlb_entry_equal_to_page_entry(tlb_entry: TLBEntry, e: PageEntry) -> bool {
        &&& tlb_entry.addr == e.addr
        &&& tlb_entry.execute_disable == e.perm.execute_disable
        &&& tlb_entry.write == e.perm.write
    }

    /// Kernel mappings retain the backing records of translations awaiting
    /// invalidation, including entries whose hardware present bit is clear.
    /// Shared by CPU TLBs and the IOTLB.
    pub open spec fn single_tlb_subset_of_pagetable<const TABLE_TYPE: PTType>(cpu_tlb: SingleTLB, pagetable: PageTable<TABLE_TYPE>) -> bool {
        &&& forall|va: VAddr|
            #![trigger pagetable.mapping_4k().dom().contains(va)]
            #![trigger cpu_tlb.tlb_4k().spec_index(va)]
            #![trigger cpu_tlb.tlb_4k().dom().contains(va)]
            cpu_tlb.tlb_4k().dom().contains(va) ==> pagetable.mapping_4k().dom().contains(va) && spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_4k().spec_index(va), pagetable.mapping_4k().spec_index(va))
        &&& forall|va: VAddr|
            #![trigger pagetable.mapping_2m().dom().contains(va)]
            #![trigger cpu_tlb.tlb_2m().spec_index(va)]
            #![trigger cpu_tlb.tlb_2m().dom().contains(va)]
            cpu_tlb.tlb_2m().dom().contains(va) ==> pagetable.mapping_2m().dom().contains(va) && spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_2m().spec_index(va), pagetable.mapping_2m().spec_index(va))
        &&& forall|va: VAddr|
            #![trigger pagetable.mapping_1g().dom().contains(va)]
            #![trigger cpu_tlb.tlb_1g().spec_index(va)]
            #![trigger cpu_tlb.tlb_1g().dom().contains(va)]
            cpu_tlb.tlb_1g().dom().contains(va) ==> pagetable.mapping_1g().dom().contains(va) && spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_1g().spec_index(va), pagetable.mapping_1g().spec_index(va))
    }

    /// Every cached translation names a present leaf of the sequential table.
    pub open spec fn single_tlb_subset_of_present_pagetable<const TABLE_TYPE: PTType>(tlb: SingleTLB, pagetable: PageTable<TABLE_TYPE>) -> bool {
        &&& single_tlb_subset_of_pagetable(tlb, pagetable)
        &&& forall|va: VAddr| #![trigger tlb.tlb_4k().spec_index(va)] #![trigger pagetable.mapping_4k().spec_index(va)] tlb.tlb_4k().dom().contains(va) ==> pagetable.mapping_4k().spec_index(va).present
        &&& forall|va: VAddr| #![trigger tlb.tlb_2m().spec_index(va)] #![trigger pagetable.mapping_2m().spec_index(va)] tlb.tlb_2m().dom().contains(va) ==> pagetable.mapping_2m().spec_index(va).present
        &&& forall|va: VAddr| #![trigger tlb.tlb_1g().spec_index(va)] #![trigger pagetable.mapping_1g().spec_index(va)] tlb.tlb_1g().dom().contains(va) ==> pagetable.mapping_1g().spec_index(va).present
    }

    /// Every 4K or 2M translation a CPU TLB caches is a user leaf the table still holds, present or awaiting
    /// invalidation, with the same frame and permissions; every 1G translation names a leaf of `mapping_1g`.
    pub open spec fn single_tlb_subset_of_whole_pagetable(cpu_tlb: SingleTLB, pagetable: WholePageTable<PT_TYPE>) -> bool {
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_4k().dom().contains(va)]
            #![trigger cpu_tlb.tlb_4k().spec_index(va)]
            cpu_tlb.tlb_4k().dom().contains(va) ==> {
                let held = pagetable.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                &&& va_4k_valid(va)
                &&& pagetable.kernel_l4_end() <= spec_v2l4index(va)
                &&& held is Some
                &&& spec_tlb_entry_equal_to_page_entry(cpu_tlb.tlb_4k().spec_index(va), held->0)
            }
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_2m().dom().contains(va)]
            #![trigger cpu_tlb.tlb_2m().spec_index(va)]
            cpu_tlb.tlb_2m().dom().contains(va) ==> {
                let held = pagetable.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
                &&& va_2m_valid(va)
                &&& pagetable.kernel_l4_end() <= spec_v2l4index(va)
                &&& held is Some
                &&& spec_tlb_entry_equal_to_page_entry(cpu_tlb.tlb_2m().spec_index(va), held->0)
            }
        &&& forall|va: VAddr|
            #![trigger pagetable.mapping_1g().dom().contains(va)]
            #![trigger cpu_tlb.tlb_1g().spec_index(va)]
            #![trigger cpu_tlb.tlb_1g().dom().contains(va)]
            cpu_tlb.tlb_1g().dom().contains(va) ==> pagetable.mapping_1g().dom().contains(va) && spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_1g().spec_index(va), pagetable.mapping_1g().spec_index(va))
    }

    /// Every translation a CPU TLB caches is a held leaf of the table that also resolves and is present: the shape after a
    /// flush or a CR3 write.
    pub open spec fn single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb: SingleTLB, pagetable: WholePageTable<PT_TYPE>) -> bool {
        &&& single_tlb_subset_of_whole_pagetable(cpu_tlb, pagetable)
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_4k().spec_index(va)] #![trigger pagetable.spec_resolve_mapping_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))] cpu_tlb.tlb_4k().dom().contains(va) ==> {
                let leaf = pagetable.spec_resolve_mapping_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                &&& leaf is Some
                &&& leaf->0.perm.present
            }
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_2m().spec_index(va)] #![trigger pagetable.spec_resolve_mapping_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))] cpu_tlb.tlb_2m().dom().contains(va) ==> {
                let leaf = pagetable.spec_resolve_mapping_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
                &&& leaf is Some
                &&& leaf->0.perm.present
            }
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_1g().spec_index(va)] #![trigger pagetable.mapping_1g().spec_index(va)] cpu_tlb.tlb_1g().dom().contains(va) ==> pagetable.mapping_1g().spec_index(va).present
    }

    /// TLB `cpu_id` keeps a 4K or 2M translation the table no longer shows only while `cpu_id` is listed stale for it: by
    /// the record of its 2M window while the L3 path still resolves, by the table record otherwise. It keeps no hidden
    /// 1G translation.
    pub open spec fn single_tlb_present_or_stale(cpu_tlb: SingleTLB, pagetable: WholePageTable<PT_TYPE>, cpu_id: CpuId) -> bool {
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_4k().spec_index(va)]
            #![trigger pagetable.spec_resolve_mapping_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))]
            cpu_tlb.tlb_4k().dom().contains(va) ==> {
                let leaf = pagetable.spec_resolve_mapping_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                let key = (pagetable.window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va));
                !(leaf is Some && leaf->0.perm.present) ==> if pagetable.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some {
                    pagetable.lower.window_stale_cpus.dom().contains(key) && pagetable.lower.window_stale_cpus.spec_index(key).contains(cpu_id)
                } else {
                    pagetable.higher.table_stale_cpus.view().contains(cpu_id)
                }
            }
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_2m().spec_index(va)]
            #![trigger pagetable.spec_resolve_mapping_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))]
            cpu_tlb.tlb_2m().dom().contains(va) ==> {
                let leaf = pagetable.spec_resolve_mapping_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
                let key = (pagetable.window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va));
                !(leaf is Some && leaf->0.perm.present) ==> if pagetable.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some {
                    pagetable.lower.window_stale_cpus.dom().contains(key) && pagetable.lower.window_stale_cpus.spec_index(key).contains(cpu_id)
                } else {
                    pagetable.higher.table_stale_cpus.view().contains(cpu_id)
                }
            }
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_1g().spec_index(va)] #![trigger pagetable.mapping_1g().spec_index(va)] cpu_tlb.tlb_1g().dom().contains(va) ==> pagetable.mapping_1g().spec_index(va).present
    }

    /// Unlock obligation over all non-exempt CPU/PCID associations of this table.
    pub open spec fn pagetable_tlb_entries_present(cpu_tlb: CpuTLB, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, pagetable_ptr: RwLockPageTableRoot, pagetable: WholePageTable<PT_TYPE>) -> bool {
        forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid)
            && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable_ptr
                ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), pagetable)
    }

    /// A TLB keeps only held leaves of its CPU's dirty table, and a leaf the table no longer shows only while the CPU is
    /// listed stale for it. Inactive, marked PCIDs remain exempt until their next activation flush.
    #[verifier::opaque]
    pub open spec fn tlb_wf_spec(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray) -> bool {
        &&& forall|cpu_id:CpuId, pcid:Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID && cpu_tlb.spec_index((cpu_id, pcid)).is_empty() == false && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let dirty_entry = cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let table = whole_pagetable(pagetable_map, pt_lower, dirty_entry.unwrap().pagetable_ptr);
                &&& dirty_entry is Some
                &&& pagetable_map.dom().contains(dirty_entry.unwrap().pagetable_ptr)
                &&& single_tlb_subset_of_whole_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), table)
                &&& single_tlb_present_or_stale(cpu_tlb.spec_index((cpu_id, pcid)), table, cpu_id)
            }
    }

    /// A page table of `k` that lists no CPU stale, neither for a window nor for the whole table, keeps every TLB entry
    /// backed by it present.
    pub proof fn tlb_wf_pagetable_entries_present_at(k: KernelK, pagetable: RwLockPageTableRoot)
        requires
            tlb_wf_spec(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush),
            k.pt_mp.dom().contains(pagetable),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), pagetable).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures pagetable_tlb_entries_present(k.cpu_tlb, k.cpu_arr, k.pcid_needflush, pagetable, whole_pagetable(k.pt_mp, k.pt_lower.view(), pagetable)),
    { reveal(tlb_wf_spec); }
}

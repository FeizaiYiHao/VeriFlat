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
    /// This relation describes the IOTLB against its IOMMU table, which maps 4K leaves only: the IOTLB caches no 2M or 1G entry.
    pub open spec fn single_tlb_subset_of_pagetable(cpu_tlb: SingleTLB, pagetable: IommuTable) -> bool {
        &&& forall|va: VAddr|
            #![trigger pagetable.mapping_4k().dom().contains(va)]
            #![trigger cpu_tlb.tlb_4k().spec_index(va)]
            #![trigger cpu_tlb.tlb_4k().dom().contains(va)]
            cpu_tlb.tlb_4k().dom().contains(va) ==> pagetable.mapping_4k().dom().contains(va) && spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_4k().spec_index(va), pagetable.mapping_4k().spec_index(va))
        &&& cpu_tlb.tlb_2m().dom() =~= Set::<VAddr>::empty()
        &&& cpu_tlb.tlb_1g().dom() =~= Set::<VAddr>::empty()
    }

    /// Every cached translation names a present leaf of the sequential table.
    pub open spec fn single_tlb_subset_of_present_pagetable(tlb: SingleTLB, pagetable: IommuTable) -> bool {
        &&& single_tlb_subset_of_pagetable(tlb, pagetable)
        &&& forall|va: VAddr| #![trigger tlb.tlb_4k().spec_index(va)] #![trigger pagetable.mapping_4k().spec_index(va)] tlb.tlb_4k().dom().contains(va) ==> pagetable.mapping_4k().spec_index(va).present
    }

    /// Every 4K, 2M or 1G translation a CPU TLB caches is a user leaf the table still holds, present or awaiting invalidation, with the same frame and permissions.
    pub open spec fn single_tlb_subset_of_whole_pagetable(cpu_tlb: SingleTLB, pagetable: WholePageTable) -> bool {
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_4k().dom().contains(va)]
            #![trigger cpu_tlb.tlb_4k().spec_index(va)]
            cpu_tlb.tlb_4k().dom().contains(va) ==> {
                let nonempty = pagetable.spec_nonempty_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                &&& va_4k_valid(va)
                &&& pagetable.kernel_l4_end() <= spec_v2l4index(va)
                &&& nonempty is Some
                &&& spec_tlb_entry_equal_to_page_entry(cpu_tlb.tlb_4k().spec_index(va), nonempty->0)
            }
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_2m().dom().contains(va)]
            #![trigger cpu_tlb.tlb_2m().spec_index(va)]
            cpu_tlb.tlb_2m().dom().contains(va) ==> {
                let nonempty = pagetable.spec_nonempty_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
                &&& va_2m_valid(va)
                &&& pagetable.kernel_l4_end() <= spec_v2l4index(va)
                &&& nonempty is Some
                &&& spec_tlb_entry_equal_to_page_entry(cpu_tlb.tlb_2m().spec_index(va), nonempty->0)
            }
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_1g().dom().contains(va)]
            #![trigger cpu_tlb.tlb_1g().spec_index(va)]
            cpu_tlb.tlb_1g().dom().contains(va) ==> {
                let nonempty = pagetable.spec_nonempty_1g_l3(spec_v2l4index(va), spec_v2l3index(va));
                &&& va_1g_valid(va)
                &&& pagetable.kernel_l4_end() <= spec_v2l4index(va)
                &&& nonempty is Some
                &&& spec_tlb_entry_equal_to_page_entry(cpu_tlb.tlb_1g().spec_index(va), nonempty->0)
            }
    }

    /// Every translation a CPU TLB caches is a non-empty leaf of the table that also resolves and is present: the shape after a
    /// flush or a CR3 write.
    pub open spec fn single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb: SingleTLB, pagetable: WholePageTable) -> bool {
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
        &&& forall|va: VAddr| #![trigger cpu_tlb.tlb_1g().spec_index(va)] #![trigger pagetable.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va))] cpu_tlb.tlb_1g().dom().contains(va) ==> {
                let leaf = pagetable.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va));
                &&& leaf is Some
                &&& leaf->0.perm.present
            }
    }

    /// TLB `cpu_id` keeps a 4K or 2M translation the table no longer shows only while `cpu_id` is listed stale for it: by
    /// the record of its 2M window while the L3 path still resolves, by the table record otherwise; a 1G translation the
    /// table no longer shows only while `cpu_id` is listed in the table record.
    pub open spec fn single_tlb_present_or_stale(cpu_tlb: SingleTLB, pagetable: WholePageTable, cpu_id: CpuId) -> bool {
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
        &&& forall|va: VAddr|
            #![trigger cpu_tlb.tlb_1g().spec_index(va)]
            #![trigger pagetable.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va))]
            cpu_tlb.tlb_1g().dom().contains(va) ==> {
                let leaf = pagetable.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va));
                !(leaf is Some && leaf->0.perm.present) ==> pagetable.higher.table_stale_cpus.view().contains(cpu_id)
            }
    }

    /// Unlock obligation over all non-exempt CPU/PCID associations of this table.
    pub open spec fn pagetable_tlb_entries_present(cpu_tlb: CpuTLB, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, pagetable_ptr: RwLockPageTableRoot, pagetable: WholePageTable) -> bool {
        forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid)
            && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable_ptr
                ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), pagetable)
    }

    /// A TLB keeps only non-empty leaves of its CPU's dirty table, and a leaf the table no longer shows only while the CPU is
    /// listed stale for it. Inactive, marked PCIDs remain exempt until their next activation flush.
    #[verifier::opaque]
    pub open spec fn cpu_tlb_wf(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray) -> bool {
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

    /// `cpu_tlb_wf` at cpu `cpu_id` and PCID `pcid`.
    pub proof fn cpu_tlb_wf_at(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid)
        requires cpu_tlb_wf(cpu_tlb, pagetable_map, pt_lower, cpu_array, needflush),
        ensures
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID && cpu_tlb.spec_index((cpu_id, pcid)).is_empty() == false && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let dirty_entry = cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let table = whole_pagetable(pagetable_map, pt_lower, dirty_entry.unwrap().pagetable_ptr);
                &&& dirty_entry is Some
                &&& pagetable_map.dom().contains(dirty_entry.unwrap().pagetable_ptr)
                &&& single_tlb_subset_of_whole_pagetable(cpu_tlb.spec_index((cpu_id, pcid)), table)
                &&& single_tlb_present_or_stale(cpu_tlb.spec_index((cpu_id, pcid)), table, cpu_id)
            },
    { reveal(cpu_tlb_wf); }

    /// A page table of `k` that lists no CPU stale, neither for a window nor for the whole table, keeps every TLB entry
    /// backed by it present.
    pub proof fn tlb_wf_pagetable_entries_present_at(k: KernelK, pagetable: RwLockPageTableRoot)
        requires
            cpu_tlb_wf(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush),
            k.pt_mp.dom().contains(pagetable),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), pagetable).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures pagetable_tlb_entries_present(k.cpu_tlb, k.cpu_arr, k.pcid_needflush, pagetable, whole_pagetable(k.pt_mp, k.pt_lower.view(), pagetable)),
    { reveal(cpu_tlb_wf); }

    /// The translations of size `size` that `tlb` caches.
    pub open spec fn single_tlb_of_size(tlb: SingleTLB, size: PageSize) -> Map<VAddr, TLBEntry> {
        match size {
            PageSize::SZ4k => tlb.tlb_4k(),
            PageSize::SZ2m => tlb.tlb_2m(),
            PageSize::SZ1g => tlb.tlb_1g(),
        }
    }

    /// Every pending user store of a cpu was translated under the non-default PCID of the cpu's hardware cr3/pcid word, and
    /// the cpu's TLB for that PCID still caches the writable translation of its size at its base address with its frame. The
    /// PCID is valid, as every hardware cr3/pcid word's is.
    #[verifier::opaque]
    pub open spec fn pending_stores_covered_by_tlb(cpu_op: CpuOpArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, cpu_tlb: CpuTLB) -> bool {
        forall|c: CpuId, s: PendingStore| #![trigger cpu_op.store_buffer(c).contains(s)]
            index_valid(NUM_CPUS, c) && cpu_op.store_buffer(c).contains(s) ==> {
                let tlb = single_tlb_of_size(cpu_tlb.spec_index((c, s.pcid)), s.size);
                &&& pcid_valid(s.pcid)
                &&& s.pcid != KERNEL_DEFAULT_PCID
                &&& cpu_hw_cr3_pcid[c as int].view().1 == s.pcid
                &&& tlb.dom().contains(s.base_va)
                &&& tlb[s.base_va].write
                &&& tlb[s.base_va].addr == s.frame
            }
    }

    /// The pending user store `s` of cpu `cpu_id` is covered by the cpu's TLB.
    pub proof fn pending_stores_covered_by_tlb_at(cpu_op: CpuOpArray, cpu_hw_cr3_pcid: CpuHwCr3PcidArray, cpu_tlb: CpuTLB, cpu_id: CpuId, s: PendingStore)
        requires
            pending_stores_covered_by_tlb(cpu_op, cpu_hw_cr3_pcid, cpu_tlb),
            index_valid(NUM_CPUS, cpu_id),
            cpu_op.store_buffer(cpu_id).contains(s),
        ensures
            ({
                let tlb = single_tlb_of_size(cpu_tlb.spec_index((cpu_id, s.pcid)), s.size);
                &&& pcid_valid(s.pcid)
                &&& s.pcid != KERNEL_DEFAULT_PCID
                &&& cpu_hw_cr3_pcid[cpu_id as int].view().1 == s.pcid
                &&& tlb.dom().contains(s.base_va)
                &&& tlb[s.base_va].write
                &&& tlb[s.base_va].addr == s.frame
            }),
    { reveal(pending_stores_covered_by_tlb); }
}

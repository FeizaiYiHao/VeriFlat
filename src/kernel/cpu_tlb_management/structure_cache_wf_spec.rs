use vstd::prelude::*;
use crate::*;
verus! {
    /// Every directory entry a CPU's paging-structure cache keeps is a user entry the table still holds, present or as a
    /// placeholder, naming the same page: the structure-cache form of `single_tlb_subset_of_whole_pagetable`.
    pub open spec fn single_structure_cache_subset_of_whole_pagetable(cache: PagingStructureCache, table: WholePageTable<PT_TYPE>) -> bool {
        &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] #![trigger cache.pml4e.spec_index(i)]
            cache.pml4e.dom().contains(i) ==> table.kernel_l4_end() <= i && pei_valid(i) && table.spec_held_l4(i) is Some && table.spec_held_l4(i)->0.addr == cache.pml4e.spec_index(i)
        &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] #![trigger cache.pdpte.spec_index(key)]
            cache.pdpte.dom().contains(key) ==> table.kernel_l4_end() <= key.0 && pei_valid(key.0) && pei_valid(key.1)
                && table.spec_held_l3(key.0, key.1) is Some && table.spec_held_l3(key.0, key.1)->0.addr == cache.pdpte.spec_index(key)
        &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] #![trigger cache.pde.spec_index(key)]
            cache.pde.dom().contains(key) ==> table.kernel_l4_end() <= key.0 && pei_valid(key.0) && pei_valid(key.1) && pei_valid(key.2)
                && table.spec_held_l2(key.0, key.1, key.2) is Some && table.spec_held_l2(key.0, key.1, key.2)->0.addr == cache.pde.spec_index(key)
    }

    /// Every directory entry the cache keeps is held and its path resolves: the shape after a flush or a CR3 write, the
    /// structure-cache form of `single_cpu_single_pcid_tlb_subset_of_present_pagetable`.
    pub open spec fn single_structure_cache_subset_of_present_pagetable(cache: PagingStructureCache, table: WholePageTable<PT_TYPE>) -> bool {
        &&& single_structure_cache_subset_of_whole_pagetable(cache, table)
        &&& forall|i: L4Index| #![trigger cache.pml4e.spec_index(i)] cache.pml4e.dom().contains(i) ==> table.spec_resolve_mapping_l4(i) is Some
        &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.spec_index(key)] cache.pdpte.dom().contains(key) ==> table.spec_resolve_mapping_l3(key.0, key.1) is Some
        &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.spec_index(key)] cache.pde.dom().contains(key) ==> table.spec_resolve_mapping_l2(key.0, key.1, key.2) is Some
    }

    /// The cache of CPU `cpu_id` keeps a directory entry the table no longer resolves only while `cpu_id` is listed stale
    /// for it: an L2 entry by the record of its 2M window while the L3 path still resolves, any other entry by the table
    /// record. The structure-cache form of `single_tlb_present_or_stale`.
    pub open spec fn single_structure_cache_present_or_stale(cache: PagingStructureCache, table: WholePageTable<PT_TYPE>, cpu_id: CpuId) -> bool {
        &&& forall|i: L4Index| #![trigger cache.pml4e.spec_index(i)]
            cache.pml4e.dom().contains(i) && table.spec_resolve_mapping_l4(i) is None ==> table.higher.table_stale_cpus.view().contains(cpu_id)
        &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.spec_index(key)]
            cache.pdpte.dom().contains(key) && table.spec_resolve_mapping_l3(key.0, key.1) is None ==> table.higher.table_stale_cpus.view().contains(cpu_id)
        &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.spec_index(key)]
            cache.pde.dom().contains(key) && table.spec_resolve_mapping_l2(key.0, key.1, key.2) is None ==> if table.spec_resolve_mapping_l3(key.0, key.1) is Some {
                let stale_key = (table.window_l2_page(key.0, key.1), key.2);
                &&& table.lower.window_stale_cpus.dom().contains(stale_key)
                &&& table.lower.window_stale_cpus.spec_index(stale_key).contains(cpu_id)
            } else {
                table.higher.table_stale_cpus.view().contains(cpu_id)
            }
    }

    /// No usable paging-structure cache names table page `page`: under every non-default PCID that is current or not
    /// marked for flush, no CPU keeps an L4, L3, or L2 entry pointing at it. Inactive, marked PCIDs are flushed before
    /// their next activation, as in `structure_cache_wf`.
    pub open spec fn table_page_unreferenced_by_structure_caches(cpu_tlb: CpuTLB, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, page: PageMapPtr) -> bool {
        forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger cpu_tlb.structure_cache((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let cache = cpu_tlb.structure_cache((cpu_id, pcid));
                &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
                &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
                &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
            }
    }

    /// A CPU keeps paging-structure entries under a PCID only for its dirty table: each is an entry the table holds, and
    /// one the table no longer resolves only while the CPU is listed stale for it. Inactive, marked PCIDs remain exempt
    /// until their next activation flush, as in `cpu_tlb_wf`.
    #[verifier::opaque]
    pub open spec fn structure_cache_wf(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray) -> bool {
        forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger cpu_tlb.structure_cache((cpu_id, pcid))]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID && !cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let dirty_entry = cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let table = whole_pagetable(pagetable_map, pt_lower, dirty_entry.unwrap().pagetable_ptr);
                &&& dirty_entry is Some
                &&& pagetable_map.dom().contains(dirty_entry.unwrap().pagetable_ptr)
                &&& single_structure_cache_subset_of_whole_pagetable(cpu_tlb.structure_cache((cpu_id, pcid)), table)
                &&& single_structure_cache_present_or_stale(cpu_tlb.structure_cache((cpu_id, pcid)), table, cpu_id)
            }
    }

    pub proof fn structure_cache_wf_at(cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid)
        requires structure_cache_wf(cpu_tlb, pagetable_map, pt_lower, cpu_array, needflush),
        ensures
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID && !cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
            && (!needflush.spec_index(cpu_id, pcid).view().needflush || cpu_array.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let dirty_entry = cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let table = whole_pagetable(pagetable_map, pt_lower, dirty_entry.unwrap().pagetable_ptr);
                &&& dirty_entry is Some
                &&& pagetable_map.dom().contains(dirty_entry.unwrap().pagetable_ptr)
                &&& single_structure_cache_subset_of_whole_pagetable(cpu_tlb.structure_cache((cpu_id, pcid)), table)
                &&& single_structure_cache_present_or_stale(cpu_tlb.structure_cache((cpu_id, pcid)), table, cpu_id)
            },
    { reveal(structure_cache_wf); }

    /// A page of a table whose user roots all fail to resolve and which lists no CPU stale is named by no usable
    /// paging-structure cache: a cached entry is held by the cache's dirty table, so naming `page` it is that table, whose
    /// unresolvable entries the empty table record cannot cover.
    pub proof fn held_table_page_under_unresolvable_path_with_empty_table_record_implies_unreferenced_by_structure_caches(k: KernelK, table: RwLockPageTableRoot, page: PageMapPtr)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).page_closure().contains(page),
            forall|l4i: L4Index| #![trigger whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l4(l4i)]
                whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l4(l4i) is None,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures table_page_unreferenced_by_structure_caches(k.cpu_tlb, k.cpu_arr, k.pcid_needflush, page),
    { broadcast use held_table_page_under_unresolvable_path_with_empty_table_record_implies_unreferenced_by_structure_cache_at; }

    /// Point form of `held_table_page_under_unresolvable_path_with_empty_table_record_implies_unreferenced_by_structure_caches`
    /// at one `(cpu_id, pcid)`.
    broadcast proof fn held_table_page_under_unresolvable_path_with_empty_table_record_implies_unreferenced_by_structure_cache_at(k: KernelK, table: RwLockPageTableRoot, page: PageMapPtr, cpu_id: CpuId,
        pcid: Pcid)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).page_closure().contains(page),
            forall|l4i: L4Index| #![trigger whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l4(l4i)]
                whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l4(l4i) is None,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures
            #![trigger k.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), table).page_closure().contains(page)]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!k.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
                &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
                &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
                &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
            },
    {
        let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
        let dirty_ptr = k.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr;
        let dirty_table = whole_pagetable(k.pt_mp, k.pt_lower.view(), dirty_ptr);
        structure_cache_wf_at(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush, cpu_id, pcid);
        if !cache.is_empty() && k.pt_mp.dom().contains(dirty_ptr) {
            pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), dirty_ptr);
            assert(dirty_table.page_closure().contains(page) ==> dirty_ptr == table) by {
                if dirty_table.page_closure().contains(page) {
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, dirty_ptr, page);
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, table, page);
                }
            };
            reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2);
        }
    }

    /// The L2 page that the held L3 entry `(l4i, l3i)` of `table` links, or with `l1` the L1 page of its held L2 entry `l2i`, is named by no usable paging-structure cache once the L3 path no longer resolves and the table lists no CPU stale: a cached entry naming the page is the held L3
    /// entry or an L2 entry under it, whose unresolvable path the empty table record cannot cover.
    pub proof fn held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_caches(k: KernelK, table: RwLockPageTableRoot,
        l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, page: PageMapPtr)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i,
            pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l3(l4i, l3i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
            l1 ==> whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l2(l4i, l3i, l2i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
            page == (if l1 { whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l2(l4i, l3i, l2i)->0.addr } else { whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l3(l4i, l3i)->0.addr }),
        ensures table_page_unreferenced_by_structure_caches(k.cpu_tlb, k.cpu_arr, k.pcid_needflush, page),
    { broadcast use held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_cache_l2_page_at, held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_cache_l1_page_at; }

    /// Point form of `held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_caches` for the L2 page, at one `(cpu_id, pcid)`.
    broadcast proof fn held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_cache_l2_page_at(k: KernelK, table: RwLockPageTableRoot,
        l4i: L4Index, l3i: L3Index, cpu_id: CpuId, pcid: Pcid)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i,
            pei_valid(l4i),
            pei_valid(l3i),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l3(l4i, l3i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures
            #![trigger k.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i)]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!k.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
                let page = whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l3(l4i, l3i)->0.addr;
                &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
                &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
                &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
            },
    {
        let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
        let dirty_ptr = k.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr;
        let dirty_table = whole_pagetable(k.pt_mp, k.pt_lower.view(), dirty_ptr);
        let t = whole_pagetable(k.pt_mp, k.pt_lower.view(), table);
        let page = whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l3(l4i, l3i)->0.addr;
        structure_cache_wf_at(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush, cpu_id, pcid);
        pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), table);
        reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2); reveal(WholePageTable::table_pages_wf); reveal(PageTableHigher::table_pages_wf);
        assert(t.lower.l2_perms.dom().contains(t.spec_held_l3(l4i, l3i)->0.addr));
        if !cache.is_empty() && k.pt_mp.dom().contains(dirty_ptr) {
            pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), dirty_ptr);
            assert(dirty_table.page_closure().contains(page) ==> dirty_ptr == table) by {
                if dirty_table.page_closure().contains(page) {
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, dirty_ptr, page);
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, table, page);
                }
            };
            reveal(WholePageTable::disjoint_l2); reveal(PageTableHigher::disjoint_l4); reveal(PageTableHigher::disjoint_l3);
            broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        }
    }

    /// Point form of `held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_caches` for the L1 page, at one `(cpu_id, pcid)`.
    broadcast proof fn held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_cache_l1_page_at(k: KernelK, table: RwLockPageTableRoot,
        l4i: L4Index, l3i: L3Index, l2i: L2Index, cpu_id: CpuId, pcid: Pcid)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i,
            pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l3(l4i, l3i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l2(l4i, l3i, l2i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures
            #![trigger k.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l2(l4i, l3i, l2i)]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!k.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
                let page = whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l2(l4i, l3i, l2i)->0.addr;
                &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
                &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
                &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
            },
    {
        let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
        let dirty_ptr = k.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr;
        let dirty_table = whole_pagetable(k.pt_mp, k.pt_lower.view(), dirty_ptr);
        let t = whole_pagetable(k.pt_mp, k.pt_lower.view(), table);
        let page = whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_held_l2(l4i, l3i, l2i)->0.addr;
        structure_cache_wf_at(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush, cpu_id, pcid);
        pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), table);
        reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2); reveal(WholePageTable::table_pages_wf); reveal(PageTableHigher::table_pages_wf);
        assert(t.lower.l2_perms.dom().contains(t.spec_held_l3(l4i, l3i)->0.addr));
        assert(t.lower.l1_rev_map.dom().contains(t.spec_held_l2(l4i, l3i, l2i)->0.addr));
        if !cache.is_empty() && k.pt_mp.dom().contains(dirty_ptr) {
            pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), dirty_ptr);
            assert(dirty_table.page_closure().contains(page) ==> dirty_ptr == table) by {
                if dirty_table.page_closure().contains(page) {
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, dirty_ptr, page);
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, table, page);
                }
            };
            reveal(WholePageTable::disjoint_l2); reveal(PageTableHigher::disjoint_l4); reveal(PageTableHigher::disjoint_l3);
            broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        }
    }

    /// The L1 page `l1_p` that the L2 entry `(l4i, l3i, l2i)` of `table` hides under a resolving L3 path is named by no usable
    /// paging-structure cache once neither the window nor the table lists a CPU stale: a cached entry naming it is that L2
    /// entry of `table`, which no longer resolves and which no stale record covers.
    pub proof fn hidden_l1_page_without_window_stale_record_implies_unreferenced_by_structure_caches(k: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index,
        l2i: L2Index, l1_p: PageMapPtr)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i,
            pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.l2_entry_hides_l1(whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.l2_entry(whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i).addr == l1_p,
            !whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.window_stale_cpus.dom().contains((whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i)),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures table_page_unreferenced_by_structure_caches(k.cpu_tlb, k.cpu_arr, k.pcid_needflush, l1_p),
    { broadcast use hidden_l1_page_without_window_stale_record_implies_unreferenced_by_structure_cache_at; }

    /// Point form of `hidden_l1_page_without_window_stale_record_implies_unreferenced_by_structure_caches` at one
    /// `(cpu_id, pcid)`.
    broadcast proof fn hidden_l1_page_without_window_stale_record_implies_unreferenced_by_structure_cache_at(k: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index,
        l2i: L2Index, cpu_id: CpuId, pcid: Pcid)
        requires
            k.inv(),
            k.pt_mp.dom().contains(table),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).kernel_l4_end() <= l4i,
            pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is Some,
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.l2_entry_hides_l1(whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i),
            !whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.window_stale_cpus.dom().contains((whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i)),
            whole_pagetable(k.pt_mp, k.pt_lower.view(), table).higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ensures
            #![trigger k.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.l2_entry(whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i)]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!k.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
                let l1_p = whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.l2_entry(whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i).addr;
                &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != l1_p
                &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != l1_p
                &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != l1_p
            },
    {
        let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
        let dirty_ptr = k.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr;
        let dirty_table = whole_pagetable(k.pt_mp, k.pt_lower.view(), dirty_ptr);
        let l1_p = whole_pagetable(k.pt_mp, k.pt_lower.view(), table).lower.l2_entry(whole_pagetable(k.pt_mp, k.pt_lower.view(), table).window_l2_page(l4i, l3i), l2i).addr;
        structure_cache_wf_at(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush, cpu_id, pcid);
        pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), table);
        reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2);
        if !cache.is_empty() && k.pt_mp.dom().contains(dirty_ptr) {
            pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), dirty_ptr);
            assert(dirty_table.page_closure().contains(l1_p) ==> dirty_ptr == table) by {
                if dirty_table.page_closure().contains(l1_p) {
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, dirty_ptr, l1_p);
                    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, table, l1_p);
                }
            };
            reveal(WholePageTable::table_pages_wf); reveal(WholePageTable::disjoint_l2);
        }
    }

    /// A page of an IOMMU table is named by no usable paging-structure cache: a cached entry is held by the cache's dirty
    /// CPU table, whose pages are tagged as CPU-table pages, while the pages of an IOMMU table are tagged as IOMMU-table
    /// pages.
    pub proof fn iommu_table_page_implies_unreferenced_by_structure_caches(k: KernelK, iommu_table: RwLockPageTableRoot, page: PageMapPtr)
        requires
            k.inv(),
            k.it_mp.dom().contains(iommu_table),
            k.it_mp.spec_index(iommu_table).view().page_closure().contains(page),
        ensures table_page_unreferenced_by_structure_caches(k.cpu_tlb, k.cpu_arr, k.pcid_needflush, page),
    { broadcast use iommu_table_page_implies_unreferenced_by_structure_cache_at; }

    /// Point form of `iommu_table_page_implies_unreferenced_by_structure_caches` at one `(cpu_id, pcid)`.
    broadcast proof fn iommu_table_page_implies_unreferenced_by_structure_cache_at(k: KernelK, iommu_table: RwLockPageTableRoot, page: PageMapPtr, cpu_id: CpuId, pcid: Pcid)
        requires
            k.inv(),
            k.it_mp.dom().contains(iommu_table),
            k.it_mp.spec_index(iommu_table).view().page_closure().contains(page),
        ensures
            #![trigger k.cpu_tlb.structure_cache((cpu_id, pcid)), k.it_mp.spec_index(iommu_table).view().page_closure().contains(page)]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            && (!k.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
                let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
                &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
                &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
                &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
            },
    {
        let cache = k.cpu_tlb.structure_cache((cpu_id, pcid));
        let dirty_ptr = k.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr;
        let dirty_table = whole_pagetable(k.pt_mp, k.pt_lower.view(), dirty_ptr);
        structure_cache_wf_at(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush, cpu_id, pcid);
        if !cache.is_empty() && k.pt_mp.dom().contains(dirty_ptr) {
            pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), dirty_ptr);
            assert(!dirty_table.page_closure().contains(page)) by {
                iommu_table_pages_wf_closure_page_at(k.it_mp, k.pg_arr, iommu_table, page);
                if dirty_table.page_closure().contains(page) { pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, dirty_ptr, page); }
            };
            reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2);
        }
    }
}

use vstd::prelude::*;
use crate::*;

verus! {
/// The table page `pg_ptr` (the L1 page of entry `(l4i, l3i, l2i)` when `l1`, else the L2 page of the hidden L3 entry `(l4i, l3i)`) leaves the write-held `table`, every held leaf and mapping
/// staying, and returns through its free-list node at `node_addr` to shard `cpu_id` of the 4K allocator `allc_ptr` of its owner, whose quota grows by one.
#[verifier::opaque]
pub(super) open spec fn mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_allocator = pre.allc_4k_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allc_ptr);
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    let old_table = pre.pt_mp.spec_index(table);
    let new_table = post.pt_mp.spec_index(table);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), table);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, table)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(table, post.pt_lower.view().spec_index(table))
    &&& forall|r: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), r)]
        pre.pt_mp.dom().contains(r) && r != table ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), r) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), r)
    &&& new_table.locking_thread() == old_table.locking_thread()
    &&& new_table.being_killed() == old_table.being_killed()
    &&& new_table.view_ghost() == post.pt_lower.view().spec_index(table)
    &&& new_table.view().kernel_entries == old_table.view().kernel_entries
    &&& new_table.view().kernel_l4_end == old_table.view().kernel_l4_end
    &&& new_table.view().cr3 == old_table.view().cr3
    &&& new_table.view().pcid == old_table.view().pcid
    &&& new_table.view().did == old_table.view().did
    &&& new_table.view().proc_ptr == old_table.view().proc_ptr
    &&& new_table.view().table_stale_cpus.view() == Set::<CpuId>::empty()
    &&& new_c.page_closure() == old_c.page_closure().remove(pg_ptr)
    &&& new_c.mapping_4k() == old_c.mapping_4k()
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks
    &&& new_c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
    &&& new_c.lower.hidden_l1_tables_in_locked_windows()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_perms.dom().contains(p) ==> old_c.lower.l2_perms.dom().contains(p) && new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
    &&& forall|i4: L4Index| #![trigger new_c.spec_resolve_mapping_l4(i4)] #![trigger old_c.spec_resolve_mapping_l4(i4)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_resolve_mapping_l4(i4) == old_c.spec_resolve_mapping_l4(i4)
    &&& forall|i4: L4Index| #![trigger new_c.spec_held_l4(i4)] #![trigger old_c.spec_held_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_held_l4(i4) == old_c.spec_held_l4(i4)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_l3(i4, i3)] #![trigger old_c.spec_held_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (l1 || (i4, i3) != (l4i, l3i)) ==> new_c.spec_held_l3(i4, i3) == old_c.spec_held_l3(i4, i3)
    &&& !l1 ==> new_c.spec_held_l3(l4i, l3i) is None
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_l2(i4, i3, i2)] #![trigger old_c.spec_held_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && (!l1 || (i4, i3, i2) != (l4i, l3i, l2i)) ==> new_c.spec_held_l2(i4, i3, i2) == old_c.spec_held_l2(i4, i3, i2)
    &&& l1 ==> new_c.spec_held_l2(l4i, l3i, l2i) is None
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_held_4k_l1(i4, i3, i2, i1)] #![trigger old_c.spec_held_4k_l1(i4, i3, i2, i1)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_held_4k_l1(i4, i3, i2, i1) == old_c.spec_held_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_2m_l2(i4, i3, i2)] #![trigger old_c.spec_held_2m_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_2m_l2(i4, i3, i2) == old_c.spec_held_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_1g_l3(i4, i3)] #![trigger old_c.spec_held_1g_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_held_1g_l3(i4, i3) == old_c.spec_held_1g_l3(i4, i3)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i).view().view().state] #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == pg_idx { free_state } else { pre.pg_arr.spec_index(i).view().view().state }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings()
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page { state: free_state, free_list_node_storage: new_page.view().free_list_node_storage, perm_4k: new_page.view().perm_4k, ..old_page.view() })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allc_ptr)
    &&& new_allocator == (PageAllocator { cpu_caches: new_allocator.cpu_caches, total_free_pages: new_allocator.total_free_pages, quota: new_allocator.quota, ..old_allocator })
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, pg_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, pg_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.quota.view().value == old_allocator.quota.view().value + 1
    &&& new_allocator.quota.view() == (AllocatorQuota { value: new_allocator.quota.view().value, ..old_allocator.quota.view() })
    &&& new_allocator.quota.is_init() == old_allocator.quota.is_init()
    &&& new_allocator.quota.view_rodata() == old_allocator.quota.view_rodata()
    &&& new_allocator.quota.view_ghost() == old_allocator.quota.view_ghost()
    &&& new_allocator.quota.locking_thread() == old_allocator.quota.locking_thread()
    &&& new_allocator.quota.being_killed() == old_allocator.quota.being_killed()
}

proof fn mmap_1g_reclaim_table_page_to_cache_eof_subsystems_inv(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn mmap_1g_reclaim_table_page_to_cache_eof_table_pages(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: PT_TYPE } }),
        pre.pt_mp.dom().contains(table),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).page_closure().contains(pg_ptr),
        post.subsystems_inv(),
    ensures
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by {
        reveal(process_object_pages_owner_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
}

proof fn mmap_1g_reclaim_table_page_to_cache_eof_page_relations(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, owner: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: PT_TYPE } }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.pt_mp.dom().contains(table),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).page_closure().contains(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(post.pt_mp, post.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, pg_idx); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(pre.ctn_mp, pre.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        let proc_ptr = pre.pt_mp.spec_index(table).view().proc_ptr;
        process_object_pages_owner_wf_at(pre.prc_mp, pre.pt_mp, pre.it_mp, pre.pg_arr, pg_idx);
        reveal(process_pagetable_wf); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, proc_ptr);
        reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, pg_ptr);
    };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// Every l3 path of `table` that resolved before the page left still resolves to the same entry: it keeps its held entries and the changed slot never resolved.
proof fn mmap_1g_reclaim_table_page_to_cache_eof_resolved_l3(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(table),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
    ensures
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_l3(i4, i3)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(i4, i3) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_l3(i4, i3) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(i4, i3),
{
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, table); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), table);
    pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), table);
    broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq,
        PageTableHigher::spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve, WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq,
        WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
}

/// Every l2 path of `table` that resolved before the page left still resolves to the same entry: it keeps its held entries and the changed slot never resolved.
proof fn mmap_1g_reclaim_table_page_to_cache_eof_resolved_l2(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(table),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
    ensures
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_l2(i4, i3, i2)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l2(i4, i3, i2) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_l2(i4, i3, i2) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l2(i4, i3, i2),
{
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_l3(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, table); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), table);
    pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), table);
    broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq,
        PageTableHigher::spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve, WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq,
        WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
}

/// Every 4k path of `table` that resolved before the page left still resolves to the same entry: it keeps its held entries and the changed slot never resolved.
proof fn mmap_1g_reclaim_table_page_to_cache_eof_resolved_4k(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(table),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
    ensures
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_4k_l1(i4, i3, i2, i1) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_4k_l1(i4, i3, i2, i1),
{
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_l3(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_l2(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, table); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), table);
    pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), table);
    broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq,
        PageTableHigher::spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve, WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq,
        WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
}

/// Every 2m path of `table` that resolved before the page left still resolves to the same entry: it keeps its held entries and the changed slot never resolved.
proof fn mmap_1g_reclaim_table_page_to_cache_eof_resolved_2m(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(table),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
    ensures
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_2m_l2(i4, i3, i2)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_2m_l2(i4, i3, i2) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_2m_l2(i4, i3, i2) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_2m_l2(i4, i3, i2),
{
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_l3(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, table); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), table);
    pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), table);
    broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq,
        PageTableHigher::spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve, WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq,
        WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
}

/// Every 1g path of `table` that resolved before the page left still resolves to the same entry: it keeps its held entries and the changed slot never resolved.
proof fn mmap_1g_reclaim_table_page_to_cache_eof_resolved_1g(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(table),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
    ensures
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_1g_l3(i4, i3)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_1g_l3(i4, i3) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_held_1g_l3(i4, i3) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_held_1g_l3(i4, i3)
                    && whole_pagetable(post.pt_mp, post.pt_lower.view(), table).spec_resolve_mapping_1g_l3(i4, i3) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_1g_l3(i4, i3),
{
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, table); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), table);
    pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), table);
    broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq,
        PageTableHigher::spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve, WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq,
        WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
}

/// The TLBs and paging-structure caches stay inside their tables: `table` lists no CPU stale before or after, so each cached entry of it resolved before and still resolves to the same held entry.
proof fn mmap_1g_reclaim_table_page_to_cache_eof_cpu_caches(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(table),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pre.pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_l3(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_l2(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_4k(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_2m(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_resolved_1g(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(cpu_tlb_wf); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// The table page leaving the write-held table for the cpu cache of its owner, whose 4K quota grows by one, keeps the kernel invariant and every non-lock field of processes, threads, CPUs and endpoints.
pub(super) proof fn mmap_1g_reclaim_table_page_to_cache_eof(
    pre: KernelK, post: KernelK, table: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, pg_ptr: PagePtr, owner: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: PT_TYPE } }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.pt_mp.dom().contains(table),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).page_closure().contains(pg_ptr),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l3(l4i, l3i) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pre.pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        page_array_wf(post.pg_arr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
{
    mmap_1g_reclaim_table_page_to_cache_eof_subsystems_inv(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_table_pages(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_page_relations(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, owner, allc_ptr, cpu_id, node_addr);
    mmap_1g_reclaim_table_page_to_cache_eof_cpu_caches(pre, post, table, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr);
    reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
}
}

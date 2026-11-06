use vstd::prelude::*;
use crate::*;

verus! {
/// The hidden L1 page `l1_ptr` of the window of `va`, whose L2 page is `l2_ptr`, leaves the window half of `pagetable`, its
/// L2 entry published cleared and every mapping staying, and returns through its free-list node at `node_addr` to shard `cpu_id` of the 4K
/// allocator `allc_ptr` of its owner, whose quota grows by one; every other table and kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn reclaim_hidden_l1_page_to_cache_eof_transition_framing(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
) -> bool {
    let pg_idx = page_ptr2page_index(l1_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_allocator = pre.allc_4k_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allc_ptr);
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let target = (spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2);
    &&& post == (KernelK { pt_lower: post.pt_lower, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& new_c.page_closure() == old_c.page_closure().remove(l1_ptr)
    &&& new_c.mapping_4k() == old_c.mapping_4k()
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks
    &&& new_c.lower.l2_entry(l2_ptr, target.2).is_empty()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, target.2) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_page(p).entry_lock(i).l1()]
        old_c.lower.l2_perms.dom().contains(p) && (p, i) != (l2_ptr, target.2) ==> new_c.lower.l2_page(p).entry_lock(i).l1() == old_c.lower.l2_page(p).entry_lock(i).l1()
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != target ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_l2(target.0, target.1, target.2) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
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
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, l1_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, l1_ptr)
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

/// The held windows of `pagetable` other than the window of `va` keep their view: the L1 page leaves only the entry
/// `(l2_ptr, l2i)` of `va`'s window, and distinct windows name distinct L2 entries.
pub(super) proof fn reclaim_hidden_l1_page_to_cache_eof_held_windows(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
    lctx: LocalContext,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, &lctx),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
    ensures
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_view(w),
{
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let vi = spec_va2index(va);
    spec_va_4k_index_roundtrip_at(va, vi.0, vi.1, vi.2, vi.3);
    spec_va_4k_index_roundtrip_at(window_of(va).va, vi.0, vi.1, vi.2, 0usize);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, pagetable); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    assert forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va)
        implies new_c.window_view(w) == old_c.window_view(w) by {
        let l4w = spec_v2l4index(w.va);
        let l3w = spec_v2l3index(w.va);
        let l2w = spec_v2l2index(w.va);
        pagetable_window_typed_lock_map_aligned_at(pre.pt_mp, pre.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, w);
        spec_va_2m_valid_index_roundtrip(w.va);
        spec_index2va_injective();
        old_c.higher.disjoint_l4_l3_implies_resolve_l3_addr_unique_at(l4w, l3w, vi.0, vi.1);
        old_c.higher.wf_l4_at(l4w);
        old_c.l3_links_l2_wf_at(old_c.spec_resolve_mapping_l4(l4w)->0.addr, l3w);
        assert((old_c.window_l2_page(l4w, l3w), l2w) != (l2_ptr, vi.2));
    };
}

proof fn reclaim_hidden_l1_page_to_cache_eof_subsystems_inv(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(l1_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked);
}

proof fn reclaim_hidden_l1_page_to_cache_eof_table_pages(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(l1_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable, table_type: PT_TYPE } }),
        pre.pt_mp.dom().contains(pagetable),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).page_closure().contains(l1_ptr),
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
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
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

/// The table keeps its mappings, so the page records still match them before the page itself changes.
proof fn reclaim_hidden_l1_page_to_cache_eof_table_mappings(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(pagetable),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr),
{
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr)) by { broadcast use spec_va_2m_valid_index_roundtrip; reveal(mapped_2m_page_pagetable_wf); };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); };
}

proof fn reclaim_hidden_l1_page_to_cache_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(l1_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable, table_type: PT_TYPE } }),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().owning_container == owner,
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.pt_mp.dom().contains(pagetable),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).page_closure().contains(l1_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
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
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
    let pg_idx = page_ptr2page_index(l1_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    reclaim_hidden_l1_page_to_cache_eof_table_mappings(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr);
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
        let proc_ptr = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
        process_object_pages_owner_wf_at(pre.prc_mp, pre.pt_mp, pre.it_mp, pre.pg_arr, pg_idx);
        reveal(process_pagetable_wf); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, proc_ptr);
        reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, l1_ptr);
    };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// The paging-structure caches stay inside the table: no usable cache keeps the hidden entry, whose window lists no CPU stale.
proof fn reclaim_hidden_l1_page_to_cache_eof_cpu_caches(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_entry_hides_l1(l2_ptr, spec_va2index(va).2),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_va2index(va).2)),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
    spec_va_4k_index_roundtrip_at(va, spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    reclaim_hidden_l1_page_to_cache_eof_tlb(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr);
    reveal(structure_cache_wf);
}

/// The TLBs stay inside the table, whose mappings and stale records are unchanged.
proof fn reclaim_hidden_l1_page_to_cache_eof_tlb(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        pre.pt_mp.dom().contains(pagetable),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
    reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
}

/// The hidden L1 page leaving its table for the cpu cache of its owner, whose 4K quota grows by one, keeps the kernel
/// invariant and every non-lock field of processes, threads, CPUs and endpoints.
pub(super) proof fn reclaim_hidden_l1_page_to_cache_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(l1_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable, table_type: PT_TYPE } }),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().owning_container == owner,
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.pt_mp.dom().contains(pagetable),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).page_closure().contains(l1_ptr),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_entry_hides_l1(l2_ptr, spec_va2index(va).2),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_va2index(va).2)),
        pre.pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
{
    reclaim_hidden_l1_page_to_cache_eof_subsystems_inv(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr);
    reclaim_hidden_l1_page_to_cache_eof_table_pages(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr);
    reclaim_hidden_l1_page_to_cache_eof_page_relations(pre, post, pagetable, va, l2_ptr, l1_ptr, owner, allc_ptr, cpu_id, node_addr);
    reclaim_hidden_l1_page_to_cache_eof_cpu_caches(pre, post, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr);
    reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
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

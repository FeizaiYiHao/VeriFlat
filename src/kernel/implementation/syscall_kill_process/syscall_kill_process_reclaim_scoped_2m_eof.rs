use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_spec::kill_reclaim_held_2m_page_scoped_eof_transition_framing;

verus! {
/// Every page-owner relation holds after the last mapping of the 2M page `pg_ptr`, a held leaf of `pagetable`, leaves
/// with its record and the page returns to its owner's 2M allocator.
proof fn kill_reclaim_held_2m_page_scoped_eof_page_owners(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_2m_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_2m_valid(va)
            &&& old_c.kernel_l4_end() <= spec_v2l4index(va)
            &&& forall|l4i: L4Index| #![trigger old_c.spec_resolve_mapping_l4(l4i)] KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> old_c.spec_resolve_mapping_l4(l4i) is None
            &&& !old_c.mapping_2m().dom().contains(va)
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr
            &&& pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped2m
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& !pre.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
        }),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
{
    reveal(kill_reclaim_held_2m_page_scoped_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
}

/// Every page keeps the mapping records of the page tables after the last mapping of the 2M page `pg_ptr` leaves
/// `pagetable` and the page returns to its owner's 2M allocator.
proof fn kill_reclaim_held_2m_page_scoped_eof_page_mappings(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_2m_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_2m_valid(va)
            &&& old_c.kernel_l4_end() <= spec_v2l4index(va)
            &&& forall|l4i: L4Index| #![trigger old_c.spec_resolve_mapping_l4(l4i)] KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> old_c.spec_resolve_mapping_l4(l4i) is None
            &&& !old_c.mapping_2m().dom().contains(va)
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr
            &&& pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped2m
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& !pre.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
        }),
        post.subsystems_inv(),
    ensures
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(kill_reclaim_held_2m_page_scoped_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, pg_idx);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf); };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid; page_ptr_roundtrip(); reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf); };
}

/// The mapping relations and the allocator invariants hold after the last mapping of the 2M page `pg_ptr` leaves
/// `pagetable` and the page returns to its owner's 2M allocator.
proof fn kill_reclaim_held_2m_page_scoped_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_2m_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_2m_valid(va)
            &&& old_c.kernel_l4_end() <= spec_v2l4index(va)
            &&& forall|l4i: L4Index| #![trigger old_c.spec_resolve_mapping_l4(l4i)] KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> old_c.spec_resolve_mapping_l4(l4i) is None
            &&& !old_c.mapping_2m().dom().contains(va)
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr
            &&& pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped2m
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& !pre.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
        }),
        post.subsystems_inv(),
    ensures
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_reclaim_held_2m_page_scoped_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        let proc_ptr = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
        reveal(container_process_page_pagetable_wf); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, proc_ptr); reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
        reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        seq_insert_head_implies_contains::<PagePtr>(); page_ptr_roundtrip(); page_index_roundtrip();
    };
    reveal(allocator_free_2m_pages_wf);
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(pg_ptr)); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(pg_ptr)); };
}

/// The 2M page that returns to its owner's 2M allocator carries one unit of quota, which that allocator's quota gains.
proof fn kill_reclaim_held_2m_page_scoped_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_2m_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr),
        pre.allc_2m_mp.dom().contains(allc_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_reclaim_held_2m_page_scoped_eof_transition_framing);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
}

/// Every invariant holds after the last mapping of the 2M page `pg_ptr`, a held leaf of `pagetable` whose user root entries
/// no longer resolve, is cleared and the page returns to shard `cpu_id` of its owner's 2M allocator `allc_ptr`, whose quota
/// grows by one.
pub(crate) proof fn kill_reclaim_held_2m_page_scoped_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_2m_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_2m_valid(va)
            &&& old_c.kernel_l4_end() <= spec_v2l4index(va)
            &&& forall|l4i: L4Index| #![trigger old_c.spec_resolve_mapping_l4(l4i)] KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> old_c.spec_resolve_mapping_l4(l4i) is None
            &&& !old_c.mapping_2m().dom().contains(va)
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            &&& old_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr
            &&& pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped2m
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& !pre.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
        }),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().inv(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.spec_index(allc_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
{
    reveal(kill_reclaim_held_2m_page_scoped_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(page_array_wf); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    kill_reclaim_held_2m_page_scoped_eof_page_owners(pre, post, pagetable, va, pg_ptr, owner, allc_ptr, cpu_id, node_addr);
    kill_reclaim_held_2m_page_scoped_eof_page_mappings(pre, post, pagetable, va, pg_ptr, owner, allc_ptr, cpu_id, node_addr);
    kill_reclaim_held_2m_page_scoped_eof_page_relations(pre, post, pagetable, va, pg_ptr, owner, allc_ptr, cpu_id, node_addr);
    kill_reclaim_held_2m_page_scoped_eof_allocator_quota_wf(pre, post, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr);
    assert(post.memory_management_inv()) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    pre.default_pagetable_wf_at(pagetable);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip; };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
}
}

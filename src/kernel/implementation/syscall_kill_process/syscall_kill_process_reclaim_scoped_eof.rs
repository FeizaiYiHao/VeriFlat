use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_spec::{kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing, kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing,
    kill_retire_table_page_scoped_eof_transition_framing};

verus! {
/// The page relations and the allocator invariants hold after the last mapping of `page_ptr` leaves `pagetable` and the
/// page returns to its owner's 4K allocator.
proof fn kill_reclaim_unmapped_4k_page_scoped_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing(pre, post, pagetable, va, page_ptr, allocator_ptr, cpu_id, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_4k_valid(va)
            &&& pre.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)
            &&& !pre.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present
            &&& pre.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).addr == page_ptr
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
        }),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
        assert(pre.pg_arr.spec_index(page_index).view().view().mappings().contains((pagetable, va)) && pre.pg_arr.spec_index(page_index).view().view().iommu_mappings().len() == 0) by {
            reveal(mapped_4k_page_pagetable_wf); page_array_wf_at(pre.pg_arr, page_index);
        };
        reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf);
    };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_perms_wf); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(page_array_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
}

/// The page that returns to its owner's 4K allocator carries one unit of quota, which that allocator's quota gains.
proof fn kill_reclaim_unmapped_4k_page_scoped_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing(pre, post, pagetable, va, page_ptr, allocator_ptr, cpu_id, node_addr),
        pre.allc_4k_mp.dom().contains(allocator_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
}

/// Every invariant holds after the last mapping of `page_ptr`, a hidden leaf of `pagetable`, is removed and the page
/// returns to shard `cpu_id` of its owner's 4K allocator `allocator_ptr`, whose quota grows by one.
pub(crate) proof fn kill_reclaim_unmapped_4k_page_scoped_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing(pre, post, pagetable, va, page_ptr, allocator_ptr, cpu_id, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_4k_valid(va)
            &&& pre.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)
            &&& !pre.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present
            &&& pre.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).addr == page_ptr
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
        }),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable).inv(),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
{
    reveal(kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing);
    assert(pagetable_hidden_leaves_only_when_wlocked(post.pt_mp)) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(post.subsystems_inv()) by { reveal(pagetable_perms_wf); reveal(page_array_wf); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    kill_reclaim_unmapped_4k_page_scoped_eof_page_relations(pre, post, pagetable, va, page_ptr, owner, allocator_ptr, cpu_id, node_addr);
    kill_reclaim_unmapped_4k_page_scoped_eof_allocator_quota_wf(pre, post, pagetable, va, page_ptr, allocator_ptr, cpu_id, node_addr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
    assert(post.pt_mp.spec_index(pagetable).view().user_view(LockStateU::Unlocked).mapping_4k =~= pre.pt_mp.spec_index(pagetable).view().user_view(LockStateU::Unlocked).mapping_4k);
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
}

/// The page relations and the allocator invariants hold after the last mapping of `page_ptr` leaves the IOMMU table
/// `iommu_table` and the page returns to its owner's 4K allocator.
proof fn kill_reclaim_unmapped_iommu_4k_page_scoped_eof_page_relations(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, allocator_ptr, cpu_id, node_addr),
        ({
            let iova = spec_index2va(indices);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& pre.it_mp.dom().contains(iommu_table)
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova)
            &&& !pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).present
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr
            &&& pre.it_mp.spec_index(iommu_table).locking_thread() is Write
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
        }),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(pre.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, spec_index2va(indices))) && pre.pg_arr.spec_index(page_index).view().view().mappings().len() == 0) by {
        reveal(page_iommu_table_wf); page_array_wf_at(pre.pg_arr, page_index); page_ptr_roundtrip();
    };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_perms_wf); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(page_array_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        container_process_page_pagetable_wf_preserved_for_page_mapping_fields_eq(post.ctn_mp, post.prc_mp, post.pt_mp, pre.pg_arr, post.pg_arr);
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
    };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
}

/// The page that returns to its owner's 4K allocator carries one unit of quota, which that allocator's quota gains.
proof fn kill_reclaim_unmapped_iommu_4k_page_scoped_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, allocator_ptr, cpu_id, node_addr),
        pre.allc_4k_mp.dom().contains(allocator_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
}

/// Every invariant holds after the last mapping of `page_ptr`, a hidden leaf of the IOMMU table `iommu_table`, is removed
/// and the page returns to shard `cpu_id` of its owner's 4K allocator `allocator_ptr`, whose quota grows by one.
pub(crate) proof fn kill_reclaim_unmapped_iommu_4k_page_scoped_eof(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, allocator_ptr, cpu_id, node_addr),
        ({
            let iova = spec_index2va(indices);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& pre.it_mp.dom().contains(iommu_table)
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova)
            &&& !pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).present
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr
            &&& pre.it_mp.spec_index(iommu_table).locking_thread() is Write
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
        }),
        iommu_table_perms_wf(post.it_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
{
    reveal(kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(pagetable_perms_wf); reveal(page_array_wf); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    kill_reclaim_unmapped_iommu_4k_page_scoped_eof_page_relations(pre, post, iommu_table, indices, page_ptr, owner, allocator_ptr, cpu_id, node_addr);
    kill_reclaim_unmapped_iommu_4k_page_scoped_eof_allocator_quota_wf(pre, post, iommu_table, indices, page_ptr, allocator_ptr, cpu_id, node_addr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); reveal(iommu_table_lock_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
    assert(post.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k =~= pre.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k);
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
}

proof fn kill_retire_table_page_scoped_eof_subsystems_inv(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_scoped_eof_transition_framing(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr),
        page_ptr_valid(page_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(kill_retire_table_page_scoped_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn kill_retire_table_page_scoped_eof_table_pages(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_scoped_eof_transition_framing(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr),
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        iommu ==> pre.it_mp.dom().contains(table) && pre.it_mp.spec_index(table).view().page_closure().contains(page_ptr),
        !iommu ==> pre.pt_mp.dom().contains(table) && pre.pt_mp.spec_index(table).view().page_closure().contains(page_ptr),
        post.subsystems_inv(),
    ensures
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.it_mp, post.pg_arr),
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp),
{
    reveal(kill_retire_table_page_scoped_eof_transition_framing);
    if iommu {
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
        assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
    } else {
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
        assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    }
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_kernel_pages_owner_wf); reveal(pagetable_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
}

proof fn kill_retire_table_page_scoped_eof_page_relations(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_scoped_eof_transition_framing(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr),
        page_ptr_valid(page_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        iommu ==> pre.it_mp.dom().contains(table) && pre.it_mp.spec_index(table).view().page_closure().contains(page_ptr),
        !iommu ==> pre.pt_mp.dom().contains(table) && pre.pt_mp.spec_index(table).view().page_closure().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_retire_table_page_scoped_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    if iommu {
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    } else {
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(pre.ctn_mp, pre.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, page_index); };
    }
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

proof fn kill_retire_table_page_scoped_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_scoped_eof_transition_framing(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr),
        pre.allc_4k_mp.dom().contains(allocator_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_retire_table_page_scoped_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
}

/// The table page leaving its zombie table for the cpu cache of its owner, whose 4K quota grows by one, keeps the kernel
/// invariant and every non-lock field of processes, threads, CPUs and endpoints.
pub(crate) proof fn kill_retire_table_page_scoped_eof(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_scoped_eof_transition_framing(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr),
        page_ptr_valid(page_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        iommu ==> pre.it_mp.dom().contains(table) && pre.it_mp.spec_index(table).view().page_closure().contains(page_ptr),
        !iommu ==> pre.pt_mp.dom().contains(table) && pre.pt_mp.spec_index(table).view().page_closure().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        !iommu ==> (pagetable_tlb_entries_present(pre.cpu_tlb, pre.cpu_arr, pre.pcid_needflush, table, pre.pt_mp.spec_index(table).view())
            ==> pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, table, post.pt_mp.spec_index(table).view())),
        !iommu ==> (pre.pt_mp.spec_index(table).view().leaves_present() ==> post.pt_mp.spec_index(table).view().leaves_present()),
        iommu ==> (pre.it_mp.spec_index(table).view().leaves_present() ==> post.it_mp.spec_index(table).view().leaves_present()),
{
    kill_retire_table_page_scoped_eof_subsystems_inv(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr);
    kill_retire_table_page_scoped_eof_table_pages(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr);
    kill_retire_table_page_scoped_eof_page_relations(pre, post, iommu, table, page_ptr, owner, allocator_ptr, cpu_id, node_addr);
    kill_retire_table_page_scoped_eof_allocator_quota_wf(pre, post, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr);
    reveal(kill_retire_table_page_scoped_eof_transition_framing);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_table_lock_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
}
}

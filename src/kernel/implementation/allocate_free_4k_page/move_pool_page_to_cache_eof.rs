use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;

verus! {
#[verifier::opaque]
pub(super) open spec fn move_pool_page_to_cache_eof_transition_framing(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr, node: usize) -> bool {
    let index = page_ptr2page_index(pg_ptr);
    let old_page = pre.pg_arr.spec_index(index).view();
    let new_page = post.pg_arr.spec_index(index).view();
    let old_allocator = pre.allc_4k_mp.spec_index(allocator);
    let new_allocator = post.allc_4k_mp.spec_index(allocator);
    let old_cache = old_allocator.cpu_caches.spec_index(cpu_id).view();
    let new_cache = new_allocator.cpu_caches.spec_index(cpu_id).view();
    &&& post == (KernelK { pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, index)
    &&& new_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::PreCpuCache { cpu_id } }, ..old_page.view() })
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator)
    &&& new_allocator == (PageAllocator { cpu_caches: new_allocator.cpu_caches, global_pool: new_allocator.global_pool, ..old_allocator })
    &&& old_allocator.global_pool.view().map().dom().contains(node)
    &&& old_allocator.global_pool.view().map().spec_index(node) == pg_ptr
    &&& new_allocator.global_pool.view().view() == old_allocator.global_pool.view().view().skip(1)
    &&& new_allocator.global_pool.view().map() == old_allocator.global_pool.view().map().remove(node)
    &&& new_allocator.global_pool.is_init()
    &&& new_allocator.global_pool.lock_id() == old_allocator.global_pool.lock_id()
    &&& new_allocator.global_pool.locking_thread() == old_allocator.global_pool.locking_thread()
    &&& new_allocator.global_pool.being_killed() == old_allocator.global_pool.being_killed()
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& !old_cache.view().map().dom().contains(node)
    &&& new_cache.view().view() == old_cache.view().view().insert(0, pg_ptr)
    &&& new_cache.view().map() == old_cache.view().map().insert(node, pg_ptr)
    &&& new_cache.is_init()
    &&& new_cache.locking_thread() == old_cache.locking_thread()
    &&& new_cache.being_killed() == old_cache.being_killed()
    &&& new_allocator.cpu_caches.spec_index(cpu_id).lock_id() == old_allocator.cpu_caches.spec_index(cpu_id).lock_id()
}

/// The refilled allocator's owner holds a pooled free page, so it is not retire-ready: a retire-ready container has no
/// user and zero quota, hence no free page.
proof fn move_pool_page_to_cache_eof_kill_retire_wf(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr, node: usize)
    requires
        pre.inv(),
        move_pool_page_to_cache_eof_transition_framing(pre, post, allocator, cpu_id, pg_ptr, node),
        pre.allc_4k_mp.dom().contains(allocator),
        pre.allc_4k_mp.spec_index(allocator).global_pool.view().view().len() > 0,
    ensures
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(move_pool_page_to_cache_eof_transition_framing);
    let owner = pre.allc_4k_mp.spec_index(allocator).owning_container;
    assert(pre.ctn_mp.dom().contains(owner) && pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator) by { reveal(container_allocator_wf); };
    if pre.ctn_mp.spec_index(owner).view_ghost().retire_ready {
        container_kill_retire_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, owner); lemma_container_allocator_quota_eq_total_free_without_users(pre, owner);
        allocator_perms_wf_at(pre.allc_4k_mp, allocator); lemma_cache_len_fold_nonneg(pre.allc_4k_mp.spec_index(allocator).cpu_caches.view());
        pre.allc_4k_mp.spec_index(allocator).global_pool.view().wf_implies_view_len_eq_len();
    }
    reveal(container_kill_retire_wf); reveal(container_allocator_wf);
}

/// EOF closure leaf: the CPU-cache and global-pool free-page invariants after the move.
proof fn move_pool_page_to_cache_eof_free_4k_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr, node: usize)
    requires
        pre.inv(),
        move_pool_page_to_cache_eof_transition_framing(pre, post, allocator, cpu_id, pg_ptr, node),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_allocator = pre.allc_4k_mp.spec_index(allocator);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& page_ptr_valid(pg_ptr)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))
            &&& pre.allc_4k_mp.dom().contains(allocator)
            &&& old_allocator.global_pool.view().view().len() > 0
            &&& old_allocator.global_pool.view().view().spec_index(0) == pg_ptr
            &&& old_allocator.global_pool.view().view().no_duplicates()
            &&& old_page.state == (PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList })
            &&& !old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)
            &&& node == old_page.free_list_node_storage.addr()
        }),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator).wf(),
    ensures
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    reveal(move_pool_page_to_cache_eof_transition_framing);
    assert(allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr) && allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective(); seq_skip_one_implies_contains_and_index_shift::<PagePtr>();
        pre.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, pg_ptr);
    };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); };
}

pub(super) proof fn move_pool_page_to_cache_eof(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr, node: usize)
    requires
        pre.inv(),
        move_pool_page_to_cache_eof_transition_framing(pre, post, allocator, cpu_id, pg_ptr, node),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_allocator = pre.allc_4k_mp.spec_index(allocator);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& page_ptr_valid(pg_ptr)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))
            &&& pre.allc_4k_mp.dom().contains(allocator)
            &&& old_allocator.global_pool.view().view().len() > 0
            &&& old_allocator.global_pool.view().view().spec_index(0) == pg_ptr
            &&& old_allocator.global_pool.view().view().no_duplicates()
            &&& old_page.state == (PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList })
            &&& !old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)
            &&& node == old_page.free_list_node_storage.addr()
        }),
        page_array_wf(post.pg_arr),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator).wf(),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(move_pool_page_to_cache_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(post.subsystems_inv()) by { reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
        };
        assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(post.ctn_mp, post.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, pg_idx); };
        assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
        move_pool_page_to_cache_eof_kill_retire_wf(pre, post, allocator, cpu_id, pg_ptr, node);
        assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, pg_idx); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(pg_idx).view().view().mappings() == pre.pg_arr.spec_index(pg_idx).view().view().mappings());
            reveal(process_emptied_tables_wf);
        };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_4k_pages_wf); };
        assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
            thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
        move_pool_page_to_cache_eof_free_4k_pages(pre, post, allocator, cpu_id, pg_ptr, node);
        assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
        assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
}

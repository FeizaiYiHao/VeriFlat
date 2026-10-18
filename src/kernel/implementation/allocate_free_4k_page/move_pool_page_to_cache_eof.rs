use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub(super) open spec fn move_pool_page_to_cache_eof_transition_framing(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, page_ptr: PagePtr, node: usize) -> bool {
    let index = page_ptr2page_index(page_ptr);
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
    &&& old_allocator.global_pool.view().map().spec_index(node) == page_ptr
    &&& new_allocator.global_pool.view().view() == old_allocator.global_pool.view().view().skip(1)
    &&& new_allocator.global_pool.view().map() == old_allocator.global_pool.view().map().remove(node)
    &&& new_allocator.global_pool.is_init()
    &&& new_allocator.global_pool.lock_id() == old_allocator.global_pool.lock_id()
    &&& new_allocator.global_pool.locking_thread() == old_allocator.global_pool.locking_thread()
    &&& new_allocator.global_pool.being_killed() == old_allocator.global_pool.being_killed()
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& !old_cache.view().map().dom().contains(node)
    &&& new_cache.view().view() == old_cache.view().view().insert(0, page_ptr)
    &&& new_cache.view().map() == old_cache.view().map().insert(node, page_ptr)
    &&& new_cache.is_init()
    &&& new_cache.locking_thread() == old_cache.locking_thread()
    &&& new_cache.being_killed() == old_cache.being_killed()
    &&& new_allocator.cpu_caches.spec_index(cpu_id).lock_id() == old_allocator.cpu_caches.spec_index(cpu_id).lock_id()
}

pub(super) proof fn move_pool_page_to_cache_eof(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, page_ptr: PagePtr, node: usize)
    requires
        pre.inv(),
        move_pool_page_to_cache_eof_transition_framing(pre, post, allocator, cpu_id, page_ptr, node),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            let old_allocator = pre.allc_4k_mp.spec_index(allocator);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& page_ptr_valid(page_ptr)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page_ptr))
            &&& pre.allc_4k_mp.dom().contains(allocator)
            &&& old_allocator.global_pool.view().view().len() > 0
            &&& old_allocator.global_pool.view().view().spec_index(0) == page_ptr
            &&& old_allocator.global_pool.view().view().no_duplicates()
            &&& old_page.state == (PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList })
            &&& !old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
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
    let page_index = page_ptr2page_index(page_ptr);
    assert(post.subsystems_inv()) by { reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(post.ctn_mp, post.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
        assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
        assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
        assert(container_allocator_cpu_cache_free_4k_page_wf(post.allc_4k_mp, post.pg_arr) && container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
            reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
            page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective(); seq_skip_lemma::<PagePtr>();
            pre.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr);
        };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
}

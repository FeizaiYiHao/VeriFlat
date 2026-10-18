use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after a 4K allocator quota, cache, or global-pool lock operation: only that sub-lock's state moved.
pub(super) proof fn allocator_4k_lock_op_eof(pre: KernelK, post: KernelK, alloc_ptr: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        post == (KernelK { allc_4k_mp: post.allc_4k_mp, ..pre }),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, alloc_ptr),
        post.allc_4k_mp.spec_index(alloc_ptr).inv(),
        allocator_invariant_fields_unchanged(pre.allc_4k_mp, post.allc_4k_mp),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        lemma_allocator_pages_wf_preserved_for_allocator_invariant_fields_except_quota_forall();
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf);
        lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall();
        lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(pre, post);
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}

/// Closes `inv()` after a 2M allocator quota, cache, or global-pool lock operation: only that sub-lock's state moved.
pub(super) proof fn allocator_2m_lock_op_eof(pre: KernelK, post: KernelK, alloc_ptr: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        post == (KernelK { allc_2m_mp: post.allc_2m_mp, ..pre }),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, alloc_ptr),
        post.allc_2m_mp.spec_index(alloc_ptr).inv(),
        allocator_invariant_fields_unchanged(pre.allc_2m_mp, post.allc_2m_mp),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    assert(allocator_perms_wf(post.allc_2m_mp)) by { reveal(allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp); };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(pre, post); };
    assert(post.memory_management_inv()) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}

/// Closes `inv()` after a 1G allocator quota lock operation: only the quota lock's state moved.
pub(super) proof fn allocator_1g_lock_op_eof(pre: KernelK, post: KernelK, alloc_ptr: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        post == (KernelK { allc_1g_mp: post.allc_1g_mp, ..pre }),
        post.allc_1g_mp.perms_wf(),
        post.allc_1g_mp.unchanged_except(&pre.allc_1g_mp, alloc_ptr),
        post.allc_1g_mp.spec_index(alloc_ptr).inv(),
        allocator_invariant_fields_unchanged(pre.allc_1g_mp, post.allc_1g_mp),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    assert(allocator_perms_wf(post.allc_1g_mp)) by { reveal(allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp); };
    assert(allocator_free_page_ptrs_wf(post.allc_1g_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { lemma_container_allocator_free_1g_page_wf_preserved_for_lock_op(pre, post); };
    assert(post.memory_management_inv()) by { reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
} // verus!

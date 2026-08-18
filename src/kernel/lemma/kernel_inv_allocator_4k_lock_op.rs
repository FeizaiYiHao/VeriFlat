use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Semantic allocator fields read by kernel invariants.  Internal quota,
/// cache, and global-pool lock owners are deliberately excluded.
#[verifier::opaque]
pub open spec fn allocator_4k_invariant_fields_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|a_ptr: RwLockPageAllocatorPtr|
        #![trigger post.spec_index(a_ptr).owning_container]
        pre.dom().contains(a_ptr) ==>
        {
            &&& post.spec_index(a_ptr).owning_container
                == pre.spec_index(a_ptr).owning_container
            &&& post.spec_index(a_ptr).total_free_pages
                == pre.spec_index(a_ptr).total_free_pages
            &&& post.spec_index(a_ptr).quota.view()
                == pre.spec_index(a_ptr).quota.view()
            &&& post.spec_index(a_ptr).global_pool.view()
                == pre.spec_index(a_ptr).global_pool.view()
            &&& forall|cpu_id: CpuId|
                #![trigger post.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                index_valid(NUM_CPUS, cpu_id) ==>
                    post.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
                    == pre.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
        }
}

pub proof fn allocator_4k_cache_lock_op_preserves_invariant_fields(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    changed_allocator: RwLockPageAllocatorPtr,
    changed_cpu: CpuId,
)
    requires
        pre.dom() =~= post.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(a_ptr)]
            pre.dom().contains(a_ptr)
                && a_ptr != changed_allocator ==>
                post.spec_index(a_ptr) == pre.spec_index(a_ptr),
        post.spec_index(changed_allocator).owning_container
            == pre.spec_index(changed_allocator).owning_container,
        post.spec_index(changed_allocator).total_free_pages
            == pre.spec_index(changed_allocator).total_free_pages,
        post.spec_index(changed_allocator).quota
            == pre.spec_index(changed_allocator).quota,
        post.spec_index(changed_allocator).global_pool
            == pre.spec_index(changed_allocator).global_pool,
        post.spec_index(changed_allocator).cpu_caches.unchanged_except(
            &pre.spec_index(changed_allocator).cpu_caches,
            changed_cpu,
        ),
    ensures
        allocator_4k_invariant_fields_unchanged(pre, post),
{
    assert(allocator_4k_invariant_fields_unchanged(pre, post)) by {
        reveal(allocator_4k_invariant_fields_unchanged);
    };
}

pub proof fn allocator_4k_quota_lock_op_preserves_invariant_fields(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    changed: RwLockPageAllocatorPtr,
)
    requires
        pre.dom() =~= post.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(a_ptr)]
            pre.dom().contains(a_ptr) && a_ptr != changed ==>
                post.spec_index(a_ptr) == pre.spec_index(a_ptr),
        post.spec_index(changed).owning_container
            == pre.spec_index(changed).owning_container,
        post.spec_index(changed).total_free_pages
            == pre.spec_index(changed).total_free_pages,
        post.spec_index(changed).cpu_caches
            == pre.spec_index(changed).cpu_caches,
        post.spec_index(changed).global_pool
            == pre.spec_index(changed).global_pool,
        post.spec_index(changed).quota.view()
            == pre.spec_index(changed).quota.view(),
    ensures
        allocator_4k_invariant_fields_unchanged(pre, post),
{
    reveal(allocator_4k_invariant_fields_unchanged);
}

pub proof fn allocator_4k_global_pool_lock_op_preserves_invariant_fields(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    changed: RwLockPageAllocatorPtr,
)
    requires
        pre.dom() =~= post.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(a_ptr)]
            pre.dom().contains(a_ptr) && a_ptr != changed ==>
                post.spec_index(a_ptr) == pre.spec_index(a_ptr),
        post.spec_index(changed).owning_container
            == pre.spec_index(changed).owning_container,
        post.spec_index(changed).total_free_pages
            == pre.spec_index(changed).total_free_pages,
        post.spec_index(changed).cpu_caches
            == pre.spec_index(changed).cpu_caches,
        post.spec_index(changed).quota
            == pre.spec_index(changed).quota,
        post.spec_index(changed).global_pool.view()
            == pre.spec_index(changed).global_pool.view(),
    ensures
        allocator_4k_invariant_fields_unchanged(pre, post),
{
    reveal(allocator_4k_invariant_fields_unchanged);
}

}

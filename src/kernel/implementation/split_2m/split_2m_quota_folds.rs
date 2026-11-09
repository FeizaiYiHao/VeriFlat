#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn split_allocator_free_page_ptrs_wf_implies_free_count_fold_bounded<const SIZE: usize>(
    allocators: PageAllocatorUnLockedMap<SIZE>, allocator: RwLockPageAllocatorPtr,
)
    requires
        allocator_perms_wf(allocators),
        allocator_free_page_ptrs_wf(allocators),
        allocators.dom().contains(allocator),
    ensures
        allocators.spec_index(allocator).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
        allocators.spec_index(allocator).total_free_pages.view() <= usize::MAX - 512,
{
    assert(allocators.spec_index(allocator).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by {
        allocator_perms_wf_at(allocators, allocator);
        assert(allocators.spec_index(allocator).global_pool.view().len() <= NUM_PAGES * 4096) by {
            reveal(allocator_free_page_ptrs_wf);
            allocators.spec_index(allocator).global_pool.view().linked_list.wf_implies_view_len_eq_len();
            seq_unique_bounded_usize_len(allocators.spec_index(allocator).global_pool.view().view(), (NUM_PAGES * 4096) as usize);
        };
        assert(allocators.spec_index(allocator).cpu_caches.view().fold_left(0int,
            |sum: int, cache: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len()) <= NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by {
            lemma_cache_len_fold_upper_bound(allocators.spec_index(allocator).cpu_caches);
        };
    };
}

}

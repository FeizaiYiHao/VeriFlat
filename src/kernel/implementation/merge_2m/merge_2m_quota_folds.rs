#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn allocator_free_page_ptrs_wf_implies_free_count_fold_bounded<const SIZE: usize>(
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
            cache_inv_implies_cache_len_fold_bounded(allocators.spec_index(allocator).cpu_caches);
        };
    };
}

pub proof fn container_process_allocator_quota_4k_wf_at(
    containers: ContainerLockedMap, processes: ProcessLockedMap, threads: ThreadLockedMap,
    allocators: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, container: RwLockContainerPtr,
)
    requires
        container_process_allocator_quota_4k_wf(containers, processes, threads, allocators),
        containers.dom().contains(container),
    ensures
        process_effective_quota_4k_fold_sum(containers.spec_index(container).view_ghost().owned_processes.view(), processes)
            + thread_effective_quota_4k_fold_sum(containers.spec_index(container).view_ghost().owned_threads.view(), threads)
            + thread_direct_pending_4k_fold_sum(containers.spec_index(container).view_ghost().owned_threads.view(), threads)
            + thread_indirect_pending_4k_fold_sum_at_depth(containers.spec_index(container).view_ghost().owned_indirect_threads.view(), threads, containers.spec_index(container).view_rodata().view().depth as int)
            + allocators.spec_index(containers.spec_index(container).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == allocators.spec_index(containers.spec_index(container).view_rodata().view().allocator_ptr_4k).total_free_pages.view(),
{ reveal(container_process_allocator_quota_4k_wf); }

pub proof fn container_process_allocator_quota_2m_wf_at(
    containers: ContainerLockedMap, processes: ProcessLockedMap, threads: ThreadLockedMap,
    allocators: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, container: RwLockContainerPtr,
)
    requires
        container_process_allocator_quota_2m_wf(containers, processes, threads, allocators),
        containers.dom().contains(container),
    ensures
        process_effective_quota_2m_fold_sum(containers.spec_index(container).view_ghost().owned_processes.view(), processes)
            + thread_effective_quota_2m_fold_sum(containers.spec_index(container).view_ghost().owned_threads.view(), threads)
            + thread_direct_pending_2m_fold_sum(containers.spec_index(container).view_ghost().owned_threads.view(), threads)
            + thread_indirect_pending_2m_fold_sum_at_depth(containers.spec_index(container).view_ghost().owned_indirect_threads.view(), threads, containers.spec_index(container).view_rodata().view().depth as int)
            + allocators.spec_index(containers.spec_index(container).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == allocators.spec_index(containers.spec_index(container).view_rodata().view().allocator_ptr_2m).total_free_pages.view(),
{ reveal(container_process_allocator_quota_2m_wf); }
}

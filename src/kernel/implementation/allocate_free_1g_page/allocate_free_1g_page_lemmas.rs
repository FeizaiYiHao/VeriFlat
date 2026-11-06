use vstd::prelude::*;
use crate::*;

verus! {
/// The first `n` CPU caches of the 1G allocator `allc_ptr` hold no page, so their length fold is zero: 1G pages never enter a CPU cache.
pub(crate) proof fn allocator_1g_cpu_caches_empty_implies_cache_len_fold_zero(k: &KernelK, allc_ptr: RwLockPageAllocatorPtr, n: int)
    requires
        k.inv(),
        k.allc_1g_mp.dom().contains(allc_ptr),
        0 <= n <= NUM_CPUS,
    ensures
        k.allc_1g_mp.spec_index(allc_ptr).cpu_caches.view().take(n).fold_left(0int, |sum: int, cache_lock: LockCell<AllocatorCache<ALLOCATOR_SIZE_1G>, (), (), NO_KILL_STATE>| { sum + cache_lock.view().linked_list.len() }) == 0,
    decreases n,
{
    let caches = k.allc_1g_mp.spec_index(allc_ptr).cpu_caches;
    if n > 0 {
        allocator_1g_cpu_caches_empty_implies_cache_len_fold_zero(k, allc_ptr, n - 1);
        allocator_perms_wf_map(k.allc_1g_mp); allocator_perms_wf_at(k.allc_1g_mp, allc_ptr);
        assert(caches.view().take(n).drop_last() =~= caches.view().take(n - 1));
        caches.view_index_eq_element_value();
        caches.spec_index((n - 1) as usize).view().view().linked_list.wf_implies_view_len_eq_len();
        allocator_1g_cpu_caches_empty_wf_at(k.allc_1g_mp, allc_ptr, (n - 1) as usize);
    }
}

/// A thread of container `ctn_ptr` with 1G quota left proves the global pool of the container's 1G allocator non-empty: the allocator's free pages are its pool pages (its CPU caches are empty) and cover every member of the 1G quota conservation sum.
pub(crate) proof fn thread_effective_quota_1g_positive_implies_global_pool_1g_nonempty(k: &KernelK, ctn_ptr: RwLockContainerPtr, alloc_ptr_1g: RwLockPageAllocatorPtr, thrd_ptr: RwLockThreadPtr)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(ctn_ptr),
        k.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g == alloc_ptr_1g,
        k.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr),
        thread_effective_quota_1g(k.thrd_mp.spec_index(thrd_ptr)) >= 1,
    ensures
        k.allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.view().len() > 0,
{
    let owned_processes = k.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
    let owned_threads = k.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view();
    assert(k.allc_1g_mp.dom().contains(alloc_ptr_1g)) by { container_allocator_wf_at(k.ctn_mp, k.allc_4k_mp, k.allc_2m_mp, k.allc_1g_mp, ctn_ptr); };
    allocator_1g_cpu_caches_empty_implies_cache_len_fold_zero(k, alloc_ptr_1g, NUM_CPUS as int);
    assert(k.allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.view().len() > 0) by {
        allocator_perms_wf_map(k.allc_1g_mp); allocator_perms_wf_at(k.allc_1g_mp, alloc_ptr_1g);
        assert(k.allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.view().take(NUM_CPUS as int) =~= k.allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.view());
        reveal(container_thread_wf); reveal(container_process_allocator_quota_1g_wf); reveal(thread_perms_wf);
        process_effective_quota_1g_nonneg_implies_fold_nonneg(owned_processes, k.prc_mp);
        thread_effective_quota_1g_nonneg_implies_fold_ge_member(owned_threads, k.thrd_mp, thrd_ptr);
        thread_direct_pending_1g_nat_implies_fold_nonneg(owned_threads, k.thrd_mp);
        thread_indirect_pending_1g_nat_implies_fold_nonneg_at_depth(k.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view(), k.thrd_mp, k.ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth as int);
    };
}

/// A free 1G page `pg_idx` on the global list sits, under its free-list node address, in the global pool its state names.
pub(crate) proof fn allocator_free_1g_pages_wf_at(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        allocator_free_1g_pages_wf(allc_1g_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let allc_ptr = page.state->Free1g_allocator_ptr.view();
            (page.state matches PageState::Free1g { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                &&& allc_1g_mp.dom().contains(allc_ptr)
                &&& allc_1g_mp.spec_index(allc_ptr).owning_container == page.owning_container
                &&& allc_1g_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(pg_idx))
                &&& allc_1g_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(page.free_list_node_storage.addr())
                &&& allc_1g_mp.spec_index(allc_ptr).global_pool.view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(pg_idx)
            }
        }),
{ reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); }

/// A page staged in thread `thrd_ptr`'s 1G cache is a valid page owned by that thread.
pub(crate) proof fn thread_staged_1g_pages_wf_at(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr)
    requires
        thread_staged_1g_pages_wf(thrd_mp, pg_arr),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr)
            ==> page_ptr_valid(pg_ptr) && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
{ reveal(thread_staged_1g_pages_wf); }

/// The 1G allocator of a live container exists, its quota is at most its free page count, and that count is bounded.
pub proof fn kernel_inv_implies_container_allocator_1g_quota_bounded(krnl: &KernelK, owner: RwLockContainerPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(owner),
    ensures
        krnl.allc_1g_mp.dom().contains(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g),
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g).quota.view().value <= krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g).total_free_pages.view(),
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g).total_free_pages.view() < usize::MAX,
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
{
    let allc_ptr = krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g;
    let allocator = krnl.allc_1g_mp.spec_index(allc_ptr);
    let threads = krnl.ctn_mp.spec_index(owner).view_ghost().owned_threads.view();
    reveal(container_allocator_wf);
    assert(allocator.quota.view().value <= allocator.total_free_pages.view()) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        process_effective_quota_1g_nonneg_implies_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_processes.view(), krnl.prc_mp);
        let effective = |t: RwLockThreadPtr| thread_effective_quota_1g(krnl.thrd_mp.spec_index(t));
        assert((|sum: int, t: RwLockThreadPtr| sum + effective(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_1g(krnl.thrd_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, effective); };
        thread_direct_pending_1g_nat_implies_fold_nonneg(threads, krnl.thrd_mp);
        thread_indirect_pending_1g_nat_implies_fold_nonneg_at_depth(krnl.ctn_mp.spec_index(owner).view_ghost().owned_indirect_threads.view(), krnl.thrd_mp, krnl.ctn_mp.spec_index(owner).view_rodata().view().depth as int);
    };
    assert(allocator.total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by {
        allocator_perms_wf_at(krnl.allc_1g_mp, allc_ptr);
        reveal(allocator_free_page_ptrs_wf);
        assert(allocator.global_pool.view().len() <= NUM_PAGES * 4096) by {
            reveal(LinkedList::value_list_unique); allocator.global_pool.view().linked_list.wf_implies_view_len_eq_len();
            seq_unique_bounded_usize_len(allocator.global_pool.view().view(), (NUM_PAGES * 4096) as usize);
        };
        assert(allocator.cpu_caches.view().fold_left(0int, |sum: int, cache: LockCell<AllocatorCache<ALLOCATOR_SIZE_1G>, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len()) <= NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by { lemma_cache_len_fold_upper_bound(allocator.cpu_caches); };
    };
}
}

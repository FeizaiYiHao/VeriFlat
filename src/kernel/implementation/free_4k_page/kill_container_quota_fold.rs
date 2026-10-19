use vstd::prelude::*;
use crate::*;

verus! {
/// A container without processes, threads, and indirect threads holds every free page of each of its allocators as
/// quota.
pub proof fn lemma_container_allocator_quota_eq_total_free_without_users(k: KernelK, container_ptr: RwLockContainerPtr)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(container_ptr),
        k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() =~= Set::<RwLockProcessPtr>::empty(),
        k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
        k.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
    ensures
        ({
            let ro = k.ctn_mp.spec_index(container_ptr).view_rodata().view();
            &&& k.allc_4k_mp.dom().contains(ro.allocator_ptr_4k)
            &&& k.allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == k.allc_4k_mp.spec_index(ro.allocator_ptr_4k).total_free_pages.view()
            &&& k.allc_2m_mp.dom().contains(ro.allocator_ptr_2m)
            &&& k.allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == k.allc_2m_mp.spec_index(ro.allocator_ptr_2m).total_free_pages.view()
            &&& k.allc_1g_mp.dom().contains(ro.allocator_ptr_1g)
            &&& k.allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == k.allc_1g_mp.spec_index(ro.allocator_ptr_1g).total_free_pages.view()
        }),
{
    let processes = k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    let depth = k.ctn_mp.spec_index(container_ptr).view_rodata().view().depth as int;
    container_allocator_wf_at(k.ctn_mp, k.allc_4k_mp, k.allc_2m_mp, k.allc_1g_mp, container_ptr);
    lemma_thread_quota_folds_empty(k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view(), k.thr_mp, depth);
    lemma_thread_quota_folds_empty(k.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view(), k.thr_mp, depth);
    let value_4k = |p: RwLockProcessPtr| process_effective_quota_4k(k.prc_mp.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + value_4k(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(k.prc_mp.spec_index(p)))
        && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + value_4k(p)) == 0) by { lemma_set_fold_int_sum_empty(processes, value_4k); };
    let value_2m = |p: RwLockProcessPtr| process_effective_quota_2m(k.prc_mp.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + value_2m(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(k.prc_mp.spec_index(p)))
        && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + value_2m(p)) == 0) by { lemma_set_fold_int_sum_empty(processes, value_2m); };
    let value_1g = |p: RwLockProcessPtr| process_effective_quota_1g(k.prc_mp.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + value_1g(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(k.prc_mp.spec_index(p)))
        && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + value_1g(p)) == 0) by { lemma_set_fold_int_sum_empty(processes, value_1g); };
    reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
}

/// The 2M twin of `lemma_container_allocator_4k_quota_bounded`: a container's 2M quota is within its 2M allocator's free
/// pages, which stay below `usize::MAX`.
pub proof fn lemma_container_allocator_2m_quota_bounded(krnl: &KernelK, owner: RwLockContainerPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(owner),
    ensures
        krnl.allc_2m_mp.dom().contains(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m),
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m).quota.view().value <= krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m).total_free_pages.view(),
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m).total_free_pages.view() < usize::MAX,
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
{
    let allocator_ptr = krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m;
    let allocator = krnl.allc_2m_mp.spec_index(allocator_ptr);
    let threads = krnl.ctn_mp.spec_index(owner).view_ghost().owned_threads.view();
    reveal(container_allocator_wf);
    assert(allocator.quota.view().value <= allocator.total_free_pages.view()) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        lemma_process_effective_quota_2m_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_processes.view(), krnl.prc_mp);
        let effective = |t: RwLockThreadPtr| thread_effective_quota_2m(krnl.thr_mp.spec_index(t));
        assert((|sum: int, t: RwLockThreadPtr| sum + effective(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_2m(krnl.thr_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, effective); };
        lemma_thread_direct_pending_2m_fold_nonneg(threads, krnl.thr_mp);
        lemma_thread_indirect_pending_2m_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_indirect_threads.view(), krnl.thr_mp, krnl.ctn_mp.spec_index(owner).view_rodata().view().depth as int);
    };
    assert(allocator.total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by {
        allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr);
        reveal(allocator_free_page_ptrs_wf);
        assert(allocator.global_pool.view().len() <= NUM_PAGES * 4096) by {
            reveal(LinkedList::value_list_unique); allocator.global_pool.view().linked_list.lemma_len_view();
            seq_unique_bounded_usize_len(allocator.global_pool.view().view(), (NUM_PAGES * 4096) as usize);
        };
        assert(allocator.cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache<ALLOCATOR_SIZE_2M>, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len()) <= NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by { lemma_cache_len_fold_upper_bound(allocator.cpu_caches); };
    };
}
} // verus!

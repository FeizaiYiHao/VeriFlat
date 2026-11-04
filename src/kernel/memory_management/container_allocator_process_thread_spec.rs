use vstd::prelude::*;
use crate::*;

verus! {
/// Each container's 4K, 2M, and 1G quota sums balance against its allocators' free pages.
pub open spec fn container_process_allocator_quota_wf(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>,
    allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>,
) -> bool {
    &&& container_process_allocator_quota_4k_wf(ctn_mp, prc_mp, thrd_mp, allc_4k_mp)
    &&& container_process_allocator_quota_2m_wf(ctn_mp, prc_mp, thrd_mp, allc_2m_mp)
    &&& container_process_allocator_quota_1g_wf(ctn_mp, prc_mp, thrd_mp, allc_1g_mp)
}

pub open spec fn process_effective_quota_4k_fold_sum(owned_processes: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> int {
    owned_processes.fold(0, |sum: int, p: RwLockProcessPtr| {sum + process_effective_quota_4k(prc_mp.spec_index(p))})
}

pub open spec fn process_effective_quota_2m_fold_sum(owned_processes: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> int {
    owned_processes.fold(0, |sum: int, p: RwLockProcessPtr| {sum + process_effective_quota_2m(prc_mp.spec_index(p))})
}

pub open spec fn process_effective_quota_1g_fold_sum(owned_processes: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> int {
    owned_processes.fold(0, |sum: int, p: RwLockProcessPtr| {sum + process_effective_quota_1g(prc_mp.spec_index(p))})
}

pub open spec fn thread_effective_quota_4k_fold_sum(owned_threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap) -> int {
    owned_threads.fold(0, |sum: int, t: RwLockThreadPtr| {sum + thread_effective_quota_4k(thrd_mp.spec_index(t))})
}

pub open spec fn thread_effective_quota_2m_fold_sum(owned_threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap) -> int {
    owned_threads.fold(0, |sum: int, t: RwLockThreadPtr| {sum + thread_effective_quota_2m(thrd_mp.spec_index(t))})
}

pub open spec fn thread_effective_quota_1g_fold_sum(owned_threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap) -> int {
    owned_threads.fold(0, |sum: int, t: RwLockThreadPtr| {sum + thread_effective_quota_1g(thrd_mp.spec_index(t))})
}

pub open spec fn thread_direct_pending_4k_fold_sum(threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap) -> int {
    threads.fold(0, |sum: int, t: RwLockThreadPtr| sum + thrd_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
}

pub open spec fn thread_direct_pending_2m_fold_sum(threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap) -> int {
    threads.fold(0, |sum: int, t: RwLockThreadPtr| sum + thrd_mp.spec_index(t).view().direct_free_quota_pending_2m.view())
}

pub open spec fn thread_direct_pending_1g_fold_sum(threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap) -> int {
    threads.fold(0, |sum: int, t: RwLockThreadPtr| sum + thrd_mp.spec_index(t).view().direct_free_quota_pending_1g.view())
}

pub open spec fn thread_indirect_pending_4k_fold_sum_at_depth(threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap, depth: int) -> int {
    threads.fold(0, |sum: int, t: RwLockThreadPtr| sum + thrd_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth))
}

pub open spec fn thread_indirect_pending_2m_fold_sum_at_depth(threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap, depth: int) -> int {
    threads.fold(0, |sum: int, t: RwLockThreadPtr| sum + thrd_mp.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth))
}

pub open spec fn thread_indirect_pending_1g_fold_sum_at_depth(threads: Set<RwLockThreadPtr>, thrd_mp: ThreadLockedMap, depth: int) -> int {
    threads.fold(0, |sum: int, t: RwLockThreadPtr| sum + thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth))
}

/// For each container, the 4K quota of its processes and threads, plus their pending frees, plus its allocator's own
/// quota equals the allocator's free pages.
// Proof dependencies (confirmed for thread-map preservation): container_thread_wf; global-pool page removal also needs
// container_allocator_wf.
#[verifier::opaque]
pub open spec fn container_process_allocator_quota_4k_wf(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>,
) -> bool {
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k]
        ctn_mp.dom().contains(c)
            ==>
            process_effective_quota_4k_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_processes.view(), prc_mp)
                + thread_effective_quota_4k_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_threads.view(), thrd_mp)
                + thread_direct_pending_4k_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_threads.view(), thrd_mp)
                + thread_indirect_pending_4k_fold_sum_at_depth(ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), thrd_mp, ctn_mp.spec_index(c).view_rodata().view().depth as int)
                + allc_4k_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
                == allc_4k_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
}

/// For each container, the 2M quota of its processes and threads, plus their pending frees, plus its allocator's own
/// quota equals the allocator's free pages.
// Proof dependencies (confirmed for thread-map preservation): container_thread_wf.
#[verifier::opaque]
pub open spec fn container_process_allocator_quota_2m_wf(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
) -> bool {
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m]
        ctn_mp.dom().contains(c)
            ==>
            process_effective_quota_2m_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_processes.view(), prc_mp)
                + thread_effective_quota_2m_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_threads.view(), thrd_mp)
                + thread_direct_pending_2m_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_threads.view(), thrd_mp)
                + thread_indirect_pending_2m_fold_sum_at_depth(ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), thrd_mp, ctn_mp.spec_index(c).view_rodata().view().depth as int)
                + allc_2m_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
                == allc_2m_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
}

/// For each container, the 1G quota of its processes and threads, plus their pending frees, plus its allocator's own
/// quota equals the allocator's free pages.
// Proof dependencies (confirmed for thread-map preservation): container_thread_wf.
#[verifier::opaque]
pub open spec fn container_process_allocator_quota_1g_wf(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>,
) -> bool {
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g]
        ctn_mp.dom().contains(c)
            ==>
            process_effective_quota_1g_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_processes.view(), prc_mp)
                + thread_effective_quota_1g_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_threads.view(), thrd_mp)
                + thread_direct_pending_1g_fold_sum(ctn_mp.spec_index(c).view_ghost().owned_threads.view(), thrd_mp)
                + thread_indirect_pending_1g_fold_sum_at_depth(ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), thrd_mp, ctn_mp.spec_index(c).view_rodata().view().depth as int)
                + allc_1g_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
                == allc_1g_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
}
}

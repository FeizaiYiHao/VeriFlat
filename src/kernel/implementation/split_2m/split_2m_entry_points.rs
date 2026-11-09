#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::merge_2m::{merge_2m_quota_folds::*, merge_2m_entry_points::*, merge_2m_entry_folds::*};

verus! {
pub proof fn thread_quota_4k_implies_split_quota_capacity(krnl: &KernelK,
    thread: RwLockThreadPtr, allocator: RwLockPageAllocatorPtr)
    requires
        krnl.inv(),
        krnl.thrd_mp.dom().contains(thread),
        krnl.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        krnl.allc_4k_mp.dom().contains(allocator),
        krnl.allc_4k_mp.spec_index(allocator).owning_container == krnl.thrd_mp.spec_index(thread).view().owning_container,
    ensures
        krnl.thrd_mp.spec_index(thread).view().quota_4k <= usize::MAX - 512,
        krnl.allc_4k_mp.spec_index(allocator).total_free_pages.view() <= usize::MAX - 512,
{
    let container = krnl.thrd_mp.spec_index(thread).view().owning_container;
    let processes = krnl.ctn_mp.spec_index(container).view_ghost().owned_processes.view();
    let threads = krnl.ctn_mp.spec_index(container).view_ghost().owned_threads.view();
    let indirect = krnl.ctn_mp.spec_index(container).view_ghost().owned_indirect_threads.view();
    let depth = krnl.ctn_mp.spec_index(container).view_rodata().view().depth;
    assert(krnl.allc_4k_mp.spec_index(allocator).total_free_pages.view() <= usize::MAX - 512) by {
        allocator_free_page_ptrs_wf_implies_free_count_fold_bounded(krnl.allc_4k_mp, allocator);
    };
    assert(krnl.thrd_mp.spec_index(thread).view().quota_4k <= krnl.allc_4k_mp.spec_index(allocator).total_free_pages.view()) by {
        reveal(container_thread_wf); reveal(thread_perms_wf); reveal(container_allocator_wf);
        reveal(container_process_allocator_quota_4k_wf);
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator);
        lemma_process_effective_quota_4k_fold_nonneg(processes, krnl.prc_mp);
        lemma_thread_effective_quota_4k_fold_ge_member(threads, krnl.thrd_mp, thread);
        lemma_thread_direct_pending_4k_fold_nonneg(threads, krnl.thrd_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(indirect, krnl.thrd_mp, depth as int);
    };
}

pub proof fn thread_quota_2m_implies_allocator_free_count_positive(krnl: &KernelK,
    thread: RwLockThreadPtr, allocator: RwLockPageAllocatorPtr)
    requires
        krnl.inv(),
        krnl.thrd_mp.dom().contains(thread),
        krnl.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        krnl.thrd_mp.spec_index(thread).view().quota_2m > 0,
        krnl.allc_2m_mp.dom().contains(allocator),
        krnl.allc_2m_mp.spec_index(allocator).owning_container == krnl.thrd_mp.spec_index(thread).view().owning_container,
    ensures
        krnl.allc_2m_mp.spec_index(allocator).total_free_pages.view() >= krnl.thrd_mp.spec_index(thread).view().quota_2m,
        krnl.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0,
{
    let container = krnl.thrd_mp.spec_index(thread).view().owning_container;
    container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thread);
    container_allocator_2m_forward_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, allocator);
    container_process_allocator_quota_2m_wf_at(krnl.ctn_mp, krnl.prc_mp, krnl.thrd_mp, krnl.allc_2m_mp, container);
    container_thread_and_perms_wf_implies_2m_fold_sum_ge_thread_quota(krnl.ctn_mp, krnl.prc_mp, krnl.thrd_mp, container, thread);
}
}

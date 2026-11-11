#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn container_thread_and_perms_wf_implies_2m_fold_sum_ge_thread_quota(
    containers: ContainerLockedMap, processes: ProcessLockedMap, threads: ThreadLockedMap,
    container: RwLockContainerPtr, thread: RwLockThreadPtr,
)
    requires
        container_thread_wf(containers, threads),
        thread_perms_wf(threads),
        containers.dom().contains(container),
        containers.spec_index(container).view_ghost().owned_threads.view().contains(thread),
        threads.dom().contains(thread),
        threads.spec_index(thread).view().temp_alloc_clean(),
    ensures
        ({
            let owned_processes = containers.spec_index(container).view_ghost().owned_processes.view();
            let owned_threads = containers.spec_index(container).view_ghost().owned_threads.view();
            let indirect_threads = containers.spec_index(container).view_ghost().owned_indirect_threads.view();
            let depth = containers.spec_index(container).view_rodata().view().depth;
            &&& process_effective_quota_2m_fold_sum(owned_processes, processes) + thread_effective_quota_2m_fold_sum(owned_threads, threads)
                + thread_direct_pending_2m_fold_sum(owned_threads, threads) + thread_indirect_pending_2m_fold_sum_at_depth(indirect_threads, threads, depth as int)
                >= threads.spec_index(thread).view().quota_2m
        }),
{
    let owned_processes = containers.spec_index(container).view_ghost().owned_processes.view();
    let owned_threads = containers.spec_index(container).view_ghost().owned_threads.view();
    let indirect_threads = containers.spec_index(container).view_ghost().owned_indirect_threads.view();
    let depth = containers.spec_index(container).view_rodata().view().depth;
    assert(process_effective_quota_2m_fold_sum(owned_processes, processes) + thread_effective_quota_2m_fold_sum(owned_threads, threads)
        + thread_direct_pending_2m_fold_sum(owned_threads, threads) + thread_indirect_pending_2m_fold_sum_at_depth(indirect_threads, threads, depth as int)
        >= threads.spec_index(thread).view().quota_2m) by {
        reveal(container_thread_wf); reveal(thread_perms_wf);
        nonneg_members_implies_process_effective_quota_2m_fold_sum_nonneg(owned_processes, processes);
        nonneg_members_implies_thread_effective_quota_2m_fold_sum_ge_member(owned_threads, threads, thread);
        thread_direct_pending_2m_fold_sum_implies_nonneg(owned_threads, threads);
        thread_indirect_pending_2m_fold_sum_at_depth_implies_nonneg(indirect_threads, threads, depth as int);
    };
}
}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Kernel invariants read thread payloads, not the current thread lock owner.
pub open spec fn thread_invariant_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger pre.spec_index(t_ptr)]
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
            post.spec_index(t_ptr).view()
                == pre.spec_index(t_ptr).view()
}

/// Thread fields read by the 4K conservation law.
pub open spec fn thread_quota_4k_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger pre.spec_index(t_ptr)]
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
            thread_effective_quota_4k(post.spec_index(t_ptr))
                == thread_effective_quota_4k(pre.spec_index(t_ptr))
            && post.spec_index(t_ptr).view().direct_free_quota_pending_4k
                == pre.spec_index(t_ptr).view().direct_free_quota_pending_4k
            && post.spec_index(t_ptr).view().indirect_free_quota_pending_4k
                == pre.spec_index(t_ptr).view().indirect_free_quota_pending_4k
}

/// Thread fields read by the 2M conservation law. Changes to unrelated
/// fields (for example the 4K staging cache) are deliberately excluded.
pub open spec fn thread_quota_2m_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger pre.spec_index(t_ptr)]
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
            thread_effective_quota_2m(post.spec_index(t_ptr))
                == thread_effective_quota_2m(pre.spec_index(t_ptr))
            && post.spec_index(t_ptr).view().direct_free_quota_pending_2m
                == pre.spec_index(t_ptr).view().direct_free_quota_pending_2m
            && post.spec_index(t_ptr).view().indirect_free_quota_pending_2m
                == pre.spec_index(t_ptr).view().indirect_free_quota_pending_2m
}

/// Thread fields read by the 1G conservation law.
pub open spec fn thread_quota_1g_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger pre.spec_index(t_ptr)]
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
            thread_effective_quota_1g(post.spec_index(t_ptr))
                == thread_effective_quota_1g(pre.spec_index(t_ptr))
            && post.spec_index(t_ptr).view().direct_free_quota_pending_1g
                == pre.spec_index(t_ptr).view().direct_free_quota_pending_1g
            && post.spec_index(t_ptr).view().indirect_free_quota_pending_1g
                == pre.spec_index(t_ptr).view().indirect_free_quota_pending_1g
}

pub proof fn thread_lock_op_preserves_invariant_fields(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    changed: RwLockThreadPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
    ensures
        thread_invariant_fields_unchanged(pre, post),
{
}

/// Every non-thread kernel field is framed by a thread lock operation.
pub open spec fn thread_lock_kernel_context_unchanged(
    pre: KernelK,
    post: KernelK,
) -> bool {
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.irt == pre.irt
    &&& post.pg_arr == pre.pg_arr
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.sched_mp == pre.sched_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.prc_mp == pre.prc_mp
    &&& post.ep_mp == pre.ep_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
}

/// Memory preservation needs the source container/thread ownership leaf, not
/// the unrelated remainder of process-management state.
pub proof fn thread_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_thread_wf(pre.ctn_mp, pre.thr_mp),
        thread_invariant_fields_unchanged(pre.thr_mp, post.thr_mp),
        thread_lock_kernel_context_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(container_process_allocator_quota_4k_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_4k_mp,
    )) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_fields(
            post.ctn_mp,
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
            post.allc_4k_mp,
        );
    };
    assert(container_process_allocator_quota_2m_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_2m_mp,
    )) by {
        container_process_allocator_quota_2m_wf_preserved_for_thread_fields(
            post.ctn_mp,
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
            post.allc_2m_mp,
        );
    };
    assert(container_process_allocator_quota_1g_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_1g_mp,
    )) by {
        container_process_allocator_quota_1g_wf_preserved_for_thread_fields(
            post.ctn_mp,
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
            post.allc_1g_mp,
        );
    };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_pages_wf);
    };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        lemma_no_change_imply_thread_staged_pages_wf_forall();
    };
}

pub proof fn thread_no_change_imply_process_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.process_management_inv(),
        thread_invariant_fields_unchanged(pre.thr_mp, post.thr_mp),
        thread_lock_kernel_context_unchanged(pre, post),
    ensures
        post.process_management_inv(),
{
    thread_invariant_fields_unchanged_implies_process_management_fields(
        pre.thr_mp,
        post.thr_mp,
    );
    assert(thread_caller_callee_wf(post.thr_mp)) by {
        thread_caller_callee_wf_preserved_for_thread_process_management_fields(
            pre.thr_mp,
            post.thr_mp,
        );
    };
    assert(thread_endpoint_ref_counter_wf(
        post.thr_mp,
        post.ep_mp,
    )) by {
        thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(
            pre.thr_mp,
            post.thr_mp,
            post.ep_mp,
        );
    };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by {
        thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(
            pre.thr_mp,
            post.thr_mp,
            post.ep_mp,
        );
    };
    assert(container_thread_endpoint_wf(
        post.ctn_mp,
        post.thr_mp,
        post.ep_mp,
    )) by {
        container_thread_endpoint_wf_preserved_for_thread_process_management_fields(
            post.ctn_mp,
            pre.thr_mp,
            post.thr_mp,
            post.ep_mp,
        );
    };
    assert(container_thread_scheduler_wf(
        post.ctn_mp,
        post.thr_mp,
        post.sched_mp,
    )) by {
        container_thread_scheduler_wf_preserved_for_thread_process_management_fields(
            post.ctn_mp,
            pre.thr_mp,
            post.thr_mp,
            post.sched_mp,
        );
    };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by {
        container_thread_wf_preserved_for_thread_process_management_fields(
            post.ctn_mp,
            pre.thr_mp,
            post.thr_mp,
        );
    };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        process_thread_wf_preserved_for_thread_process_management_fields(
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
        );
    };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by {
        thread_cpu_wf_preserved_for_thread_process_management_fields(
            pre.thr_mp,
            post.thr_mp,
            post.cpu_arr,
        );
    };
}

pub proof fn container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    allocator_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_4k_wf(
            container_map,
            process_map,
            pre_thread_map,
            allocator_map,
        ),
        container_thread_wf(container_map, pre_thread_map),
        thread_quota_4k_fields_unchanged(pre_thread_map, post_thread_map),
    ensures
        container_process_allocator_quota_4k_wf(
            container_map,
            process_map,
            post_thread_map,
            allocator_map,
        ),
{
    assert(container_process_allocator_quota_4k_wf(
        container_map,
        process_map,
        post_thread_map,
        allocator_map,
    )) by {
        reveal(container_process_allocator_quota_4k_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr)
                .view_rodata().view().allocator_ptr_4k]
            container_map.dom().contains(c_ptr)
        implies
        {
            &&& thread_effective_quota_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
                    post_thread_map,
                )
                == thread_effective_quota_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
                    pre_thread_map,
                )
            &&& thread_direct_pending_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost()
                        .owned_threads.view(),
                    post_thread_map,
                )
                == thread_direct_pending_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost()
                        .owned_threads.view(),
                    pre_thread_map,
                )
            &&& thread_indirect_pending_4k_fold_sum_at_depth(
                    container_map.spec_index(c_ptr).view_ghost()
                        .owned_indirect_threads.view(),
                    post_thread_map,
                    container_map.spec_index(c_ptr).view_rodata().view().depth as int,
                )
                == thread_indirect_pending_4k_fold_sum_at_depth(
                    container_map.spec_index(c_ptr).view_ghost()
                        .owned_indirect_threads.view(),
                    pre_thread_map,
                    container_map.spec_index(c_ptr).view_rodata().view().depth as int,
                )
        }
    by {
        assert(container_map.spec_index(c_ptr).view_ghost().owned_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        assert(container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_4k_fold_eq(
            container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_effective_quota_4k_fold_eq(
            container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_4k_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_indirect_threads.view(),
            pre_thread_map,
            post_thread_map,
            container_map.spec_index(c_ptr).view_rodata().view().depth as int,
        );
        };
    };
}

pub proof fn container_process_allocator_quota_4k_wf_preserved_for_thread_fields(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    allocator_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_4k_wf(
            container_map,
            process_map,
            pre_thread_map,
            allocator_map,
        ),
        container_thread_wf(container_map, pre_thread_map),
        thread_invariant_fields_unchanged(
            pre_thread_map,
            post_thread_map,
        ),
    ensures
        container_process_allocator_quota_4k_wf(
            container_map,
            process_map,
            post_thread_map,
            allocator_map,
        ),
{
    assert(container_process_allocator_quota_4k_wf(
        container_map,
        process_map,
        post_thread_map,
        allocator_map,
    )) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
            container_map,
            process_map,
            pre_thread_map,
            post_thread_map,
            allocator_map,
        );
    };
}

pub proof fn container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    allocator_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_2m_wf(
            container_map,
            process_map,
            pre_thread_map,
            allocator_map,
        ),
        container_thread_wf(container_map, pre_thread_map),
        thread_quota_2m_fields_unchanged(
            pre_thread_map,
            post_thread_map,
        ),
    ensures
        container_process_allocator_quota_2m_wf(
            container_map,
            process_map,
            post_thread_map,
            allocator_map,
        ),
{
    assert(container_process_allocator_quota_2m_wf(
        container_map,
        process_map,
        post_thread_map,
        allocator_map,
    )) by {
        reveal(container_process_allocator_quota_2m_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr)
                .view_rodata().view().allocator_ptr_2m]
            container_map.dom().contains(c_ptr)
        implies
        {
            &&& thread_effective_quota_2m_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
                    post_thread_map,
                )
                == thread_effective_quota_2m_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
                    pre_thread_map,
                )
            &&& container_map.spec_index(c_ptr).view_ghost()
                .owned_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .direct_free_quota_pending_2m.view(),
                )
                == container_map.spec_index(c_ptr).view_ghost()
                    .owned_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .direct_free_quota_pending_2m.view(),
                    )
            &&& container_map.spec_index(c_ptr).view_ghost()
                .owned_indirect_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .indirect_free_quota_pending_2m.view().spec_index(
                                container_map.spec_index(c_ptr)
                                    .view_rodata().view().depth as int,
                            ),
                )
                == container_map.spec_index(c_ptr).view_ghost()
                    .owned_indirect_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .indirect_free_quota_pending_2m.view().spec_index(
                                    container_map.spec_index(c_ptr)
                                        .view_rodata().view().depth as int,
                                ),
                    )
        }
    by {
        assert(container_map.spec_index(c_ptr).view_ghost().owned_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        assert(container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_2m_fold_eq(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_effective_quota_2m_fold_eq(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_2m_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_indirect_threads.view(),
            pre_thread_map,
            post_thread_map,
            container_map.spec_index(c_ptr)
                .view_rodata().view().depth as int,
        );
        };
    };
}

pub proof fn container_process_allocator_quota_2m_wf_preserved_for_thread_fields(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    allocator_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_2m_wf(
            container_map,
            process_map,
            pre_thread_map,
            allocator_map,
        ),
        container_thread_wf(container_map, pre_thread_map),
        thread_invariant_fields_unchanged(pre_thread_map, post_thread_map),
    ensures
        container_process_allocator_quota_2m_wf(
            container_map,
            process_map,
            post_thread_map,
            allocator_map,
        ),
{
    assert(container_process_allocator_quota_2m_wf(
        container_map,
        process_map,
        post_thread_map,
        allocator_map,
    )) by {
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
            container_map,
            process_map,
            pre_thread_map,
            post_thread_map,
            allocator_map,
        );
    };
}

pub proof fn container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    allocator_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_1g_wf(
            container_map,
            process_map,
            pre_thread_map,
            allocator_map,
        ),
        container_thread_wf(container_map, pre_thread_map),
        thread_quota_1g_fields_unchanged(
            pre_thread_map,
            post_thread_map,
        ),
    ensures
        container_process_allocator_quota_1g_wf(
            container_map,
            process_map,
            post_thread_map,
            allocator_map,
        ),
{
    assert(container_process_allocator_quota_1g_wf(
        container_map,
        process_map,
        post_thread_map,
        allocator_map,
    )) by {
        reveal(container_process_allocator_quota_1g_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr)
                .view_rodata().view().allocator_ptr_1g]
            container_map.dom().contains(c_ptr)
        implies
        {
            &&& thread_effective_quota_1g_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
                    post_thread_map,
                )
                == thread_effective_quota_1g_fold_sum(
                    container_map.spec_index(c_ptr).view_ghost().owned_threads.view(),
                    pre_thread_map,
                )
            &&& container_map.spec_index(c_ptr).view_ghost()
                .owned_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .direct_free_quota_pending_1g.view(),
                )
                == container_map.spec_index(c_ptr).view_ghost()
                    .owned_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .direct_free_quota_pending_1g.view(),
                    )
            &&& container_map.spec_index(c_ptr).view_ghost()
                .owned_indirect_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .indirect_free_quota_pending_1g.view().spec_index(
                                container_map.spec_index(c_ptr)
                                    .view_rodata().view().depth as int,
                            ),
                )
                == container_map.spec_index(c_ptr).view_ghost()
                    .owned_indirect_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .indirect_free_quota_pending_1g.view().spec_index(
                                    container_map.spec_index(c_ptr)
                                        .view_rodata().view().depth as int,
                                ),
                    )
        }
    by {
        assert(container_map.spec_index(c_ptr).view_ghost().owned_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        assert(container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_1g_fold_eq(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_effective_quota_1g_fold_eq(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_1g_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_ghost()
                .owned_indirect_threads.view(),
            pre_thread_map,
            post_thread_map,
            container_map.spec_index(c_ptr)
                .view_rodata().view().depth as int,
        );
        };
    };
}

pub proof fn container_process_allocator_quota_1g_wf_preserved_for_thread_fields(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    allocator_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_1g_wf(
            container_map,
            process_map,
            pre_thread_map,
            allocator_map,
        ),
        container_thread_wf(container_map, pre_thread_map),
        thread_invariant_fields_unchanged(pre_thread_map, post_thread_map),
    ensures
        container_process_allocator_quota_1g_wf(
            container_map,
            process_map,
            post_thread_map,
            allocator_map,
        ),
{
    assert(container_process_allocator_quota_1g_wf(
        container_map,
        process_map,
        post_thread_map,
        allocator_map,
    )) by {
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
            container_map,
            process_map,
            pre_thread_map,
            post_thread_map,
            allocator_map,
        );
    };
}

}

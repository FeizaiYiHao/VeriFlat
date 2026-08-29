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
    &&& post.pagetable_map == pre.pagetable_map
    &&& post.iommu_table_map == pre.iommu_table_map
    &&& post.iommu_root_table == pre.iommu_root_table
    &&& post.page_array == pre.page_array
    &&& post.cpu_array == pre.cpu_array
    &&& post.container_map == pre.container_map
    &&& post.scheduler_map == pre.scheduler_map
    &&& post.pcid_allocator_map == pre.pcid_allocator_map
    &&& post.process_map == pre.process_map
    &&& post.endpoint_map == pre.endpoint_map
    &&& post.allocator_4k_map == pre.allocator_4k_map
    &&& post.allocator_2m_map == pre.allocator_2m_map
    &&& post.allocator_1g_map == pre.allocator_1g_map
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.root_container == pre.root_container
    &&& post.default_pagetable == pre.default_pagetable
}

/// Memory preservation needs the source container/thread ownership leaf, not
/// the unrelated remainder of process-management state.
pub proof fn thread_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_thread_wf(pre.container_map, pre.thread_map),
        thread_invariant_fields_unchanged(pre.thread_map, post.thread_map),
        thread_lock_kernel_context_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(container_process_allocator_quota_4k_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_4k_map,
    )) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_fields(
            post.container_map,
            post.process_map,
            pre.thread_map,
            post.thread_map,
            post.allocator_4k_map,
        );
    };
    assert(container_process_allocator_quota_2m_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_2m_map,
    )) by {
        container_process_allocator_quota_2m_wf_preserved_for_thread_fields(
            post.container_map,
            post.process_map,
            pre.thread_map,
            post.thread_map,
            post.allocator_2m_map,
        );
    };
    assert(container_process_allocator_quota_1g_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_1g_map,
    )) by {
        container_process_allocator_quota_1g_wf_preserved_for_thread_fields(
            post.container_map,
            post.process_map,
            pre.thread_map,
            post.thread_map,
            post.allocator_1g_map,
        );
    };
    assert(thread_pages_wf(post.thread_map, post.page_array)) by {
        reveal(thread_pages_wf);
    };
    assert(thread_staged_pages_wf(post.thread_map, post.page_array)) by {
        lemma_no_change_imply_thread_staged_pages_wf_forall();
    };
}

pub proof fn thread_no_change_imply_process_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.process_management_inv(),
        thread_invariant_fields_unchanged(pre.thread_map, post.thread_map),
        thread_lock_kernel_context_unchanged(pre, post),
    ensures
        post.process_management_inv(),
{
    thread_invariant_fields_unchanged_implies_process_management_fields(
        pre.thread_map,
        post.thread_map,
    );
    assert(thread_caller_callee_wf(post.thread_map)) by {
        thread_caller_callee_wf_preserved_for_thread_process_management_fields(
            pre.thread_map,
            post.thread_map,
        );
    };
    assert(thread_endpoint_ref_counter_wf(
        post.thread_map,
        post.endpoint_map,
    )) by {
        thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(
            pre.thread_map,
            post.thread_map,
            post.endpoint_map,
        );
    };
    assert(thread_endpoint_queue_wf(post.thread_map, post.endpoint_map)) by {
        thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(
            pre.thread_map,
            post.thread_map,
            post.endpoint_map,
        );
    };
    assert(container_thread_endpoint_wf(
        post.container_map,
        post.thread_map,
        post.endpoint_map,
    )) by {
        container_thread_endpoint_wf_preserved_for_thread_process_management_fields(
            post.container_map,
            pre.thread_map,
            post.thread_map,
            post.endpoint_map,
        );
    };
    assert(container_thread_scheduler_wf(
        post.container_map,
        post.thread_map,
        post.scheduler_map,
    )) by {
        container_thread_scheduler_wf_preserved_for_thread_process_management_fields(
            post.container_map,
            pre.thread_map,
            post.thread_map,
            post.scheduler_map,
        );
    };
    assert(container_thread_wf(post.container_map, post.thread_map)) by {
        container_thread_wf_preserved_for_thread_process_management_fields(
            post.container_map,
            pre.thread_map,
            post.thread_map,
        );
    };
    assert(process_thread_wf(post.process_map, post.thread_map)) by {
        process_thread_wf_preserved_for_thread_process_management_fields(
            post.process_map,
            pre.thread_map,
            post.thread_map,
        );
    };
    assert(thread_cpu_wf(post.thread_map, post.cpu_array)) by {
        thread_cpu_wf_preserved_for_thread_process_management_fields(
            pre.thread_map,
            post.thread_map,
            post.cpu_array,
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
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    post_thread_map,
                )
                == thread_effective_quota_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    pre_thread_map,
                )
            &&& thread_direct_pending_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost()
                        .owned_threads.view(),
                    post_thread_map,
                )
                == thread_direct_pending_4k_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost()
                        .owned_threads.view(),
                    pre_thread_map,
                )
            &&& thread_indirect_pending_4k_fold_sum_at_depth(
                    container_map.spec_index(c_ptr).view_kernel_ghost()
                        .owned_indirect_threads.view(),
                    post_thread_map,
                    container_map.spec_index(c_ptr).view_rodata().view().depth as int,
                )
                == thread_indirect_pending_4k_fold_sum_at_depth(
                    container_map.spec_index(c_ptr).view_kernel_ghost()
                        .owned_indirect_threads.view(),
                    pre_thread_map,
                    container_map.spec_index(c_ptr).view_rodata().view().depth as int,
                )
        }
    by {
        assert(container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        assert(container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_4k_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_effective_quota_4k_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_4k_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_kernel_ghost()
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
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    post_thread_map,
                )
                == thread_effective_quota_2m_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    pre_thread_map,
                )
            &&& container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .direct_free_quota_pending_2m.view(),
                )
                == container_map.spec_index(c_ptr).view_user_ghost()
                    .owned_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .direct_free_quota_pending_2m.view(),
                    )
            &&& container_map.spec_index(c_ptr).view_kernel_ghost()
                .owned_indirect_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .indirect_free_quota_pending_2m.view().spec_index(
                                container_map.spec_index(c_ptr)
                                    .view_rodata().view().depth as int,
                            ),
                )
                == container_map.spec_index(c_ptr).view_kernel_ghost()
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
        assert(container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        assert(container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_2m_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_effective_quota_2m_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_2m_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_kernel_ghost()
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
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    post_thread_map,
                )
                == thread_effective_quota_1g_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    pre_thread_map,
                )
            &&& container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .direct_free_quota_pending_1g.view(),
                )
                == container_map.spec_index(c_ptr).view_user_ghost()
                    .owned_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .direct_free_quota_pending_1g.view(),
                    )
            &&& container_map.spec_index(c_ptr).view_kernel_ghost()
                .owned_indirect_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .indirect_free_quota_pending_1g.view().spec_index(
                                container_map.spec_index(c_ptr)
                                    .view_rodata().view().depth as int,
                            ),
                )
                == container_map.spec_index(c_ptr).view_kernel_ghost()
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
        assert(container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        assert(container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().subset_of(pre_thread_map.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_1g_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_effective_quota_1g_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_1g_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_kernel_ghost()
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

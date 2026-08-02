use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Kernel invariants read thread payloads, not the current thread lock owner.
#[verifier::opaque]
pub open spec fn thread_invariant_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
            post.spec_index(t_ptr).view()
                == pre.spec_index(t_ptr).view()
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
    reveal(thread_invariant_fields_unchanged);
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
    reveal(thread_invariant_fields_unchanged);
    reveal(container_process_allocator_quota_4k_wf);
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.spec_index(c_ptr)
            .view_rodata().view().allocator_ptr_4k]
        container_map.dom().contains(c_ptr)
    implies
        {
            &&& container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .direct_free_quota_pending_4k.view(),
                )
                == container_map.spec_index(c_ptr).view_user_ghost()
                    .owned_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .direct_free_quota_pending_4k.view(),
                    )
            &&& container_map.spec_index(c_ptr).view_kernel_ghost()
                .owned_indirect_threads.view().fold(
                    0,
                    |sum: int, t_ptr: RwLockThreadPtr|
                        sum + post_thread_map.spec_index(t_ptr).view()
                            .indirect_free_quota_pending_4k.view().spec_index(
                                container_map.spec_index(c_ptr)
                                    .view_rodata().view().depth as int,
                            ),
                )
                == container_map.spec_index(c_ptr).view_kernel_ghost()
                    .owned_indirect_threads.view().fold(
                        0,
                        |sum: int, t_ptr: RwLockThreadPtr|
                            sum + pre_thread_map.spec_index(t_ptr).view()
                                .indirect_free_quota_pending_4k.view().spec_index(
                                    container_map.spec_index(c_ptr)
                                        .view_rodata().view().depth as int,
                                ),
                    )
        }
    by {
        assert(container_map.spec_index(c_ptr).view_user_ghost()
            .owned_threads.view().subset_of(pre_thread_map.dom())) by {
            reveal(container_thread_wf);
        };
        assert(container_map.spec_index(c_ptr).view_kernel_ghost()
            .owned_indirect_threads.view().subset_of(
                pre_thread_map.dom(),
            )) by {
            reveal(container_thread_wf);
        };
        lemma_thread_direct_pending_4k_fold_eq(
            container_map.spec_index(c_ptr).view_user_ghost()
                .owned_threads.view(),
            pre_thread_map,
            post_thread_map,
        );
        lemma_thread_indirect_pending_4k_fold_eq_at_depth(
            container_map.spec_index(c_ptr).view_kernel_ghost()
                .owned_indirect_threads.view(),
            pre_thread_map,
            post_thread_map,
            container_map.spec_index(c_ptr)
                .view_rodata().view().depth as int,
        );
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
        thread_invariant_fields_unchanged(
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
    reveal(thread_invariant_fields_unchanged);
    reveal(container_process_allocator_quota_2m_wf);
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.spec_index(c_ptr)
            .view_rodata().view().allocator_ptr_2m]
        container_map.dom().contains(c_ptr)
    implies
        {
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
        assert(container_map.spec_index(c_ptr).view_user_ghost()
            .owned_threads.view().subset_of(pre_thread_map.dom())) by {
            reveal(container_thread_wf);
        };
        assert(container_map.spec_index(c_ptr).view_kernel_ghost()
            .owned_indirect_threads.view().subset_of(
                pre_thread_map.dom(),
            )) by {
            reveal(container_thread_wf);
        };
        lemma_thread_direct_pending_2m_fold_eq(
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
        thread_invariant_fields_unchanged(
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
    reveal(thread_invariant_fields_unchanged);
    reveal(container_process_allocator_quota_1g_wf);
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.spec_index(c_ptr)
            .view_rodata().view().allocator_ptr_1g]
        container_map.dom().contains(c_ptr)
    implies
        {
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
        assert(container_map.spec_index(c_ptr).view_user_ghost()
            .owned_threads.view().subset_of(pre_thread_map.dom())) by {
            reveal(container_thread_wf);
        };
        assert(container_map.spec_index(c_ptr).view_kernel_ghost()
            .owned_indirect_threads.view().subset_of(
                pre_thread_map.dom(),
            )) by {
            reveal(container_thread_wf);
        };
        lemma_thread_direct_pending_1g_fold_eq(
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
}

}

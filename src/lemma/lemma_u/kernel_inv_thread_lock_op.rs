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

pub proof fn kernel_inv_preserved_for_thread_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.inv(),
        thread_perms_wf(post.thread_map),
        thread_invariant_fields_unchanged(
            pre.thread_map,
            post.thread_map,
        ),
        post.pagetable_map == pre.pagetable_map,
        post.iommu_table_map == pre.iommu_table_map,
        post.iommu_root_table == pre.iommu_root_table,
        post.page_array == pre.page_array,
        post.cpu_array == pre.cpu_array,
        post.cpu_tlb == pre.cpu_tlb,
        post.iommu_tlb == pre.iommu_tlb,
        post.root_container == pre.root_container,
        post.container_map == pre.container_map,
        post.scheduler_map == pre.scheduler_map,
        post.pcid_allocator_map == pre.pcid_allocator_map,
        post.process_map == pre.process_map,
        post.endpoint_map == pre.endpoint_map,
        post.allocator_4k_map == pre.allocator_4k_map,
        post.allocator_2m_map == pre.allocator_2m_map,
        post.allocator_1g_map == pre.allocator_1g_map,
        post.default_pagetable == pre.default_pagetable,
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by {
        assert(container_process_allocator_quota_4k_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_4k_map,
        )) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_fields(
                pre.container_map,
                pre.process_map,
                pre.thread_map,
                post.thread_map,
                pre.allocator_4k_map,
            );
        };
        assert(container_process_allocator_quota_2m_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_2m_map,
        )) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_fields(
                pre.container_map,
                pre.process_map,
                pre.thread_map,
                post.thread_map,
                pre.allocator_2m_map,
            );
        };
        assert(container_process_allocator_quota_1g_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_1g_map,
        )) by {
            container_process_allocator_quota_1g_wf_preserved_for_thread_fields(
                pre.container_map,
                pre.process_map,
                pre.thread_map,
                post.thread_map,
                pre.allocator_1g_map,
            );
        };
        assert(thread_pages_wf(
            post.thread_map,
            post.page_array,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(thread_pages_wf);
        };
    };
    assert(post.process_management_inv()) by {
        assert(thread_endpoint_ref_counter_wf(
            post.thread_map,
            post.endpoint_map,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(thread_endpoint_queue_wf(
            post.thread_map,
            post.endpoint_map,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(thread_endpoint_queue_wf);
        };
        assert(container_thread_endpoint_wf(
            post.container_map,
            post.thread_map,
            post.endpoint_map,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(container_endpoint_wf);
            reveal(thread_endpoint_ref_counter_wf);
            reveal(thread_endpoint_queue_wf);
            reveal(container_thread_endpoint_wf);
        };
        assert(container_thread_scheduler_wf(
            post.container_map,
            post.thread_map,
            post.scheduler_map,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(container_thread_wf);
            reveal(container_scheduler_wf);
            reveal(container_thread_scheduler_wf);
        };
        assert(container_thread_wf(
            post.container_map,
            post.thread_map,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(container_thread_wf);
        };
        assert(process_thread_wf(
            post.process_map,
            post.thread_map,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(process_thread_wf);
        };
        assert(thread_cpu_wf(
            post.thread_map,
            post.cpu_array,
        )) by {
            reveal(thread_invariant_fields_unchanged);
            reveal(thread_cpu_wf);
        };
    };
    assert(post.inv()) by {
        reveal(KernelK::inv);
    };
}

pub proof fn lemma_no_change_imply_kernel_inv_for_thread_lock_op_forall()
    ensures
        forall|pre: KernelK, post: KernelK, changed: RwLockThreadPtr|
            #![trigger
                pre.inv(),
                post.inv(),
                post.thread_map.unchanged_except(
                    &pre.thread_map,
                    changed,
                )
            ]
            pre.inv()
            && pre.thread_map.dom().contains(changed)
            && post.thread_map.perms_wf()
            && post.thread_map.unchanged_except(&pre.thread_map, changed)
            && post.thread_map.spec_index(changed).inv()
            && post.thread_map.spec_index(changed).view()
                == pre.thread_map.spec_index(changed).view()
            && (!(post.thread_map.spec_index(changed).locking_thread() is Write)
                ==> post.thread_map.spec_index(changed).view()
                    .free_quota_pending_clean())
            && post.pagetable_map == pre.pagetable_map
            && post.iommu_table_map == pre.iommu_table_map
            && post.iommu_root_table == pre.iommu_root_table
            && post.page_array == pre.page_array
            && post.cpu_array == pre.cpu_array
            && post.cpu_tlb == pre.cpu_tlb
            && post.iommu_tlb == pre.iommu_tlb
            && post.root_container == pre.root_container
            && post.container_map == pre.container_map
            && post.scheduler_map == pre.scheduler_map
            && post.pcid_allocator_map == pre.pcid_allocator_map
            && post.process_map == pre.process_map
            && post.endpoint_map == pre.endpoint_map
            && post.allocator_4k_map == pre.allocator_4k_map
            && post.allocator_2m_map == pre.allocator_2m_map
            && post.allocator_1g_map == pre.allocator_1g_map
            && post.default_pagetable == pre.default_pagetable
            ==> post.inv(),
{
    assert forall|pre: KernelK, post: KernelK, changed: RwLockThreadPtr| #![auto]
        pre.inv()
        && pre.thread_map.dom().contains(changed)
        && post.thread_map.perms_wf()
        && post.thread_map.unchanged_except(&pre.thread_map, changed)
        && post.thread_map.spec_index(changed).inv()
        && post.thread_map.spec_index(changed).view()
            == pre.thread_map.spec_index(changed).view()
        && (!(post.thread_map.spec_index(changed).locking_thread() is Write)
            ==> post.thread_map.spec_index(changed).view()
                .free_quota_pending_clean())
        && post.pagetable_map == pre.pagetable_map
        && post.iommu_table_map == pre.iommu_table_map
        && post.iommu_root_table == pre.iommu_root_table
        && post.page_array == pre.page_array
        && post.cpu_array == pre.cpu_array
        && post.cpu_tlb == pre.cpu_tlb
        && post.iommu_tlb == pre.iommu_tlb
        && post.root_container == pre.root_container
        && post.container_map == pre.container_map
        && post.scheduler_map == pre.scheduler_map
        && post.pcid_allocator_map == pre.pcid_allocator_map
        && post.process_map == pre.process_map
        && post.endpoint_map == pre.endpoint_map
        && post.allocator_4k_map == pre.allocator_4k_map
        && post.allocator_2m_map == pre.allocator_2m_map
        && post.allocator_1g_map == pre.allocator_1g_map
        && post.default_pagetable == pre.default_pagetable
    implies
        post.inv()
    by {
        assert(thread_perms_wf(post.thread_map)) by {
            reveal(thread_perms_wf);
            reveal(threads_inv);
            reveal(thread_free_quota_pending_empty_unless_wlocked);
        };
        thread_lock_op_preserves_invariant_fields(
            pre.thread_map,
            post.thread_map,
            changed,
        );
        kernel_inv_preserved_for_thread_lock_op(pre, post);
    };
}

}

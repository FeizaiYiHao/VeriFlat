use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Kernel invariants read process payloads and read-only data, but never the
/// current process lock owner.
#[verifier::opaque]
pub open spec fn process_invariant_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.spec_index(p_ptr)]
        pre.dom().contains(p_ptr) ==>
        {
            &&& post.spec_index(p_ptr).view()
                == pre.spec_index(p_ptr).view()
            &&& post.spec_index(p_ptr).view_rodata()
                == pre.spec_index(p_ptr).view_rodata()
        }
}

pub proof fn process_lock_op_preserves_invariant_fields(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    changed: RwLockProcessPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
        post.spec_index(changed).view_rodata()
            == pre.spec_index(changed).view_rodata(),
    ensures
        process_invariant_fields_unchanged(pre, post),
{
    reveal(process_invariant_fields_unchanged);
}

/// Preserve the complete kernel invariant across a process lock/unlock.  The
/// only non-first-order part is the three quota folds, kept inside this lemma.
pub proof fn kernel_inv_preserved_for_process_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.inv(),
        process_perms_wf(post.process_map),
        process_invariant_fields_unchanged(
            pre.process_map,
            post.process_map,
        ),
        post.pagetable_map == pre.pagetable_map,
        post.page_array == pre.page_array,
        post.cpu_array == pre.cpu_array,
        post.cpu_tlb == pre.cpu_tlb,
        post.root_container == pre.root_container,
        post.container_map == pre.container_map,
        post.scheduler_map == pre.scheduler_map,
        post.thread_map == pre.thread_map,
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
        assert(container_process_page_pagetable_wf(
            post.container_map,
            post.process_map,
            post.pagetable_map,
            post.page_array,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(container_process_page_pagetable_wf);
            reveal(container_process_wf);
            reveal(process_pagetable_match);
            reveal(container_page_owner_wf);
            reveal(mapped_4k_page_pagetable_wf);
            reveal(mapped_2m_page_pagetable_wf);
            reveal(mapped_1g_page_pagetable_wf);
        };
        assert(process_pages_wf(
            post.page_array,
            post.process_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(process_pages_wf);
        };
        assert(container_process_allocator_quota_4k_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_4k_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(container_process_allocator_quota_4k_wf);
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr)
                    .view_rodata().view().allocator_ptr_4k]
                post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view()
                    .owned_processes.view().fold(
                        0,
                        |sum: int, p_ptr: RwLockProcessPtr|
                            sum + process_effective_quota_4k(
                                post.process_map.spec_index(p_ptr),
                            ),
                    )
                    == pre.container_map.spec_index(c_ptr).view()
                        .owned_processes.view().fold(
                            0,
                            |sum: int, p_ptr: RwLockProcessPtr|
                                sum + process_effective_quota_4k(
                                    pre.process_map.spec_index(p_ptr),
                                ),
                        )
            by {
                assert(post.container_map.spec_index(c_ptr).view()
                    .owned_processes.view().subset_of(
                        pre.process_map.dom(),
                    )) by {
                    reveal(container_process_wf);
                };
                lemma_process_effective_quota_4k_fold_eq(
                    post.container_map.spec_index(c_ptr).view()
                        .owned_processes.view(),
                    pre.process_map,
                    post.process_map,
                );
            };
        };
        assert(container_process_allocator_quota_2m_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_2m_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(container_process_allocator_quota_2m_wf);
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr)
                    .view_rodata().view().allocator_ptr_2m]
                post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view()
                    .owned_processes.view().fold(
                        0,
                        |sum: int, p_ptr: RwLockProcessPtr|
                            sum + process_effective_quota_2m(
                                post.process_map.spec_index(p_ptr),
                            ),
                    )
                    == pre.container_map.spec_index(c_ptr).view()
                        .owned_processes.view().fold(
                            0,
                            |sum: int, p_ptr: RwLockProcessPtr|
                                sum + process_effective_quota_2m(
                                    pre.process_map.spec_index(p_ptr),
                                ),
                        )
            by {
                assert(post.container_map.spec_index(c_ptr).view()
                    .owned_processes.view().subset_of(
                        pre.process_map.dom(),
                    )) by {
                    reveal(container_process_wf);
                };
                lemma_process_effective_quota_2m_fold_eq(
                    post.container_map.spec_index(c_ptr).view()
                        .owned_processes.view(),
                    pre.process_map,
                    post.process_map,
                );
            };
        };
        assert(container_process_allocator_quota_1g_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_1g_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(container_process_allocator_quota_1g_wf);
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr)
                    .view_rodata().view().allocator_ptr_1g]
                post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view()
                    .owned_processes.view().fold(
                        0,
                        |sum: int, p_ptr: RwLockProcessPtr|
                            sum + process_effective_quota_1g(
                                post.process_map.spec_index(p_ptr),
                            ),
                    )
                    == pre.container_map.spec_index(c_ptr).view()
                        .owned_processes.view().fold(
                            0,
                            |sum: int, p_ptr: RwLockProcessPtr|
                                sum + process_effective_quota_1g(
                                    pre.process_map.spec_index(p_ptr),
                                ),
                        )
            by {
                assert(post.container_map.spec_index(c_ptr).view()
                    .owned_processes.view().subset_of(
                        pre.process_map.dom(),
                    )) by {
                    reveal(container_process_wf);
                };
                lemma_process_effective_quota_1g_fold_eq(
                    post.container_map.spec_index(c_ptr).view()
                        .owned_processes.view(),
                    pre.process_map,
                    post.process_map,
                );
            };
        };
        assert(process_pagetable_match(
            post.process_map,
            post.pagetable_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(process_pagetable_match);
        };
        assert(process_staged_pages_wf(
            post.process_map,
            post.page_array,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(process_staged_pages_4k_wf);
            reveal(process_staged_pages_2m_wf);
            reveal(process_staged_pages_1g_wf);
        };
    };
    assert(post.process_management_inv()) by {
        assert(container_process_wf(
            post.container_map,
            post.process_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(container_process_wf);
        };
        assert(per_container_process_tree_wf(
            post.container_map,
            post.process_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            per_container_process_tree_wf_preserved_for_tree_fields_eq(
                post.container_map,
                pre.process_map,
                post.process_map,
            );
        };
        assert(process_cpu_wf(
            post.process_map,
            post.cpu_array,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(process_cpu_wf);
        };
        assert(process_thread_wf(
            post.process_map,
            post.thread_map,
        )) by {
            reveal(process_invariant_fields_unchanged);
            reveal(process_thread_wf);
        };
    };
    assert(cpu_dirty_map_wf(
        post.container_map,
        post.process_map,
        post.cpu_array,
        post.cpu_tlb,
        post.pagetable_map,
    )) by {
        reveal(process_invariant_fields_unchanged);
        reveal(cpu_dirty_map_contains_container_processes);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
    assert(post.inv()) by {
        reveal(KernelK::inv);
    };
}

pub proof fn lemma_no_change_imply_kernel_inv_for_process_lock_op_forall()
    ensures
        forall|pre: KernelK, post: KernelK, changed: RwLockProcessPtr|
            #![trigger
                pre.inv(),
                post.inv(),
                post.process_map.unchanged_except(
                    &pre.process_map,
                    changed,
                )
            ]
            pre.inv()
            && pre.process_map.dom().contains(changed)
            && post.process_map.perms_wf()
            && post.process_map.unchanged_except(&pre.process_map, changed)
            && (post.process_map.spec_index(changed)
                    == pre.process_map.spec_index(changed)
                || {
                    &&& post.process_map.spec_index(changed).inv()
                    &&& (!(post.process_map.spec_index(changed)
                            .locking_thread() is Write)
                        ==> post.process_map.spec_index(changed).view()
                            .temp_alloc_clean())
                })
            && post.process_map.spec_index(changed).view()
                == pre.process_map.spec_index(changed).view()
            && post.process_map.spec_index(changed).view_rodata()
                == pre.process_map.spec_index(changed).view_rodata()
            && post.pagetable_map == pre.pagetable_map
            && post.page_array == pre.page_array
            && post.cpu_array == pre.cpu_array
            && post.cpu_tlb == pre.cpu_tlb
            && post.root_container == pre.root_container
            && post.container_map == pre.container_map
            && post.scheduler_map == pre.scheduler_map
            && post.thread_map == pre.thread_map
            && post.endpoint_map == pre.endpoint_map
            && post.allocator_4k_map == pre.allocator_4k_map
            && post.allocator_2m_map == pre.allocator_2m_map
            && post.allocator_1g_map == pre.allocator_1g_map
            && post.default_pagetable == pre.default_pagetable
            ==> post.inv(),
{
    assert forall|pre: KernelK, post: KernelK, changed: RwLockProcessPtr| #![auto]
        pre.inv()
        && pre.process_map.dom().contains(changed)
        && post.process_map.perms_wf()
        && post.process_map.unchanged_except(&pre.process_map, changed)
        && (post.process_map.spec_index(changed)
                == pre.process_map.spec_index(changed)
            || {
                &&& post.process_map.spec_index(changed).inv()
                &&& (!(post.process_map.spec_index(changed)
                        .locking_thread() is Write)
                    ==> post.process_map.spec_index(changed).view()
                        .temp_alloc_clean())
            })
        && post.process_map.spec_index(changed).view()
            == pre.process_map.spec_index(changed).view()
        && post.process_map.spec_index(changed).view_rodata()
            == pre.process_map.spec_index(changed).view_rodata()
        && post.pagetable_map == pre.pagetable_map
        && post.page_array == pre.page_array
        && post.cpu_array == pre.cpu_array
        && post.cpu_tlb == pre.cpu_tlb
        && post.root_container == pre.root_container
        && post.container_map == pre.container_map
        && post.scheduler_map == pre.scheduler_map
        && post.thread_map == pre.thread_map
        && post.endpoint_map == pre.endpoint_map
        && post.allocator_4k_map == pre.allocator_4k_map
        && post.allocator_2m_map == pre.allocator_2m_map
        && post.allocator_1g_map == pre.allocator_1g_map
        && post.default_pagetable == pre.default_pagetable
    implies
        post.inv()
    by {
        assert(process_perms_wf(post.process_map)) by {
            reveal(process_perms_wf);
            reveal(process_temp_alloc_empty_unless_wlocked);
        };
        process_lock_op_preserves_invariant_fields(
            pre.process_map,
            post.process_map,
            changed,
        );
        kernel_inv_preserved_for_process_lock_op(pre, post);
    };
}

}

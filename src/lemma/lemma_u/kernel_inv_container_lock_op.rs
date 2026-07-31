use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// The kernel invariants never read a container lock's current owner.  They
/// only read the map domain and these four non-lock projections.
#[verifier::opaque]
pub open spec fn container_invariant_fields_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger post.spec_index(c_ptr)]
        pre.dom().contains(c_ptr) ==>
        {
            &&& post.spec_index(c_ptr).view()
                == pre.spec_index(c_ptr).view()
            &&& post.spec_index(c_ptr).view_rodata()
                == pre.spec_index(c_ptr).view_rodata()
            &&& post.spec_index(c_ptr).view_kernel_ghost()
                == pre.spec_index(c_ptr).view_kernel_ghost()
            &&& post.spec_index(c_ptr).view_user_ghost()
                == pre.spec_index(c_ptr).view_user_ghost()
        }
}

/// Turn the pointwise postcondition of a container lock operation into the
/// projection used by invariant framing.
pub proof fn container_lock_op_preserves_invariant_fields(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    changed: RwLockContainerPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
        post.spec_index(changed).view_rodata()
            == pre.spec_index(changed).view_rodata(),
        post.spec_index(changed).view_kernel_ghost()
            == pre.spec_index(changed).view_kernel_ghost(),
        post.spec_index(changed).view_user_ghost()
            == pre.spec_index(changed).view_user_ghost(),
    ensures
        container_invariant_fields_unchanged(pre, post),
{
    reveal(container_invariant_fields_unchanged);
}

/// A container lock/unlock changes only lock state.  Equal companion fields
/// and equal container invariant projections preserve every kernel invariant.
pub proof fn kernel_inv_preserved_for_container_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.inv(),
        container_perms_wf(post.container_map),
        container_invariant_fields_unchanged(
            pre.container_map,
            post.container_map,
        ),
        post.pagetable_map == pre.pagetable_map,
        post.page_array == pre.page_array,
        post.cpu_array == pre.cpu_array,
        post.cpu_tlb == pre.cpu_tlb,
        post.root_container == pre.root_container,
        post.scheduler_map == pre.scheduler_map,
        post.process_map == pre.process_map,
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
        assert(container_page_owner_wf(
            post.container_map,
            post.page_array,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_page_owner_wf);
        };
        assert(container_process_page_pagetable_wf(
            post.container_map,
            post.process_map,
            post.pagetable_map,
            post.page_array,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_process_page_pagetable_wf);
            reveal(container_process_wf);
            reveal(process_pagetable_match);
            reveal(container_page_owner_wf);
        };
        assert(container_pages_wf(
            post.page_array,
            post.container_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_pages_wf);
        };
        assert(container_process_allocator_quota_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_4k_map,
            post.allocator_2m_map,
            post.allocator_1g_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
        };
        assert(container_allocator_wf(
            post.container_map,
            post.allocator_4k_map,
            post.allocator_2m_map,
            post.allocator_1g_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_allocator_wf);
        };
        assert(container_allocator_free_4k_page_wf(
            post.container_map,
            post.allocator_4k_map,
            post.page_array,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_wf);
            reveal(container_page_owner_wf);
        };
        assert(container_allocator_free_2m_page_wf(
            post.container_map,
            post.allocator_2m_map,
            post.page_array,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_allocator_free_2m_page_wf);
            reveal(container_allocator_wf);
            reveal(container_page_owner_wf);
        };
        assert(container_allocator_free_1g_page_wf(
            post.container_map,
            post.allocator_1g_map,
            post.page_array,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_allocator_free_1g_page_wf);
            reveal(container_allocator_wf);
            reveal(container_page_owner_wf);
        };
    };
    assert(post.process_management_inv()) by {
        assert(container_tree_wf(
            post.root_container,
            post.container_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            container_no_change_to_tree_fields_imply_wf(
                pre.root_container,
                pre.container_map,
                post.container_map,
            );
        };
        assert(container_process_wf(
            post.container_map,
            post.process_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_process_wf);
        };
        assert(per_container_process_tree_wf(
            post.container_map,
            post.process_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(per_container_process_tree_wf);
        };
        assert(container_cpu_wf(
            post.container_map,
            post.cpu_array,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_cpu_wf);
        };
        assert(container_thread_endpoint_wf(
            post.container_map,
            post.thread_map,
            post.endpoint_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
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
            reveal(container_invariant_fields_unchanged);
            reveal(container_thread_wf);
            reveal(container_scheduler_wf);
            reveal(container_thread_scheduler_wf);
        };
        assert(container_endpoint_wf(
            post.container_map,
            post.endpoint_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_endpoint_wf);
        };
        assert(container_scheduler_wf(
            post.container_map,
            post.scheduler_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_scheduler_wf);
        };
        assert(container_thread_wf(
            post.container_map,
            post.thread_map,
        )) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_thread_wf);
        };
    };
    assert(cpu_dirty_map_wf(
        post.container_map,
        post.process_map,
        post.cpu_array,
        post.cpu_tlb,
        post.pagetable_map,
    )) by {
        reveal(container_invariant_fields_unchanged);
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

}

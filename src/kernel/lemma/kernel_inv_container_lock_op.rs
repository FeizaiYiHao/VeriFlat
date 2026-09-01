use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Container invariant fields other than the empty-process write-lock guard.
pub open spec fn container_invariant_fields_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger pre.spec_index(c_ptr)]
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
}

/// Every non-container kernel field is framed by a container lock operation.
pub open spec fn container_lock_kernel_context_unchanged(
    pre: KernelK,
    post: KernelK,
) -> bool {
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.irt == pre.irt
    &&& post.pg_arr == pre.pg_arr
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.sched_mp == pre.sched_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.prc_mp == pre.prc_mp
    &&& post.thr_mp == pre.thr_mp
    &&& post.ep_mp == pre.ep_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
}

pub proof fn container_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_process_wf(pre.ctn_mp, pre.prc_mp),
        container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp),
        container_lock_kernel_context_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by {
        reveal(container_page_owner_wf);
    };
    assert(container_process_page_pagetable_wf(
        post.ctn_mp,
        post.prc_mp,
        post.pt_mp,
        post.pg_arr,
    )) by {
        reveal(container_process_page_pagetable_wf);
        reveal(container_process_wf);
        reveal(process_pagetable_match);
        reveal(container_page_owner_wf);
    };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by {
        reveal(container_pages_wf);
    };
    assert(container_process_allocator_quota_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        reveal(container_process_allocator_quota_4k_wf);
        reveal(container_process_allocator_quota_2m_wf);
        reveal(container_process_allocator_quota_1g_wf);
    };
    assert(container_allocator_wf(
        post.ctn_mp,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        reveal(container_allocator_wf);
    };
}

pub proof fn container_no_change_imply_process_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.process_management_inv(),
        container_process_wf(post.ctn_mp, post.prc_mp),
        container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp),
        container_lock_kernel_context_unchanged(pre, post),
    ensures
        post.process_management_inv(),
{
    assert(container_pcid_allocator_wf(
        post.ctn_mp,
        post.pcid_allc_mp,
    )) by {
        lemma_no_change_imply_container_pcid_allocator_wf_forall();
    };
    assert(process_pcid_allocator_wf(
        post.ctn_mp,
        post.prc_mp,
        post.pcid_allc_mp,
    )) by {
        lemma_no_change_imply_process_pcid_allocator_wf_for_container_fields_forall();
    };
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by {
        container_no_change_to_tree_fields_imply_wf(
            pre.rt_ctn,
            pre.ctn_mp,
            post.ctn_mp,
        );
    };
    assert({
        &&& pre.ctn_mp.dom().contains(pre.rt_ctn)
        &&& post.ctn_mp.dom().contains(post.rt_ctn)
        &&& pre.ctn_mp.spec_index(pre.rt_ctn).view().root_process_in_processes()
        &&& post.ctn_mp.spec_index(post.rt_ctn).view().root_process_in_processes()
    }) by {
        reveal(container_root_wf);
        reveal(container_invariant_fields_unchanged);
    };
    assert(per_container_process_tree_wf(
        post.ctn_mp,
        post.prc_mp,
    )) by {
        reveal(per_container_process_tree_wf);
    };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_arr)) by {
        reveal(container_cpu_wf);
    };
    assert(container_thread_endpoint_wf(
        post.ctn_mp,
        post.thr_mp,
        post.ep_mp,
    )) by {
        reveal(container_endpoint_wf);
        reveal(thread_endpoint_ref_counter_wf);
        reveal(thread_endpoint_queue_wf);
        reveal(container_thread_endpoint_wf);
    };
    assert(container_thread_scheduler_wf(
        post.ctn_mp,
        post.thr_mp,
        post.sched_mp,
    )) by {
        reveal(container_thread_wf);
        reveal(container_scheduler_wf);
        reveal(container_thread_scheduler_wf);
    };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by {
        reveal(container_endpoint_wf);
    };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by {
        reveal(container_scheduler_wf);
    };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by {
        reveal(container_thread_wf);
    };
}

pub proof fn container_no_change_imply_cpu_dirty_map_wf(
    pre: KernelK,
    post: KernelK,
)
    requires
        cpu_dirty_map_wf(
            pre.ctn_mp,
            pre.prc_mp,
            pre.cpu_arr,
            pre.cpu_tlb,
            pre.pt_mp,
        ),
        container_cpu_wf(pre.ctn_mp, pre.cpu_arr),
        container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp),
        container_lock_kernel_context_unchanged(pre, post),
    ensures
        cpu_dirty_map_wf(
            post.ctn_mp,
            post.prc_mp,
            post.cpu_arr,
            post.cpu_tlb,
            post.pt_mp,
        ),
{
    reveal(cpu_dirty_map_contains_container_processes);
    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    reveal(cpu_dirty_map_proc_pcid_match);
    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    reveal(container_cpu_wf);
}

}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Kernel invariants read process payloads and read-only data, but never the
/// current process lock owner.
pub open spec fn process_invariant_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger pre.spec_index(p_ptr)]
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
}

/// Every non-process kernel field is framed by a process lock operation.
pub open spec fn process_lock_kernel_context_unchanged(
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
    &&& post.thread_map == pre.thread_map
    &&& post.endpoint_map == pre.endpoint_map
    &&& post.allocator_4k_map == pre.allocator_4k_map
    &&& post.allocator_2m_map == pre.allocator_2m_map
    &&& post.allocator_1g_map == pre.allocator_1g_map
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.root_container == pre.root_container
    &&& post.default_pagetable == pre.default_pagetable
}

pub proof fn process_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_process_wf(pre.container_map, pre.process_map),
        process_invariant_fields_unchanged(pre.process_map, post.process_map),
        process_lock_kernel_context_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(container_process_page_pagetable_wf(
        post.container_map,
        post.process_map,
        post.pagetable_map,
        post.page_array,
    )) by {
        lemma_no_change_imply_container_process_page_pagetable_wf_forall();
    };
    assert(process_pages_wf(post.page_array, post.process_map)) by {
        lemma_no_change_imply_process_pages_wf_forall();
    };
    assert(container_process_allocator_quota_4k_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_4k_map,
    )) by {
        reveal(container_process_allocator_quota_4k_wf);
        reveal(container_process_wf);
        lemma_process_effective_quota_4k_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_2m_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_2m_map,
    )) by {
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(
            post.container_map,
            post.thread_map,
            post.allocator_2m_map,
            pre.process_map,
            post.process_map,
        );
    };
    assert(container_process_allocator_quota_1g_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_1g_map,
    )) by {
        container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(
            post.container_map,
            post.thread_map,
            post.allocator_1g_map,
            pre.process_map,
            post.process_map,
        );
    };
    assert(process_pagetable_match(post.process_map, post.pagetable_map)) by {
        lemma_no_change_imply_process_pagetable_match_forall();
    };
    assert(process_iommu_table_match(
        post.process_map,
        post.iommu_table_map,
    )) by {
        lemma_no_change_imply_process_iommu_table_match_forall();
    };
}

pub proof fn process_no_change_imply_process_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.process_management_inv(),
        process_invariant_fields_unchanged(pre.process_map, post.process_map),
        process_lock_kernel_context_unchanged(pre, post),
    ensures
        post.process_management_inv(),
{
    assert(process_pcid_allocator_wf(
        post.container_map,
        post.process_map,
        post.pcid_allocator_map,
    )) by {
        lemma_no_change_imply_process_pcid_allocator_wf_forall();
    };
    assert(container_process_wf(post.container_map, post.process_map)) by {
        lemma_no_change_imply_container_process_wf_forall();
    };
    assert(per_container_process_tree_wf(
        post.container_map,
        post.process_map,
    )) by {
        lemma_no_change_imply_per_container_process_tree_wf_forall();
    };
    assert(process_cpu_wf(post.process_map, post.cpu_array)) by {
        lemma_no_change_imply_process_cpu_wf_forall();
    };
    assert(process_thread_wf(post.process_map, post.thread_map)) by {
        lemma_no_change_imply_process_thread_wf_forall();
    };
}

}

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
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.irt == pre.irt
    &&& post.pg_arr == pre.pg_arr
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.sched_mp == pre.sched_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
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

pub proof fn process_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_process_wf(pre.ctn_mp, pre.prc_mp),
        process_invariant_fields_unchanged(pre.prc_mp, post.prc_mp),
        process_lock_kernel_context_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(container_process_page_pagetable_wf(
        post.ctn_mp,
        post.prc_mp,
        post.pt_mp,
        post.pg_arr,
    )) by {
        lemma_no_change_imply_container_process_page_pagetable_wf_forall();
    };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by {
        lemma_no_change_imply_process_pages_wf_forall();
    };
    assert(container_process_allocator_quota_4k_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_4k_mp,
    )) by {
        reveal(container_process_allocator_quota_4k_wf);
        reveal(container_process_wf);
        lemma_process_effective_quota_4k_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_2m_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_2m_mp,
    )) by {
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(
            post.ctn_mp,
            post.thr_mp,
            post.allc_2m_mp,
            pre.prc_mp,
            post.prc_mp,
        );
    };
    assert(container_process_allocator_quota_1g_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_1g_mp,
    )) by {
        container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(
            post.ctn_mp,
            post.thr_mp,
            post.allc_1g_mp,
            pre.prc_mp,
            post.prc_mp,
        );
    };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by {
        lemma_no_change_imply_process_pagetable_match_forall();
    };
    assert(process_iommu_table_match(
        post.prc_mp,
        post.it_mp,
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
        process_invariant_fields_unchanged(pre.prc_mp, post.prc_mp),
        process_lock_kernel_context_unchanged(pre, post),
    ensures
        post.process_management_inv(),
{
    assert(process_pcid_allocator_wf(
        post.ctn_mp,
        post.prc_mp,
        post.pcid_allc_mp,
    )) by {
        lemma_no_change_imply_process_pcid_allocator_wf_forall();
    };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by {
        lemma_no_change_imply_container_process_wf_forall();
    };
    assert(per_container_process_tree_wf(
        post.ctn_mp,
        post.prc_mp,
    )) by {
        lemma_no_change_imply_per_container_process_tree_wf_forall();
    };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by {
        lemma_no_change_imply_process_cpu_wf_forall();
    };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        lemma_no_change_imply_process_thread_wf_forall();
    };
}

}

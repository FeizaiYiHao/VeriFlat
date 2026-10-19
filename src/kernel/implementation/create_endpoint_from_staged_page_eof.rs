use vstd::prelude::*;
use crate::*;

verus! {
/// Complete kernel-state summary of `create_endpoint_from_staged_page`.
#[verifier::opaque]
pub open spec fn create_endpoint_from_staged_page_eof_transition_framing(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let pre_container = pre.ctn_mp.spec_index(container_ptr);
    let post_container = post.ctn_mp.spec_index(container_ptr);
    let pre_staging = pre.thr_mp.spec_index(staging_thread_ptr);
    let post_staging = post.thr_mp.spec_index(staging_thread_ptr);
    let endpoint = post.ep_mp.spec_index(page_ptr);
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& post_page.view() == (Page { state: PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    &&& post_page.view().perm_4k.view().is_none()
    &&& post_page.view_rodata() == pre_page.view_rodata()
    &&& post_page.view_ghost() == pre_page.view_ghost()
    &&& post_page.locking_thread() == pre_page.locking_thread()
    &&& post_page.being_killed() == pre_page.being_killed()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& post_container.view() == pre_container.view()
    &&& post_container.view_rodata() == pre_container.view_rodata()
    &&& post_container.view_ghost() == (ContainerGhost { owned_endpoints: Ghost(pre_container.view_ghost().owned_endpoints.view().insert(page_ptr)), ..pre_container.view_ghost() })
    &&& post_container.locking_thread() == pre_container.locking_thread()
    &&& post_container.being_killed() == pre_container.being_killed()
    &&& post_container.killer_info() == pre_container.killer_info()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, staging_thread_ptr)
    &&& post_staging.view() == (Thread {
        quota_4k: post_staging.view().quota_4k, temp_alloc_cache_4k: post_staging.view().temp_alloc_cache_4k,
        endpoint_descriptors: post_staging.view().endpoint_descriptors, ..pre_staging.view()
    })
    &&& post_staging.view().temp_alloc_cache_4k.view() == pre_staging.view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& post_staging.view().quota_4k == pre_staging.view().quota_4k - 1
    &&& post_staging.view().endpoint_descriptors.view() == pre_staging.view().endpoint_descriptors.view().update(endpoint_index as int, Some(page_ptr))
    &&& post_staging.locking_thread() == pre_staging.locking_thread()
    &&& post_staging.being_killed() == pre_staging.being_killed()
    &&& post_staging.killer_info() == pre_staging.killer_info()
    &&& post_staging.view_ghost() == pre_staging.view_ghost()
    &&& post.ep_mp.dom() == pre.ep_mp.dom().insert(page_ptr)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)] pre.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e) == pre.ep_mp.spec_index(e)
    &&& endpoint.is_init()
    &&& !endpoint.being_killed()
    &&& endpoint.view().queue.view() == Seq::<RwLockThreadPtr>::empty()
    &&& endpoint.view().queue_state == EndpointState::RECEIVE
    &&& endpoint.view().owning_threads.view() == set![(staging_thread_ptr, endpoint_index)]
    &&& endpoint.view().owning_container == container_ptr
}

proof fn eof_create_endpoint_memory_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_endpoint_from_staged_page_eof_transition_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.memory_management_inv(),
{
    reveal(create_endpoint_from_staged_page_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
        page_iommu_table_wf_preserved_for_nonmapped_page_change(pre.ctn_mp, pre.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, page_index);
        reveal(page_iommu_table_wf);
    };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(pre.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, pre.allc_4k_mp);
            container_process_allocator_quota_4k_wf_preserved_for_container_allocator_eq(pre.ctn_mp, post.ctn_mp, post.prc_mp, post.thr_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp);
            reveal(container_thread_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(pre.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, pre.allc_2m_mp);
            container_process_allocator_quota_2m_wf_preserved_for_container_allocator_eq(pre.ctn_mp, post.ctn_mp, post.prc_mp, post.thr_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_4k_mp, pre.allc_1g_mp);
            reveal(container_thread_wf);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
    };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

proof fn eof_create_endpoint_ref_counter_wf(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        thread_endpoint_ref_counter_wf(pre.thr_mp, pre.ep_mp),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.wf(),
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        create_endpoint_from_staged_page_eof_transition_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
{
    reveal(create_endpoint_from_staged_page_eof_transition_framing); reveal(thread_endpoint_ref_counter_wf);
}

proof fn eof_create_endpoint_process_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        !pre.ep_mp.dom().contains(page_ptr),
        create_endpoint_from_staged_page_eof_transition_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.process_management_inv(),
{
    reveal(create_endpoint_from_staged_page_eof_transition_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { container_cpu_wf_preserved_for_container_cpu_fields_eq(pre.ctn_mp, post.ctn_mp, post.cpu_set_mp, post.cpu_arr); };
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by {
        thread_perms_wf_at(pre.thr_mp, staging_thread_ptr); eof_create_endpoint_ref_counter_wf(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
}

pub(super) proof fn eof_create_endpoint_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        !pre.ep_mp.dom().contains(page_ptr),
        create_endpoint_from_staged_page_eof_transition_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.inv(),
{
    eof_create_endpoint_memory_management_inv(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    eof_create_endpoint_process_management_inv(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    reveal(create_endpoint_from_staged_page_eof_transition_framing);
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf);
    };
}
}

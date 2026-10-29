use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn publish_staged_container_root_eof_object_pages_allocators_pagetable(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(allocator_4k_pages_wf(post.pg_arr, post.allc_4k_mp)) by {
        assert(allocator_4k_pages_forward_wf(pre.pg_arr, pre.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
        assert(allocator_4k_pages_backward_wf(pre.pg_arr, pre.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
        assert(allocator_4k_pages_forward_wf(post.pg_arr, post.allc_4k_mp)) by { page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; };
        assert(allocator_4k_pages_backward_wf(post.pg_arr, post.allc_4k_mp)) by { page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; };
        reveal(allocator_4k_pages_wf);
    };
    assert(allocator_2m_pages_wf(post.pg_arr, post.allc_2m_mp)) by {
        assert(allocator_2m_pages_forward_wf(pre.pg_arr, pre.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
        assert(allocator_2m_pages_backward_wf(pre.pg_arr, pre.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
        assert(allocator_2m_pages_forward_wf(post.pg_arr, post.allc_2m_mp)) by { page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; };
        assert(allocator_2m_pages_backward_wf(post.pg_arr, post.allc_2m_mp)) by { page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; };
        reveal(allocator_2m_pages_wf);
    };
    assert(allocator_1g_pages_wf(post.pg_arr, post.allc_1g_mp)) by {
        assert(allocator_1g_pages_forward_wf(pre.pg_arr, pre.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
        assert(allocator_1g_pages_backward_wf(pre.pg_arr, pre.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
        assert(allocator_1g_pages_forward_wf(post.pg_arr, post.allc_1g_mp)) by { page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; };
        assert(allocator_1g_pages_backward_wf(post.pg_arr, post.allc_1g_mp)) by { page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; };
        reveal(allocator_1g_pages_wf);
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        assert(pagetable_root_page_forward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_closure_page_forward_wf(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_root_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_closure_page_backward_wf(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_root_page_forward_wf(post.pt_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); };
        assert(pagetable_closure_page_forward_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); };
        assert(pagetable_root_page_backward_wf(post.pt_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); };
        assert(pagetable_closure_page_backward_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { broadcast use publish_staged_container_root_eof_existing_pagetable_closure_page_backward; };
        reveal(pagetable_pages_wf);
    };
}

pub(super) proof fn publish_staged_container_root_eof_object_pages_process_thread_iommu_endpoint(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        process_pages_wf(post.pg_arr, post.prc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); reveal(process_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(iommu_table_pages_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
}

pub(super) proof fn publish_staged_container_root_eof_object_pages_scheduler_cpu_set(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); reveal(scheduler_pages_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); reveal(cpu_set_pages_wf); };
}

pub(super) proof fn publish_staged_container_root_eof_object_pages_pcid_allocator(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); reveal(pcid_allocator_pages_wf);
    };
}

pub(super) proof fn publish_staged_container_root_eof_object_pages_container_process_pagetable(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
    ensures container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf); reveal(container_process_page_pagetable_wf);
    };
}

pub(super) proof fn publish_staged_container_root_eof_object_pages_iommu(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(container_page_owner_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    };
}
}

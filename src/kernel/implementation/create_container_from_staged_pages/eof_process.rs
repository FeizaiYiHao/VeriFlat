use vstd::prelude::*;
use crate::*;
use super::*;

verus! {

#[verifier::spinoff_prover]
pub(super) proof fn eof_container_uppertree_seq_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp),
{
    assert(container_uppertree_seq_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); };
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    let child_uppers = post.ctn_mp.spec_index(container_page).view_ghost().uppertree_seq.view();
    assert(container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf);
        seq_push_lemma::<RwLockContainerPtr>(); seq_push_unique_lemma::<RwLockContainerPtr>();
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_container_tree_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(container_root_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_root_wf); };
    assert(container_children_parent_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_children_parent_wf); seq_push_lemma::<RwLockContainerPtr>(); };
    assert(containers_linkedlist_wf(post.rt_ctn, post.ctn_mp)) by { reveal(containers_linkedlist_wf); reveal(container_children_parent_wf); seq_push_lemma::<RwLockContainerPtr>(); };
    assert(container_children_depth_wf(post.rt_ctn, post.ctn_mp)) by {
        assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(container_perms_wf); };
        let child_uppers = pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr);
        reveal(container_children_depth_wf); reveal(container_tree_fields_wf);
        seq_push_lemma::<RwLockContainerPtr>();
    };
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(container_perms_wf); };
    assert(container_subtree_set_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf); seq_push_lemma::<RwLockContainerPtr>(); };
    eof_container_uppertree_seq_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(container_subtree_set_exclusive(post.rt_ctn, post.ctn_mp)) by {
        reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
        seq_push_lemma::<RwLockContainerPtr>();
        seq_push_unique_lemma::<RwLockContainerPtr>();
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_container_cpu_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp),
        container_cpu_wf(pre.ctn_mp, pre.cpu_set_mp, pre.cpu_arr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
{
    reveal(publish_staged_container_root_kernel_state_framing); reveal(container_cpu_set_wf); reveal(container_cpu_wf);
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_container_relations_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_tree_wf(process_page, set![process_page], post.prc_mp,)) by {
        reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_children_depth_wf); reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
    };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); reveal(container_process_wf); process_no_change_to_tree_fields_imply_wf_forall(); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    eof_container_cpu_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { pcid_allocator_perms_wf_at(post.pcid_allc_mp, pcid_allocator_page); reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp,)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    assert(process_empty_lists_wlocked(post.prc_mp)) by {
        assert(process_empty_lists_wlocked(pre.prc_mp)) by { reveal(process_thread_wf); };
        reveal(process_empty_lists_wlocked);
    };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); reveal(process_empty_lists_wlocked); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_process_management_inv(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        post.process_management_inv(),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    eof_container_tree_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    eof_container_relations_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_direct_invariants(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        post.process_management_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(&post.irt, post.prc_mp),
        iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp),
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush,),
        tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(cpu_dirty_map_contains_container_processes(post.ctn_mp, post.cpu_set_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,)) by { reveal(container_cpu_wf); reveal(cpu_dirty_map_contains_container_processes); };
    assert(cpu_dirty_map_proc_pcid_match(post.prc_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,)) by { reveal(cpu_dirty_map_proc_pcid_match); };
    assert(cpu_not_in_dirty_map_imply_not_in_tlb(post.cpu_arr, post.cpu_tlb)) by { reveal(cpu_not_in_dirty_map_imply_not_in_tlb); };
    assert(cpu_dirty_map_contains_pagetable_pcid_match(post.pt_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_container_page_owner_forward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, c_ptr: RwLockContainerPtr, page_ptr: PagePtr,
)
    requires
        container_page_owner_forward_wf(pre.ctn_mp, pre.pg_arr),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.ctn_mp.dom().contains(c_ptr),
        post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)
        ]
        {
            &&& page_ptr_valid(page_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    let moved_pages = new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).union(funding_pages.to_set());
    if c_ptr == container_page {
        assert(post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr) by {
            if funding_pages.to_set().contains(page_ptr) {
            } else {
                let container_head = page_ptr2page_index(container_page);
                let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
                reveal(new_container_moved_pages);
                if page_2m_all_ptrs(container_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                    page_2m_ptr_prefix_member_bounds(container_head, 512, page_ptr);
                    if page_ptr2page_index(page_ptr) != container_head {
                    }
                } else if page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                    page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, page_ptr,);
                    if page_ptr2page_index(page_ptr) != pcid_allocator_head {
                    }
                } else {
                    reveal(new_container_bootstrap_4k_pages);
                }
            }
        };
    } else if c_ptr == parent_container_ptr {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
    } else {
        assert(!moved_pages.contains(page_ptr)) by {
            if moved_pages.contains(page_ptr) {
            }
        };
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
    }
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_container_page_owner_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
)
    requires
        container_page_owner_backward_wf(pre.ctn_mp, pre.pg_arr),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().owning_container
        ]
        {
            let c_ptr = post.pg_arr.spec_index(page_index).view().view().owning_container;
            &&& post.ctn_mp.dom().contains(c_ptr)
            &&& post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_index2page_ptr(page_index))
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    let page_ptr = page_index2page_ptr(page_index);
    let moved_pages = new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).union(funding_pages.to_set());
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    if moved_pages.contains(page_ptr) {
        assert(post.pg_arr.spec_index(page_index).view().view().owning_container == container_page) by {
            if funding_pages.to_set().contains(page_ptr) {
            } else {
                let container_head = page_ptr2page_index(container_page);
                let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
                reveal(new_container_moved_pages);
                if page_2m_all_ptrs(container_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                    page_2m_ptr_prefix_member_bounds(container_head, 512, page_ptr);
                    if page_index != container_head {
                    }
                } else if page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                    page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, page_ptr,);
                    if page_index != pcid_allocator_head {
                    }
                } else {
                    reveal(new_container_bootstrap_4k_pages);
                }
            }
        };
    } else {
        eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_index,
        );
        let c_ptr = pre.pg_arr.spec_index(page_index).view().view().owning_container;
        if c_ptr == parent_container_ptr {
        } else {
        }
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_container_page_owner_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
{
    assert(container_page_owner_forward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_page_owner_wf); };
    assert(container_page_owner_backward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_page_owner_wf); };
    assert(container_page_owner_forward_wf(post.ctn_mp, post.pg_arr)) by { broadcast use eof_container_page_owner_forward; };
    assert(container_page_owner_backward_wf(post.ctn_mp, post.pg_arr)) by { broadcast use eof_container_page_owner_backward; };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_memory_management_inv(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.no_duplicates(),
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        )),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        forall|page_ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(page_ptr)]
            funding_pages.to_set().contains(page_ptr) ==> page_ptr_valid(page_ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr,),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.allocator_free_pages_wf(),
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
        post.memory_management_inv(),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    eof_container_page_owner_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    eof_object_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    eof_hugepage_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    eof_container_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    eof_thread_staged_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    eof_allocator_free_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    eof_allocator_quota_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
}
}

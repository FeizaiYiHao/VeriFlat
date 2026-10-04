use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn eof_subsystems_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_page_ptr).inv(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        post.subsystems_inv(),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    let process_page_index = page_ptr2page_index(process_page_ptr);
    let pagetable_page_index = page_ptr2page_index(pagetable_page_ptr);
    let l4_page_index = page_ptr2page_index(l4_page_ptr);
    assert(index_valid(NUM_PAGES, process_page_index) && index_valid(NUM_PAGES, pagetable_page_index) && index_valid(NUM_PAGES, l4_page_index)) by {
        page_ptr_valid_imply_page_index_valid();
    };
    assert(process_page_index != pagetable_page_index && process_page_index != l4_page_index && pagetable_page_index != l4_page_index) by {
        page_ptr2page_index_neq(process_page_ptr, pagetable_page_ptr); page_ptr2page_index_neq(process_page_ptr, l4_page_ptr);
        page_ptr2page_index_neq(pagetable_page_ptr, l4_page_ptr);
    };
    assert(pagetable_perms_wf(post.pt_mp)) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); };
    assert(process_tree_fields_wf(post.prc_mp)) by {
        assert(process_tree_fields_wf(pre.prc_mp)) by { reveal(process_perms_wf); };
        reveal(container_process_wf);
        assert(!pre.prc_mp.spec_index(parent_ptr).view().children.view().contains(process_page_ptr)) by {
            reveal(per_container_process_tree_wf); reveal(process_children_parent_wf);
        };
        assert(!pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().contains(parent_ptr)) by {
            reveal(per_container_process_tree_wf); reveal(process_uppertree_seq_wf);
        };
        process_perms_wf_at(pre.prc_mp, parent_ptr); seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>();
    };
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked);
    };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_page_table_relations(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
    ensures
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
        page_ptr_valid_imply_page_index_valid();
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
}

#[verifier::spinoff_prover]
proof fn eof_thread_staged_pages_1g(pre: KernelK, post: KernelK, staging_thread_ptr: RwLockThreadPtr)
    requires
        thread_staged_pages_1g_wf(pre.thr_mp, pre.pg_arr),
        post.thr_mp.unchanged_except(&pre.thr_mp, staging_thread_ptr),
        post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g,
        forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && (pre.pg_arr.spec_index(i).view().view().state is Owned1g || post.pg_arr.spec_index(i).view().view().state is Owned1g)
            ==> post.pg_arr.spec_index(i).view().view().state == pre.pg_arr.spec_index(i).view().view().state,
    ensures
        thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr),
{
    reveal(thread_staged_pages_1g_wf);
}

pub(super) proof fn eof_memory_relations(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_kernel_state_framing);
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { eof_thread_staged_pages_1g(pre, post, staging_thread_ptr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by {
        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 3,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp),
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_4k_mp)) by {
        let old_target_owned = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        reveal(container_process_wf); lemma_process_effective_quota_folds_insert_zero(old_target_owned, pre.prc_mp, post.prc_mp, process_page_ptr);
        lemma_process_effective_quota_4k_fold_sum_eq_forall(); reveal(container_process_allocator_quota_4k_wf);
    };
    assert(thread_quota_4k_fields_unchanged(pre.thr_mp, post.thr_mp)) by {
        let old_staged_pages = pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view();
        lemma_set_ext_equal_three_distinct_len(old_staged_pages, process_page_ptr, pagetable_page_ptr, l4_page_ptr);
    };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by { reveal(container_thread_wf); };
    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_2m_mp)) by {
        let old_target_owned = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        reveal(container_process_wf); lemma_process_effective_quota_folds_insert_zero(old_target_owned, pre.prc_mp, post.prc_mp, process_page_ptr);
        lemma_process_effective_quota_2m_fold_sum_eq_forall(); reveal(container_process_allocator_quota_2m_wf);
    };
    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_1g_mp)) by {
        let old_target_owned = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        reveal(container_process_wf); lemma_process_effective_quota_folds_insert_zero(old_target_owned, pre.prc_mp, post.prc_mp, process_page_ptr);
        lemma_process_effective_quota_1g_fold_sum_eq_forall(); reveal(container_process_allocator_quota_1g_wf);
    };
    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_memory_management_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 3,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
    ensures
        post.memory_management_inv(),
{
    eof_page_table_relations(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    eof_memory_relations(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    eof_allocator_quota_wf(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_process_tree_invariants(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        process_perms_wf(post.prc_mp),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    let ancestors = pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr);
    let root_process = pre.ctn_mp.spec_index(container_ptr).view().root_process;
    let process_tree_dom = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    assert(process_tree_wf(root_process, process_tree_dom, pre.prc_mp)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
    assert(process_tree_fields_wf(post.prc_mp)) by {
        assert(process_tree_fields_wf(pre.prc_mp)) by { reveal(process_perms_wf); };
        assert(!pre.prc_mp.spec_index(parent_ptr).view().children.view().contains(process_page_ptr)) by { reveal(container_process_wf); reveal(process_children_parent_wf); };
        assert(!pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().contains(parent_ptr)) by { reveal(container_process_wf); reveal(process_uppertree_seq_wf); };
        process_perms_wf_at(pre.prc_mp, parent_ptr); seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>();
    };
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked);
    };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(process_add_child_ensures(root_process, process_tree_dom, pre.prc_mp, post.prc_mp, parent_ptr, process_page_ptr)) by {
        reveal(container_process_wf); ancestors.to_set_ensures(); seq_push_lemma::<RwLockProcessPtr>();
    };
    process_add_child_preserves_tree_wf(root_process, process_tree_dom, pre.prc_mp, post.prc_mp, parent_ptr, process_page_ptr);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(per_container_process_tree_wf); reveal(container_process_wf); reveal(process_uppertree_seq_wf); process_no_change_to_tree_fields_imply_wf_forall();
        ancestors.to_set_ensures();
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_process_management_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        post.process_management_inv(),
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_kernel_state_framing);
    eof_process_tree_invariants(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    assert(post.process_management_inv()) by {
        assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            reveal(container_thread_endpoint_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
        };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
        assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); reveal(container_pcid_allocator_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_scheduler_wf); reveal(container_thread_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(Seq::contains); reveal(process_empty_lists_wlocked); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 3,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_page_ptr).inv(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        post == (KernelK {
            pg_arr: post.pg_arr, prc_mp: post.prc_mp, pt_mp: post.pt_mp,
            ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pcid_allc_mp: post.pcid_allc_mp, ..pre
        }),
        post.prc_mp.dom() == pre.prc_mp.dom().insert(process_page_ptr),
        post.prc_mp.spec_index(parent_ptr).view().owned_threads == pre.prc_mp.spec_index(parent_ptr).view().owned_threads,
        post.prc_mp.spec_index(parent_ptr).being_killed() == pre.prc_mp.spec_index(parent_ptr).being_killed(),
        !post.prc_mp.spec_index(process_page_ptr).being_killed(),
        !post.prc_mp.spec_index(process_page_ptr).view().zombie,
        post.prc_mp.spec_index(process_page_ptr).view_rodata().view().owning_container == container_ptr,
        post.prc_mp.spec_index(process_page_ptr).view_rodata().view().pagetable == pagetable_page_ptr,
        post.prc_mp.spec_index(process_page_ptr).view().iommu_table == None,
        post.pt_mp.dom() == pre.pt_mp.dom().insert(pagetable_page_ptr),
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt)]
            pre.pt_mp.dom().contains(pt) ==> post.pt_mp.spec_index(pt) == pre.pt_mp.spec_index(pt),
        post.pt_mp.spec_index(pagetable_page_ptr).view().is_empty(),
        post.pt_mp.spec_index(pagetable_page_ptr).view().proc_ptr == process_page_ptr,
        post.prc_mp.spec_index(process_page_ptr).view().pagetable == pagetable_page_ptr,
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        post.thr_mp.dom() == pre.thr_mp.dom(),
        post.thr_mp.spec_index(staging_thread_ptr).view() == (Thread {
            quota_4k: (pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 3) as usize,
            temp_alloc_cache_4k: Ghost(Set::empty()), ..pre.thr_mp.spec_index(staging_thread_ptr).view()
        }),
        post.thr_mp.spec_index(staging_thread_ptr).being_killed() == pre.thr_mp.spec_index(staging_thread_ptr).being_killed(),
        post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom(),
        post.inv(),
        kernel_u_create_process_changed(kernel_k_to_nonlock_kernel_u(pre), kernel_k_to_nonlock_kernel_u(post), parent_ptr, process_page_ptr, staging_thread_ptr),
        kernel_k_to_nonlock_kernel_u(post) != kernel_k_to_nonlock_kernel_u(pre),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    eof_subsystems_inv(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    eof_memory_management_inv(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    eof_process_management_inv(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
    kernel_create_process_framing_implies_nonlock_u_step(
        pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
    );
}
}

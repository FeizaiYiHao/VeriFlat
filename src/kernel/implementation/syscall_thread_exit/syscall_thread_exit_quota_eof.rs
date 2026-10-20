use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_quota_spec::thread_exit_quota_eof_transition_framing;

verus! {
/// Returning the `size` quota of the exiting thread and of its process to their container's `size` allocator keeps the
/// kernel invariant.
pub(super) proof fn thread_exit_quota_eof_subsystems(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, allocator_ptr: RwLockPageAllocatorPtr,
    size: PageSize,
)
    requires
        pre.inv(),
        thread_exit_quota_eof_transition_framing(pre, post, process_ptr, thread_ptr, allocator_ptr, size),
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        allocator_ptr == match size {
            PageSize::SZ4k => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k,
            PageSize::SZ2m => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m,
            PageSize::SZ1g => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g,
        },
        match size {
            PageSize::SZ4k => pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k,
            PageSize::SZ2m => pre.allc_2m_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m,
            PageSize::SZ1g => pre.allc_1g_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g,
        } <= usize::MAX,
    ensures
        post.subsystems_inv(),
{
    reveal(thread_exit_quota_eof_transition_framing);
    assert(pre.prc_mp.perms_wf() && pre.thr_mp.perms_wf() && pre.thr_mp.spec_index(thread_ptr).inv()) by { reveal(process_perms_wf); reveal(thread_perms_wf); };
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); reveal(allocator_perms_wf);
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked);
    };
}

pub(super) proof fn thread_exit_quota_eof_memory(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, allocator_ptr: RwLockPageAllocatorPtr,
    size: PageSize,
)
    requires
        pre.inv(),
        thread_exit_quota_eof_transition_framing(pre, post, process_ptr, thread_ptr, allocator_ptr, size),
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        allocator_ptr == match size {
            PageSize::SZ4k => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k,
            PageSize::SZ2m => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m,
            PageSize::SZ1g => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g,
        },
        match size {
            PageSize::SZ4k => pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k,
            PageSize::SZ2m => pre.allc_2m_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m,
            PageSize::SZ1g => pre.allc_1g_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g,
        } <= usize::MAX,
    ensures
        post.memory_management_inv(),
{
    reveal(thread_exit_quota_eof_transition_framing);
    let process = pre.prc_mp.spec_index(process_ptr).view();
    let thread = pre.thr_mp.spec_index(thread_ptr).view();
    let dp4k = if size is SZ4k { -(process.quota_4k as int) } else { 0int };
    let dp2m = if size is SZ2m { -(process.quota_2m as int) } else { 0int };
    let dp1g = if size is SZ1g { -(process.quota_1g as int) } else { 0int };
    let dt4k = if size is SZ4k { -(thread.quota_4k as int) } else { 0int };
    let dt2m = if size is SZ2m { -(thread.quota_2m as int) } else { 0int };
    let dt1g = if size is SZ1g { -(thread.quota_1g as int) } else { 0int };
    assert(pre.prc_mp.perms_wf() && pre.thr_mp.perms_wf() && pre.thr_mp.spec_index(thread_ptr).inv()) by { reveal(process_perms_wf); reveal(thread_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            lemma_allocator_pages_wf_preserved_for_allocator_invariant_fields_except_quota_forall(); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { lemma_container_process_page_pagetable_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { lemma_page_iommu_table_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
        assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); reveal(container_allocator_wf); };
        assert(allocator_free_page_ptrs_wf(post.allc_4k_mp) && allocator_free_page_ptrs_wf(post.allc_2m_mp) && allocator_free_page_ptrs_wf(post.allc_1g_mp)) by {
            lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall::<ALLOCATOR_SIZE_4K>(); lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall::<ALLOCATOR_SIZE_2M>(); lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall::<ALLOCATOR_SIZE_1G>();
        };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(pre, post); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(pre, post); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { lemma_container_allocator_free_1g_page_wf_preserved_for_lock_op(pre, post); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            lemma_container_process_thread_quota_folds_change_forall(pre.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, process_ptr, thread_ptr, dp4k, dp2m, dp1g, dt4k, dt2m, dt1g); reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            lemma_container_process_thread_quota_folds_change_forall(pre.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, process_ptr, thread_ptr, dp4k, dp2m, dp1g, dt4k, dt2m, dt1g); reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            lemma_container_process_thread_quota_folds_change_forall(pre.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, process_ptr, thread_ptr, dp4k, dp2m, dp1g, dt4k, dt2m, dt1g); reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf);
        };
    };
}

pub(super) proof fn thread_exit_quota_eof_process(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, allocator_ptr: RwLockPageAllocatorPtr,
    size: PageSize,
)
    requires
        pre.inv(),
        thread_exit_quota_eof_transition_framing(pre, post, process_ptr, thread_ptr, allocator_ptr, size),
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        allocator_ptr == match size {
            PageSize::SZ4k => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k,
            PageSize::SZ2m => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m,
            PageSize::SZ1g => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g,
        },
        match size {
            PageSize::SZ4k => pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k,
            PageSize::SZ2m => pre.allc_2m_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m,
            PageSize::SZ1g => pre.allc_1g_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g,
        } <= usize::MAX,
    ensures
        post.process_management_inv(),
{
    reveal(thread_exit_quota_eof_transition_framing);
    assert(pre.prc_mp.perms_wf() && pre.thr_mp.perms_wf() && pre.thr_mp.spec_index(thread_ptr).inv()) by { reveal(process_perms_wf); reveal(thread_perms_wf); };
    assert(post.process_management_inv()) by {
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { lemma_process_pcid_allocator_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { lemma_per_container_process_tree_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp);
        };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
            process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp);
            lemma_process_thread_wf_preserved_for_process_thread_membership_fields_forall();
        };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        process_emptied_threads_wf_preserved_for_state_owned_threads_exited_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp);
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
    };
}

pub(super) proof fn thread_exit_quota_eof(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, allocator_ptr: RwLockPageAllocatorPtr,
    size: PageSize,
)
    requires
        pre.inv(),
        thread_exit_quota_eof_transition_framing(pre, post, process_ptr, thread_ptr, allocator_ptr, size),
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        allocator_ptr == match size {
            PageSize::SZ4k => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k,
            PageSize::SZ2m => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m,
            PageSize::SZ1g => pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g,
        },
        match size {
            PageSize::SZ4k => pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k,
            PageSize::SZ2m => pre.allc_2m_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m,
            PageSize::SZ1g => pre.allc_1g_mp.spec_index(allocator_ptr).quota.view().value + pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g,
        } <= usize::MAX,
    ensures
        post.inv(),
        forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
            pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if c == container_ptr && size is SZ4k { pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k } else { 0 },
        forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
            pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int + if c == container_ptr && size is SZ2m { pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m } else { 0 },
        forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
            pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view() as int
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view() as int + if c == container_ptr && size is SZ1g { pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g } else { 0 },
{
    reveal(thread_exit_quota_eof_transition_framing);
    assert(pre.prc_mp.perms_wf() && pre.thr_mp.perms_wf() && pre.thr_mp.spec_index(thread_ptr).inv()) by { reveal(process_perms_wf); reveal(thread_perms_wf); };
    thread_exit_quota_eof_subsystems(pre, post, container_ptr, process_ptr, thread_ptr, allocator_ptr, size);
    thread_exit_quota_eof_memory(pre, post, container_ptr, process_ptr, thread_ptr, allocator_ptr, size);
    thread_exit_quota_eof_process(pre, post, container_ptr, process_ptr, thread_ptr, allocator_ptr, size);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall();
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
    reveal(container_allocator_wf);
}
} // verus!

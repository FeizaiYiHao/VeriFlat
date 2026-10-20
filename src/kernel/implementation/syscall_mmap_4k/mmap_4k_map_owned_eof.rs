use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_4k_spec::mmap_4k_progress_after_leaf;

verus! {
/// Publishes the staged 4K page `page_ptr` of `thread_ptr` at `va` in `pagetable_ptr`: the page becomes mapped once, the thread
/// consumes it from its 4K cache and quota and advances its mmap progress; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn map_owned_4k_page_eof_transition_framing(pre: KernelK, post: KernelK, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_pt = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let new_pt = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr))
    &&& forall|other_pagetable: RwLockPageTableRoot|
        #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), other_pagetable)]
        pre.pt_mp.dom().contains(other_pagetable) && other_pagetable != pagetable_ptr ==> pagetable_c(post.pt_mp, post.pt_lower.view(), other_pagetable) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), other_pagetable)
    &&& post.pt_mp.spec_index(pagetable_ptr).locking_thread() == pre.pt_mp.spec_index(pagetable_ptr).locking_thread()
    &&& post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed()
    &&& post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view()
    &&& post.pt_mp.spec_index(pagetable_ptr).view_ghost() == post.pt_lower.view().spec_index(pagetable_ptr)
    &&& new_pt.mapping_4k() == old_pt.mapping_4k().insert(va, MapEntry { addr: page_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(old_page.view().owning_container) })
    &&& new_pt.mapping_2m() == old_pt.mapping_2m()
    &&& new_pt.page_closure() == old_pt.page_closure()
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view() == (Page { state: PageState::Mapped4k, mappings: new_page.view().mappings, ref_count: 1, ..old_page.view() })
    &&& new_page.view().mappings() == Set::empty().insert((pagetable_ptr, va))
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread {
        temp_alloc_cache_4k: new_thread.view().temp_alloc_cache_4k, quota_4k: new_thread.view().quota_4k, syscall_progress: new_thread.view().syscall_progress, ..old_thread.view()
    })
    &&& new_thread.view().temp_alloc_cache_4k.view() == old_thread.view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& new_thread.view().quota_4k == old_thread.view().quota_4k - 1
    &&& new_thread.view().syscall_progress.view() == mmap_4k_progress_after_leaf(old_thread.view().syscall_progress.view())
}

/// The published 4K leaf, the consumed staged page, and the charged thread quota keep the kernel invariant.
pub(super) proof fn map_owned_4k_page_eof(pre: KernelK, post: KernelK, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_4k_page_eof_transition_framing(pre, post, page_ptr, thread_ptr, pagetable_ptr, va),
        page_ptr_valid(page_ptr),
        va_4k_valid(va),
        pre.thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(pre.thr_mp.spec_index(thread_ptr)),
        !pre.thr_mp.spec_index(thread_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container,
        pre.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va) == false,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_wlocked(post.pt_mp, post.pt_lower.view()),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write,
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() is Write,
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(map_owned_4k_page_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by {
        assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked);
        };
    };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_4k_mapping_insert(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, pagetable_ptr, page_ptr, va); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
            process_thread_wf_at(pre.prc_mp, pre.thr_mp, thread_ptr); reveal(process_pagetable_match);
            container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(post.ctn_mp, post.prc_mp, pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, pagetable_ptr, page_ptr, va);
        };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_array_wf_at(pre.pg_arr, page_index); reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr);
        };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            reveal(thread_staged_pages_4k_wf);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by {
            reveal(process_emptied_tables_wf); reveal(process_pagetable_match); process_thread_wf_at(pre.prc_mp, pre.thr_mp, thread_ptr);
            process_perms_wf_at(pre.prc_mp, pre.thr_mp.spec_index(thread_ptr).view().owning_proc);
            process_emptied_threads_wf_at(pre.prc_mp, pre.thr_mp, pre.thr_mp.spec_index(thread_ptr).view().owning_proc, thread_ptr);
        };
        assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
            container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
        };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        tlb_wf_spec_preserved_for_4k_mapping_insert(post.cpu_tlb, post.cpu_arr, pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pagetable_ptr, va, post.pcid_needflush);
    };
}
} // verus!

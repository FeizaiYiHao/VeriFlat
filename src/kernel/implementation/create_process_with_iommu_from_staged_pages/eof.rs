use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
proof fn create_process_with_iommu_from_staged_pages_eof_subsystems_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_page_ptr).inv(),
        post.it_mp.perms_wf(),
        post.it_mp.spec_index(iommu_table_page_ptr).inv(),
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
    hide(Seq::contains);
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(pagetable_perms_wf(post.pt_mp)) by { reveal(pagetable_perms_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    create_process_with_iommu_from_staged_pages_eof_pagetable_window_holders_hold_pagetable(pre, post, pagetable_page_ptr);
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(iommu_table_perms_wf(post.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); };
    create_process_with_iommu_from_staged_pages_eof_process_perms_wf(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    create_process_with_iommu_from_staged_pages_eof_thread_perms_wf(pre, post, staging_thread_ptr);
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
}

/// The new empty page table has no locked window; every other page table keeps its window holders.
proof fn create_process_with_iommu_from_staged_pages_eof_pagetable_window_holders_hold_pagetable(pre: KernelK, post: KernelK, pagetable_page_ptr: PagePtr)
    requires
        pagetable_window_holders_hold_pagetable(pre.pt_mp, pre.pt_lower.view()),
        post.pt_mp.dom() == pre.pt_mp.dom().insert(pagetable_page_ptr),
        forall|pt_ptr: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt_ptr)]
            post.pt_mp.dom().contains(pt_ptr) && pt_ptr != pagetable_page_ptr ==> pre.pt_mp.dom().contains(pt_ptr) && post.pt_mp.spec_index(pt_ptr) == pre.pt_mp.spec_index(pt_ptr),
        forall|pt_ptr: RwLockPageTableRoot| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), pt_ptr)]
            pre.pt_mp.dom().contains(pt_ptr) ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pt_ptr) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pt_ptr),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_page_ptr).wf(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_page_ptr).is_empty(),
    ensures
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
{
    reveal(pagetable_window_holders_hold_pagetable); reveal(PageTableC::wf_window_locks);
    assert(forall|l4i: L4Index| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_page_ptr).spec_resolve_mapping_l4(l4i)]
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_page_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_page_ptr).spec_resolve_mapping_l4(l4i) is None);
}

/// The new process joins its parent's child list; every other process keeps its tree fields.
proof fn create_process_with_iommu_from_staged_pages_eof_process_perms_wf(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
    ensures
        process_tree_fields_wf(post.prc_mp),
        process_perms_wf(post.prc_mp),
{
    hide(Seq::contains);
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(process_tree_fields_wf(post.prc_mp)) by {
        reveal(Seq::contains);
        assert(process_tree_fields_wf(pre.prc_mp)) by { reveal(process_perms_wf); };
        reveal(container_process_wf);
        assert(!pre.prc_mp.spec_index(parent_ptr).view().children.view().contains(process_page_ptr)) by { reveal(per_container_process_tree_wf); reveal(process_children_parent_wf); };
        assert(!pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().contains(parent_ptr)) by { reveal(per_container_process_tree_wf); reveal(process_uppertree_seq_wf); };
        process_perms_wf_at(pre.prc_mp, parent_ptr); seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>();
    };
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
}

/// The staging thread only loses its staged 4K pages and their quota; every other thread is unchanged.
proof fn create_process_with_iommu_from_staged_pages_eof_thread_perms_wf(pre: KernelK, post: KernelK, staging_thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre.thr_mp),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.thr_mp.unchanged_except(&pre.thr_mp, staging_thread_ptr),
        post.thr_mp.spec_index(staging_thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(staging_thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k, ..pre.thr_mp.spec_index(staging_thread_ptr).view()
        }),
        post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().is_empty(),
        post.thr_mp.spec_index(staging_thread_ptr).locking_thread() == pre.thr_mp.spec_index(staging_thread_ptr).locking_thread(),
        post.thr_mp.spec_index(staging_thread_ptr).being_killed() == pre.thr_mp.spec_index(staging_thread_ptr).being_killed(),
        post.thr_mp.spec_index(staging_thread_ptr).killer_info() == pre.thr_mp.spec_index(staging_thread_ptr).killer_info(),
        post.thr_mp.spec_index(staging_thread_ptr).view_ghost() == pre.thr_mp.spec_index(staging_thread_ptr).view_ghost(),
    ensures
        thread_perms_wf(post.thr_mp),
{
    reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
    reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_transit_wf);
}

proof fn create_process_with_iommu_from_staged_pages_eof_page_table_relations(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp),
{
    hide(Seq::contains);
    create_process_with_iommu_from_staged_pages_eof_page_table_relations_pagetable(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_page_table_relations_iommu(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
}

/// The new page table and its root page close the page-table relations.
proof fn create_process_with_iommu_from_staged_pages_eof_page_table_relations_pagetable(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
{
    hide(Seq::contains);
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
}

/// The new IOMMU table and its root page close the IOMMU-table relations.
proof fn create_process_with_iommu_from_staged_pages_eof_page_table_relations_iommu(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_iommu_table_match(post.prc_mp, post.it_mp),
{
    hide(Seq::contains);
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
}

#[verifier::spinoff_prover]
proof fn create_process_with_iommu_from_staged_pages_eof_memory_relations_allocators(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.memory_management_inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
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

proof fn create_process_with_iommu_from_staged_pages_eof_memory_relations_object_pages(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.memory_management_inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr),
        thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr),
        thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
}

proof fn create_process_with_iommu_from_staged_pages_eof_memory_relations(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.memory_management_inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
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
    reveal(create_process_from_staged_pages_eof_transition_framing);
    create_process_with_iommu_from_staged_pages_eof_memory_relations_allocators(
        pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr,
        parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
    );
    create_process_with_iommu_from_staged_pages_eof_memory_relations_object_pages(
        pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr,
        parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
    );
}

proof fn create_process_with_iommu_from_staged_pages_eof_memory_management_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 5,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        post.memory_management_inv(),
{
    create_process_with_iommu_from_staged_pages_eof_page_table_relations(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_memory_relations(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_from_staged_pages_eof_allocator_quota_wf(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_wf(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_from_staged_pages_eof_page_object_owner_wf(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_from_staged_pages_eof_container_kill_retire_wf(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
}

/// The new process's object page, both root pages, and both L4 pages belong to its container; every other page keeps its
/// state, owner, and process.
proof fn create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_wf(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
{
    reveal(process_kernel_pages_owner_wf);
    create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_as_process(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_pagetable_root(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_iommu_root(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_pagetable_node(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_iommu_node(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
}

pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_inv(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 5,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_page_ptr).inv(),
        post.it_mp.perms_wf(),
        post.it_mp.spec_index(iommu_table_page_ptr).inv(),
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
        post == (KernelK { pg_arr: post.pg_arr, prc_mp: post.prc_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pcid_allc_mp: post.pcid_allc_mp, ..pre }),
        post.prc_mp.dom() == pre.prc_mp.dom().insert(process_page_ptr),
        post.prc_mp.spec_index(parent_ptr).view().owned_threads == pre.prc_mp.spec_index(parent_ptr).view().owned_threads,
        post.prc_mp.spec_index(parent_ptr).being_killed() == pre.prc_mp.spec_index(parent_ptr).being_killed(),
        !post.prc_mp.spec_index(process_page_ptr).being_killed(),
        !post.prc_mp.spec_index(process_page_ptr).view().zombie,
        post.prc_mp.spec_index(process_page_ptr).view().state.view() is Creating,
        post.prc_mp.spec_index(process_page_ptr).view_rodata().view().owning_container == container_ptr,
        post.prc_mp.spec_index(process_page_ptr).view_rodata().view().pagetable == pagetable_page_ptr,
        post.prc_mp.spec_index(process_page_ptr).view().iommu_table == Some(iommu_table_page_ptr),
        post.pt_mp.dom() == pre.pt_mp.dom().insert(pagetable_page_ptr),
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt)]
            pre.pt_mp.dom().contains(pt) ==> post.pt_mp.spec_index(pt) == pre.pt_mp.spec_index(pt),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_page_ptr).is_empty(),
        post.pt_mp.spec_index(pagetable_page_ptr).view().proc_ptr == process_page_ptr,
        post.prc_mp.spec_index(process_page_ptr).view().pagetable == pagetable_page_ptr,
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        post.ctn_mp.spec_index(container_ptr).killer_info() == pre.ctn_mp.spec_index(container_ptr).killer_info(),
        post.thr_mp.dom() == pre.thr_mp.dom(),
        post.thr_mp.spec_index(staging_thread_ptr).view() == (Thread {
            quota_4k: (pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 5) as usize,
            temp_alloc_cache_4k: Ghost(Set::empty()), ..pre.thr_mp.spec_index(staging_thread_ptr).view()
        }),
        post.thr_mp.spec_index(staging_thread_ptr).being_killed() == pre.thr_mp.spec_index(staging_thread_ptr).being_killed(),
        post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom(),
        post.it_mp.dom() == pre.it_mp.dom().insert(iommu_table_page_ptr),
        post.it_mp.spec_index(iommu_table_page_ptr).view().is_empty(),
        post.inv(),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    create_process_with_iommu_from_staged_pages_eof_subsystems_inv(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_with_iommu_from_staged_pages_eof_memory_management_inv(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    create_process_from_staged_pages_eof_process_management_inv(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, true, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

}

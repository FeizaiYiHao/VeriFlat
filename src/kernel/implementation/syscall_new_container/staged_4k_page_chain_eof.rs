use vstd::prelude::*;
use crate::*;

verus! {
/// Setting the staging link of one owned or free 4K page: only that page's `free_list` changes.
#[verifier::opaque]
pub(super) open spec fn set_4k_page_staging_next_eof_transition_framing(pre: KernelK, post: KernelK, page_ptr: PagePtr, next: PagePtr) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& post == (KernelK { pg_arr: post.pg_arr, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view() == (Page { free_list: next, ..old_page.view() })
}

/// The staging-link write keeps every page's state and owner, so each page keeps its object owner.
proof fn set_4k_page_staging_next_eof_page_object_owner(pre: KernelK, post: KernelK, page_ptr: PagePtr, next: PagePtr)
    requires
        pre.inv(),
        set_4k_page_staging_next_eof_transition_framing(pre, post, page_ptr, next),
        page_ptr_valid(page_ptr),
    ensures page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp),
{
    reveal(set_4k_page_staging_next_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid();
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); };
}

/// Closes every kernel invariant after the staging-link write from the entry invariants, the summary, and the
/// representation facts `set_4k_staging_next` guarantees.
pub(super) proof fn set_4k_page_staging_next_eof(pre: KernelK, post: KernelK, page_ptr: PagePtr, next: PagePtr)
    requires
        pre.inv(),
        set_4k_page_staging_next_eof_transition_framing(pre, post, page_ptr, next),
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k || pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Free4k,
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().inv(),
    ensures post.inv(),
{
    reveal(set_4k_page_staging_next_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    page_ptr_valid_imply_page_index_valid();
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(page_array_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, page_index);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(post.ctn_mp, post.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    set_4k_page_staging_next_eof_page_object_owner(pre, post, page_ptr, next);
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr);
    };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

/// The pages of an allocated staged chain belong to the owning container's owned pages, from the invariants after the chain.
pub(super) proof fn allocate_staged_4k_page_chain_eof_owned_pages(
    post: KernelK, lctx: &LocalContext, page_ptrs: Seq<PagePtr>, perms: Map<PagePtr, LockPerm>, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
)
    requires
        post.inv(),
        perms.dom() == page_ptrs.to_set(),
        allocated_4k_page_lock_perms_wf(perms, &post, lctx, thread_ptr, container_ptr),
    ensures page_ptrs.to_set().subset_of(post.ctn_mp.spec_index(container_ptr).view().owned_pages.view()),
{ page_ptrs.to_set_ensures(); page_ptr_roundtrip(); reveal(container_page_owner_wf); }
} // verus!

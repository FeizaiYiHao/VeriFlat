use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn eof_publish_postconditions(
    pre: KernelK, post: KernelK, pre_lctx: LocalContext, parent_container_ptr: RwLockContainerPtr,
    current_thread_ptr: RwLockThreadPtr, container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr,
    process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
    parent_container_lock_perm: LockPerm, current_thread_lock_perm: LockPerm,
    post_lctx: LocalContext, funding_page_lock_perms: Map<PagePtr, LockPerm>,
)
    requires
        typed_lock_maps_aligned(&pre, &pre_lctx),
        parent_container_lock_perm.lock_id() == pre.ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == pre.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        ),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& typed_lock_map_contains_mode(post_lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
    ensures
        post.cpu_tlb == pre.cpu_tlb,
        post.cpu_arr == pre.cpu_arr,
        post.pcid_needflush == pre.pcid_needflush,
        post.cpu_published == pre.cpu_published,
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom().insert(allocator_4k_page),
        post.allc_2m_mp.dom() == pre.allc_2m_mp.dom().insert(allocator_2m_page),
        post.allc_1g_mp.dom() == pre.allc_1g_mp.dom().insert(allocator_1g_page),
        post.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }),
        post.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }),
        post.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }),
        !post.ctn_mp.spec_index(container_page).being_killed(),
        post.ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_container_ptr),
        post.ctn_mp.spec_index(container_page).view_rodata().view().scheduler == scheduler_page,
        post.ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_4k == allocator_4k_page,
        post.ctn_mp.spec_index(container_page).view_ghost().owned_processes.view() == set![process_page],
        !post.prc_mp.spec_index(process_page).being_killed(),
        !post.prc_mp.spec_index(process_page).view().zombie,
        post.prc_mp.spec_index(process_page).view_rodata().view().owning_container == container_page,
        post.prc_mp.spec_index(process_page).view_rodata().view().pagetable == pagetable_page,
        post.prc_mp.spec_index(process_page).view().quota_4k == process_quota_4k,
        post.allc_4k_mp.spec_index(allocator_4k_page).owning_container == container_page,
        post.allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().view() == funding_pages,
        post.allc_4k_mp.spec_index(allocator_4k_page).total_free_pages.view() == funding_pages.len(),
        post.allc_4k_mp.spec_index(allocator_4k_page).quota.view().view() == allocator_quota_4k,
        post.pt_mp.spec_index(pagetable_page).view().is_empty(),
        post.pt_mp.spec_index(pagetable_page).view().proc_ptr == process_page,
        post.prc_mp.spec_index(process_page).view().iommu_table is None,
        post.ctn_mp.spec_index(container_page).view_ghost().uppertree_seq.view() == pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        post.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq == pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq,
        post.ctn_mp.spec_index(parent_container_ptr).view_rodata() == pre.ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_page).view_rodata().view().cpu_set == cpu_set_page,
        !post.sched_mp.spec_index(scheduler_page).being_killed(),
        post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page],
        post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g,
        post.thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_fields_equal(&pre.thr_mp.spec_index(current_thread_ptr).view(),),
        post.thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(current_thread_ptr).view().quota_4k,
            quota_2m: post.thr_mp.spec_index(current_thread_ptr).view().quota_2m,
            temp_alloc_cache_4k: post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k,
            temp_alloc_cache_2m: post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m,
            ..pre.thr_mp.spec_index(current_thread_ptr).view()
        }),
        post.thr_mp.spec_index(current_thread_ptr).view().owning_container == pre.thr_mp.spec_index(current_thread_ptr).view().owning_container,
        post.thr_mp.spec_index(current_thread_ptr).view().owning_proc == pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc,
        post.thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == pre.thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr,
        post.thr_mp.spec_index(current_thread_ptr).view().state == pre.thr_mp.spec_index(current_thread_ptr).view().state,
        post.thr_mp.spec_index(current_thread_ptr).being_killed() == pre.thr_mp.spec_index(current_thread_ptr).being_killed(),
        post.thr_mp.spec_index(current_thread_ptr).view().quota_4k == pre.thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8 - funding_pages.len(),
        post.thr_mp.spec_index(current_thread_ptr).view().quota_2m == pre.thr_mp.spec_index(current_thread_ptr).view().quota_2m - 2,
        post.pg_arr.spec_index(page_ptr2page_index(thread_page)) == pre.pg_arr.spec_index(page_ptr2page_index(thread_page)),
        post.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        post.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr,
        !post.ctn_mp.spec_index(parent_container_ptr).being_killed(),
        post.ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes == pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes,
        !post.ctn_mp.spec_index(container_page).view().owned_pages.view().contains(thread_page),
        post.pt_mp.dom().contains(pagetable_page),
        post.ctn_mp.dom().contains(parent_container_ptr),
        post.ctn_mp.dom().contains(container_page),
        post.prc_mp.dom().contains(process_page),
        post.thr_mp.dom().contains(current_thread_ptr),
        post.sched_mp.dom().contains(scheduler_page),
        post.cpu_set_mp.dom().contains(cpu_set_page),
        post.pcid_allc_mp.dom().contains(pcid_allocator_page),
        post.allc_4k_mp.dom().contains(allocator_4k_page),
        post.allc_2m_mp.dom().contains(allocator_2m_page),
        post.allc_1g_mp.dom().contains(allocator_1g_page),
        held_cpus_unchanged(pre.cpu_arr, post.cpu_arr, &pre_lctx),
        held_processes_unchanged(pre.prc_mp, post.prc_mp, &pre_lctx),
        held_pagetables_unchanged(pre.pt_mp, post.pt_mp, &pre_lctx),
        held_cpu_sets_unchanged(pre.cpu_set_mp, post.cpu_set_mp, &pre_lctx),
        post.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() == pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().difference(
            new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page,
                scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).union(funding_pages.to_set()),
        ),
        parent_container_lock_perm.lock_id() == post.ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == post.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        staged_4k_page_chain(post.pg_arr, funding_pages),
        post.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_4k_page), state: FreePageAllocatorState::GlobalList })
                &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(post_lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(staged_4k_page_chain(post.pg_arr, funding_pages)) by { broadcast use page_ptr_sequence_index_in_equal_set; };
    assert(held_cpus_unchanged(pre.cpu_arr, post.cpu_arr, &pre_lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(held_processes_unchanged(pre.prc_mp, post.prc_mp, &pre_lctx)) by {
        pre.prc_mp.typed_lock_map_aligned_held_in_dom(pre_lctx.process_lock_map(), pre_lctx.thread_id());
    };
    assert(held_pagetables_unchanged(pre.pt_mp, post.pt_mp, &pre_lctx)) by {
        pre.pt_mp.typed_lock_map_aligned_held_in_dom(pre_lctx.pagetable_lock_map(), pre_lctx.thread_id());
    };
    assert(held_cpu_sets_unchanged(pre.cpu_set_mp, post.cpu_set_mp, &pre_lctx)) by {
        pre.cpu_set_mp.typed_lock_map_aligned_held_in_dom(pre_lctx.cpu_set_lock_map(), pre_lctx.thread_id());
    };
}
}

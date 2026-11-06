use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::allocate_free_1g_page_pop_eof::pop_stage_1g_page_eof_transition_framing;

verus! {
pub(super) proof fn pop_stage_1g_page_eof_postconditions(pre: KernelK, post: KernelK, pre_lctx: LocalContext, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        !pre.thrd_mp.spec_index(thread).being_killed(),
        !pre.pg_arr.spec_index(page_ptr2page_index(page)).view().being_killed(),
        pop_stage_1g_page_eof_transition_framing(pre, post, allocator, thread, container, page, node),
        index_valid(NUM_PAGES, page_ptr2page_index(page)),
        pre.thrd_mp.dom().contains(thread),
        pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view().owning_container == container,
        post.thrd_mp.perms_wf(),
    ensures
        post.allc_1g_mp.unchanged_except(&pre.allc_1g_mp, allocator),
        post.allc_1g_mp.spec_index(allocator).quota == pre.allc_1g_mp.spec_index(allocator).quota,
        post == (KernelK { pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_1g_mp: post.allc_1g_mp, ..pre }),
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page)),
        held_pages_unchanged_except(pre.pg_arr, post.pg_arr, &pre_lctx, set![page_ptr2page_index(page)]),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post.thrd_mp.spec_index(thread).being_killed() == false,
        post.thrd_mp.spec_index(thread).view() == (Thread { temp_alloc_cache_1g: post.thrd_mp.spec_index(thread).view().temp_alloc_cache_1g, ..pre.thrd_mp.spec_index(thread).view() }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        held_threads_unchanged_except(pre.thrd_mp, post.thrd_mp, &pre_lctx, set![thread]),
        post.thrd_mp.lock_id_by_key(thread) == pre.thrd_mp.lock_id_by_key(thread),
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().being_killed() == false,
        post.thrd_mp.spec_index(thread).view().temp_alloc_cache_1g.view() =~= pre.thrd_mp.spec_index(thread).view().temp_alloc_cache_1g.view().insert(page),
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state == (PageState::Owned1g { thread_ptr: thread }),
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().owning_container == container,
{
    reveal(pop_stage_1g_page_eof_transition_framing);
    assert(post.thrd_mp.lock_id_by_key(thread) == pre.thrd_mp.lock_id_by_key(thread)) by { thread_perms_wf_at(pre.thrd_mp, thread); };
    pre.thrd_mp.typed_lock_map_aligned_held_in_dom(pre_lctx.thread_lock_map(), pre_lctx.thread_id());
    assert(held_pages_unchanged_except(pre.pg_arr, post.pg_arr, &pre_lctx, set![page_ptr2page_index(page)])) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        kernel_pagetable_nonlock_fields_unchanged_for_equal(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()); kernel_iommu_table_nonlock_fields_unchanged_for_equal(pre.it_mp, post.it_mp);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr); kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
}

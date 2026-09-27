use vstd::prelude::*;
use crate::*;
use super::allocate_free_2m_page_pop_eof::pop_stage_2m_page_transition_framing;

verus! {
pub(super) proof fn eof_pop_2m_postconditions(
    pre: KernelK, post: KernelK, pre_lctx: LocalContext, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        !pre.thr_mp.spec_index(thread).being_killed(),
        !pre.pg_arr.spec_index(page_ptr2page_index(page)).view().being_killed(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.thr_mp.perms_wf(),
    ensures
        page_ptr_valid(page),
        pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state is Free2m,
        !pre.thr_mp.spec_index(thread).view().temp_alloc_cache_2m.view().contains(page),
        post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allocator),
        post.allc_2m_mp.spec_index(allocator).quota == pre.allc_2m_mp.spec_index(allocator).quota,
        post == (KernelK { pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_2m_mp: post.allc_2m_mp, ..pre }),
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page)),
        held_pages_unchanged_except(pre.pg_arr, post.pg_arr, &pre_lctx, set![page_ptr2page_index(page)]),
        kernel_k_to_nonlock_kernel_u(post) == kernel_k_to_nonlock_kernel_u(pre),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post.thr_mp.spec_index(thread).being_killed() == false,
        post.thr_mp.spec_index(thread).view() == (Thread {
            temp_alloc_cache_2m: post.thr_mp.spec_index(thread).view().temp_alloc_cache_2m, ..pre.thr_mp.spec_index(thread).view()
        }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        held_threads_unchanged_except(pre.thr_mp, post.thr_mp, &pre_lctx, set![thread]),
        post.thr_mp.lock_id_by_key(thread) == pre.thr_mp.lock_id_by_key(thread),
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().being_killed() == false,
        post.thr_mp.spec_index(thread).view().temp_alloc_cache_2m.view() =~= pre.thr_mp.spec_index(thread).view().temp_alloc_cache_2m.view().insert(page),
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state == (PageState::Owned2m { thread_ptr: thread }),
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().owning_container == container,
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(post.thr_mp.lock_id_by_key(thread) == pre.thr_mp.lock_id_by_key(thread)) by { reveal(thread_perms_wf); };
    pre.thr_mp.typed_lock_map_aligned_held_in_dom(pre_lctx.thread_lock_map(), pre_lctx.thread_id());
    assert(held_pages_unchanged_except(pre.pg_arr, post.pg_arr, &pre_lctx, set![page_ptr2page_index(page)])) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        kernel_pagetable_nonlock_fields_unchanged_for_equal(pre.pt_mp, post.pt_mp);
        kernel_iommu_table_nonlock_fields_unchanged_for_equal(pre.it_mp, post.it_mp);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
    kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&pre, &post);
}
}

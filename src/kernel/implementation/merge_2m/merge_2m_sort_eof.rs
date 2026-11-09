#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_seqs_equal, assert_seqs_equal_internal};
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
use crate::*;

verus! {
pub open spec fn merge_2m_sort_eof_transition_framing(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, sorted_sources: usize) -> bool {
    let before = pre.allc_4k_mp.spec_index(allocator);
    let after = post.allc_4k_mp.spec_index(allocator);
    &&& sorted_sources <= NUM_CPUS + 1
    &&& post == (KernelK { allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator)
    &&& after.owning_container == before.owning_container
    &&& after.total_free_pages == before.total_free_pages
    &&& after.quota == before.quota
    &&& after.global_pool.is_init() == before.global_pool.is_init()
    &&& after.global_pool.view_rodata() == before.global_pool.view_rodata()
    &&& after.global_pool.view_ghost() == before.global_pool.view_ghost()
    &&& after.global_pool.locking_thread() == before.global_pool.locking_thread()
    &&& after.global_pool.control() == before.global_pool.control()
    &&& after.global_pool.view().line_pad == before.global_pool.view().line_pad
    &&& after.global_pool.view().linked_list.map() == before.global_pool.view().linked_list.map()
    &&& after.global_pool.view().linked_list.dom() == before.global_pool.view().linked_list.dom()
    &&& after.global_pool.view().linked_list.length == before.global_pool.view().linked_list.length
    &&& after.global_pool.view().linked_list.view().len() == before.global_pool.view().linked_list.view().len()
    &&& after.global_pool.view().linked_list.view().to_set() == before.global_pool.view().linked_list.view().to_set()
    &&& after.global_pool.view().linked_list.container_depth == before.global_pool.view().linked_list.container_depth
    &&& after.global_pool.view().linked_list.minor == before.global_pool.view().linked_list.minor
    &&& forall|page: PagePtr| #![trigger after.global_pool.view().view().contains(page)] #![trigger before.global_pool.view().view().contains(page)]
        after.global_pool.view().view().contains(page) == before.global_pool.view().view().contains(page)
    &&& sorted_sources <= NUM_CPUS ==> after.global_pool == before.global_pool
    &&& sorted_sources == NUM_CPUS + 1 ==> LinkedList::<PagePtr, 233>::values_sorted(after.global_pool.view().linked_list.view())
    &&& forall|cpu: CpuId| #![trigger after.cpu_caches.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> {
        let old_cache = before.cpu_caches.spec_index(cpu).view();
        let new_cache = after.cpu_caches.spec_index(cpu).view();
        &&& new_cache.is_init() == old_cache.is_init()
        &&& new_cache.view_rodata() == old_cache.view_rodata()
        &&& new_cache.view_ghost() == old_cache.view_ghost()
        &&& new_cache.locking_thread() == old_cache.locking_thread()
        &&& new_cache.control() == old_cache.control()
        &&& new_cache.view().line_pad == old_cache.view().line_pad
        &&& new_cache.view().linked_list.map() == old_cache.view().linked_list.map()
        &&& new_cache.view().linked_list.dom() == old_cache.view().linked_list.dom()
        &&& new_cache.view().linked_list.length == old_cache.view().linked_list.length
        &&& new_cache.view().linked_list.view().len() == old_cache.view().linked_list.view().len()
        &&& new_cache.view().linked_list.view().to_set() == old_cache.view().linked_list.view().to_set()
        &&& new_cache.view().linked_list.container_depth == old_cache.view().linked_list.container_depth
        &&& new_cache.view().linked_list.minor == old_cache.view().linked_list.minor
        &&& forall|page: PagePtr| #![trigger new_cache.view().view().contains(page)] #![trigger old_cache.view().view().contains(page)]
            new_cache.view().view().contains(page) == old_cache.view().view().contains(page)
        &&& cpu < sorted_sources ==> LinkedList::<PagePtr, 233>::values_sorted(new_cache.view().linked_list.view())
        &&& cpu >= sorted_sources ==> new_cache == old_cache
    }
}

pub proof fn merge_2m_sort_eof_implies_kernel_inv_and_alignment(pre: KernelK, post: KernelK, lctx: &LocalContext, allocator: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, lctx),
        pre.allc_4k_mp.dom().contains(allocator),
        merge_2m_sort_eof_transition_framing(pre, post, allocator, (NUM_CPUS + 1) as usize),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator).wf(),
        post.allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id()),
        post.allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id()),
        post.allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id()),
    ensures
        post.inv(),
        merge_2m_source_pages(post.allc_4k_mp.spec_index(allocator)) == merge_2m_source_pages(pre.allc_4k_mp.spec_index(allocator)),
        typed_lock_maps_aligned(&post, lctx),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(merge_2m_sort_eof_transition_framing);
    assert_seqs_equal!(Seq::new((NUM_CPUS + 1) as nat, |source: int| post.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source as usize).view().to_set()),
        Seq::new((NUM_CPUS + 1) as nat, |source: int| pre.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source as usize).view().to_set()));

    reveal(KernelK::inv);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_4k_pages_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { merge_2m_sort_eof_implies_free_4k_pages_wf(pre, post, allocator); };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { merge_2m_sort_eof_implies_quota_4k_wf(pre, post, allocator); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); };

    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}

pub proof fn merge_2m_sort_eof_implies_free_4k_pages_wf(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator),
        merge_2m_sort_eof_transition_framing(pre, post, allocator, (NUM_CPUS + 1) as usize),
    ensures allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    reveal(merge_2m_sort_eof_transition_framing);
    reveal(KernelK::inv);
    reveal(allocator_free_4k_pages_wf);
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_global_pool_4k_pages_wf); };
    assert(allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_cpu_cache_4k_pages_wf); };
}

pub proof fn merge_2m_sort_eof_implies_quota_4k_wf(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator),
        merge_2m_sort_eof_transition_framing(pre, post, allocator, (NUM_CPUS + 1) as usize),
    ensures container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp),
{
    reveal(merge_2m_sort_eof_transition_framing);
    reveal(KernelK::inv);
    reveal(container_process_allocator_quota_4k_wf);
    reveal(container_allocator_wf);
}

}

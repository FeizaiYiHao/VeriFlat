#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scan::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_spec::*;

verus! {
pub proof fn merge_2m_commit_eof_implies_allocator_page_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
        !pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().map().dom().contains(pre.pg_arr.spec_index(candidate.head).view().view().free_list_node_storage.addr()),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_array_wf(post.pg_arr),
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(post.allc_2m_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_4k_pages_wf); };
    assert(allocator_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_2m_pages_wf); };
    assert(allocator_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_1g_pages_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by {
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by {
        reveal(allocator_free_page_ptrs_wf);
        page_index_valid_implies_page_ptr_valid();
    };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
        page_ptr_roundtrip(); page_index_roundtrip(); page_ptr_valid_implies_page_index_valid();
    };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
        reveal(page_array_wf);
        allocator_free_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, candidate.head);
        reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
        page_index_roundtrip();
    };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by {
        reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
        page_ptr_valid_implies_page_index_valid();
    };
}

pub proof fn merge_2m_commit_eof_implies_allocator_quota_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_4k >= 512,
        pre.thrd_mp.spec_index(thread).view().quota_2m < usize::MAX,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
    ensures
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
        one_member_changed_implies_thread_effective_quota_4k_fold_sum_changed_by_forall(thread, -512); unchanged_members_implies_thread_effective_quota_4k_fold_sum_eq_forall();
        unchanged_thread_pending_4k_implies_per_container_pending_4k_fold_sums_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
        one_member_changed_implies_thread_effective_quota_2m_fold_sum_changed_by_forall(thread, 1); unchanged_members_implies_thread_effective_quota_2m_fold_sum_eq_forall();
        unchanged_thread_pending_2m_implies_per_container_pending_2m_fold_sums_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
        unchanged_members_implies_thread_effective_quota_1g_fold_sum_eq_forall(); unchanged_thread_pending_1g_implies_per_container_pending_1g_fold_sums_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
}

pub proof fn merge_2m_commit_eof_implies_allocator_and_quota_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_4k >= 512,
        pre.thrd_mp.spec_index(thread).view().quota_2m < usize::MAX,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
        !pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().map().dom().contains(pre.pg_arr.spec_index(candidate.head).view().view().free_list_node_storage.addr()),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_array_wf(post.pg_arr),
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    merge_2m_commit_eof_implies_allocator_page_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
    merge_2m_commit_eof_implies_allocator_quota_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
}
}

use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn create_process_from_staged_pages_eof_allocator_quota_4k_wf(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
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
        pre.thr_mp.spec_index(staging_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        create_process_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
    ensures
        container_process_allocator_quota_4k_wf(
            post.ctn_mp,
            post.prc_mp,
            post.thr_mp,
            post.allc_4k_mp,
        ),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by {
        reveal(KernelK::inv);
        reveal(KernelK::process_management_inv);
    };
    assert(container_thread_wf(pre.ctn_mp, pre.thr_mp)) by {
        reveal(KernelK::inv);
        reveal(KernelK::process_management_inv);
    };
    assert(container_process_allocator_quota_4k_wf(
        pre.ctn_mp,
        pre.prc_mp,
        pre.thr_mp,
        pre.allc_4k_mp,
    )) by {
        reveal(KernelK::inv);
        reveal(KernelK::memory_management_inv);
        reveal(container_process_allocator_quota_wf);
    };
    assert(container_process_allocator_quota_4k_wf(
        post.ctn_mp,
        post.prc_mp,
        pre.thr_mp,
        post.allc_4k_mp,
    )) by {
        let old_target_owned =
            pre.ctn_mp.spec_index(container_ptr).view().owned_processes.view();
        let pre_value = |p_ptr: RwLockProcessPtr|
            process_effective_quota_4k(pre.prc_mp.spec_index(p_ptr));
        let post_value = |p_ptr: RwLockProcessPtr|
            process_effective_quota_4k(post.prc_mp.spec_index(p_ptr));
        reveal(container_process_wf);
        lemma_set_fold_int_sum_insert_zero(
            old_target_owned,
            pre_value,
            post_value,
            process_page_ptr,
        );
        let pre_fold =
            |sum: int, p_ptr: RwLockProcessPtr| sum + pre_value(p_ptr);
        let post_fold =
            |sum: int, p_ptr: RwLockProcessPtr| sum + post_value(p_ptr);
        let direct_pre_fold = |sum: int, p_ptr: RwLockProcessPtr|
            sum + process_effective_quota_4k(pre.prc_mp.spec_index(p_ptr));
        let direct_post_fold = |sum: int, p_ptr: RwLockProcessPtr|
            sum + process_effective_quota_4k(post.prc_mp.spec_index(p_ptr));
        assert(pre_fold =~= direct_pre_fold);
        assert(post_fold =~= direct_post_fold);
        assert(process_effective_quota_4k_fold_sum(
            old_target_owned.insert(process_page_ptr),
            post.prc_mp,
        ) == process_effective_quota_4k_fold_sum(
            old_target_owned,
            pre.prc_mp,
        )) by {
            reveal(process_effective_quota_4k_fold_sum);
        };
        lemma_process_effective_quota_4k_fold_sum_eq_forall();
        reveal(container_process_allocator_quota_4k_wf);
        reveal(process_effective_quota_4k);
        reveal(process_effective_quota_4k_fold_sum);
        reveal(LockedMap::unchanged_except);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_quota_4k_fields_unchanged(pre.thr_mp, post.thr_mp)) by {
        let old_staged_pages = pre.thr_mp.spec_index(staging_thread_ptr)
            .view().temp_alloc_cache_4k.view();
        lemma_set_ext_equal_three_distinct_len(
            old_staged_pages,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
        );
        assert(thread_effective_quota_4k(
            post.thr_mp.spec_index(staging_thread_ptr),
        ) == thread_effective_quota_4k(
            pre.thr_mp.spec_index(staging_thread_ptr),
        )) by {
            reveal(thread_effective_quota_4k);
        };
        reveal(thread_quota_4k_fields_unchanged);
        reveal(thread_effective_quota_4k);
        reveal(LockedMap::unchanged_except);
    };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by {
        reveal(container_thread_wf);
        reveal(LockedMap::unchanged_except);
    };
    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
        post.ctn_mp,
        post.prc_mp,
        pre.thr_mp,
        post.thr_mp,
        post.allc_4k_mp,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn create_process_from_staged_pages_eof_allocator_quota_2m_wf(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        create_process_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
    ensures
        container_process_allocator_quota_2m_wf(
            post.ctn_mp,
            post.prc_mp,
            post.thr_mp,
            post.allc_2m_mp,
        ),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by {
        reveal(KernelK::inv);
        reveal(KernelK::process_management_inv);
    };
    assert(container_thread_wf(pre.ctn_mp, pre.thr_mp)) by {
        reveal(KernelK::inv);
        reveal(KernelK::process_management_inv);
    };
    assert(container_process_allocator_quota_2m_wf(
        pre.ctn_mp,
        pre.prc_mp,
        pre.thr_mp,
        pre.allc_2m_mp,
    )) by {
        reveal(KernelK::inv);
        reveal(KernelK::memory_management_inv);
        reveal(container_process_allocator_quota_wf);
    };
    assert(container_process_allocator_quota_2m_wf(
        post.ctn_mp,
        post.prc_mp,
        pre.thr_mp,
        post.allc_2m_mp,
    )) by {
        let old_target_owned =
            pre.ctn_mp.spec_index(container_ptr).view().owned_processes.view();
        let pre_value = |p_ptr: RwLockProcessPtr|
            process_effective_quota_2m(pre.prc_mp.spec_index(p_ptr));
        let post_value = |p_ptr: RwLockProcessPtr|
            process_effective_quota_2m(post.prc_mp.spec_index(p_ptr));
        reveal(container_process_wf);
        lemma_set_fold_int_sum_insert_zero(
            old_target_owned,
            pre_value,
            post_value,
            process_page_ptr,
        );
        let pre_fold =
            |sum: int, p_ptr: RwLockProcessPtr| sum + pre_value(p_ptr);
        let post_fold =
            |sum: int, p_ptr: RwLockProcessPtr| sum + post_value(p_ptr);
        let direct_pre_fold = |sum: int, p_ptr: RwLockProcessPtr|
            sum + process_effective_quota_2m(pre.prc_mp.spec_index(p_ptr));
        let direct_post_fold = |sum: int, p_ptr: RwLockProcessPtr|
            sum + process_effective_quota_2m(post.prc_mp.spec_index(p_ptr));
        assert(pre_fold =~= direct_pre_fold);
        assert(post_fold =~= direct_post_fold);
        assert(process_effective_quota_2m_fold_sum(
            old_target_owned.insert(process_page_ptr),
            post.prc_mp,
        ) == process_effective_quota_2m_fold_sum(
            old_target_owned,
            pre.prc_mp,
        )) by {
            reveal(process_effective_quota_2m_fold_sum);
        };
        lemma_process_effective_quota_2m_fold_sum_eq_forall();
        reveal(container_process_allocator_quota_2m_wf);
        reveal(process_effective_quota_2m);
        reveal(process_effective_quota_2m_fold_sum);
        reveal(LockedMap::unchanged_except);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_quota_2m_fields_unchanged(pre.thr_mp, post.thr_mp)) by {
        reveal(thread_quota_2m_fields_unchanged);
        reveal(thread_effective_quota_2m);
        reveal(LockedMap::unchanged_except);
    };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by {
        reveal(container_thread_wf);
        reveal(LockedMap::unchanged_except);
    };
    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
        post.ctn_mp,
        post.prc_mp,
        pre.thr_mp,
        post.thr_mp,
        post.allc_2m_mp,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn create_process_from_staged_pages_eof_allocator_quota_1g_wf(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        create_process_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
    ensures
        container_process_allocator_quota_1g_wf(
            post.ctn_mp,
            post.prc_mp,
            post.thr_mp,
            post.allc_1g_mp,
        ),
{
    reveal(create_process_from_staged_pages_kernel_state_framing);
    assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by {
        reveal(KernelK::inv);
        reveal(KernelK::process_management_inv);
    };
    assert(container_thread_wf(pre.ctn_mp, pre.thr_mp)) by {
        reveal(KernelK::inv);
        reveal(KernelK::process_management_inv);
    };
    assert(container_process_allocator_quota_1g_wf(
        pre.ctn_mp,
        pre.prc_mp,
        pre.thr_mp,
        pre.allc_1g_mp,
    )) by {
        reveal(KernelK::inv);
        reveal(KernelK::memory_management_inv);
        reveal(container_process_allocator_quota_wf);
    };
    assert(container_process_allocator_quota_1g_wf(
        post.ctn_mp,
        post.prc_mp,
        pre.thr_mp,
        post.allc_1g_mp,
    )) by {
        let old_target_owned =
            pre.ctn_mp.spec_index(container_ptr).view().owned_processes.view();
        let pre_value = |p_ptr: RwLockProcessPtr|
            process_effective_quota_1g(pre.prc_mp.spec_index(p_ptr));
        let post_value = |p_ptr: RwLockProcessPtr|
            process_effective_quota_1g(post.prc_mp.spec_index(p_ptr));
        reveal(container_process_wf);
        lemma_set_fold_int_sum_insert_zero(
            old_target_owned,
            pre_value,
            post_value,
            process_page_ptr,
        );
        let pre_fold =
            |sum: int, p_ptr: RwLockProcessPtr| sum + pre_value(p_ptr);
        let post_fold =
            |sum: int, p_ptr: RwLockProcessPtr| sum + post_value(p_ptr);
        let direct_pre_fold = |sum: int, p_ptr: RwLockProcessPtr|
            sum + process_effective_quota_1g(pre.prc_mp.spec_index(p_ptr));
        let direct_post_fold = |sum: int, p_ptr: RwLockProcessPtr|
            sum + process_effective_quota_1g(post.prc_mp.spec_index(p_ptr));
        assert(pre_fold =~= direct_pre_fold);
        assert(post_fold =~= direct_post_fold);
        assert(process_effective_quota_1g_fold_sum(
            old_target_owned.insert(process_page_ptr),
            post.prc_mp,
        ) == process_effective_quota_1g_fold_sum(
            old_target_owned,
            pre.prc_mp,
        )) by {
            reveal(process_effective_quota_1g_fold_sum);
        };
        lemma_process_effective_quota_1g_fold_sum_eq_forall();
        reveal(container_process_allocator_quota_1g_wf);
        reveal(process_effective_quota_1g);
        reveal(process_effective_quota_1g_fold_sum);
        reveal(LockedMap::unchanged_except);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_quota_1g_fields_unchanged(pre.thr_mp, post.thr_mp)) by {
        reveal(thread_quota_1g_fields_unchanged);
        reveal(thread_effective_quota_1g);
        reveal(LockedMap::unchanged_except);
    };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by {
        reveal(container_thread_wf);
        reveal(LockedMap::unchanged_except);
    };
    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
        post.ctn_mp,
        post.prc_mp,
        pre.thr_mp,
        post.thr_mp,
        post.allc_1g_mp,
    );
}


}

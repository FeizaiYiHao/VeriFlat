use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_allocator_quota_2m_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        container_page != pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp,),
{
    assert(container_process_allocator_quota_2m_wf(pre.ctn_mp, pre.prc_mp, pre.thr_mp, pre.allc_2m_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(container_process_allocator_quota_wf); };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_2m_mp,)) by {
        assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
        assert(container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
        reveal(publish_staged_container_root_kernel_state_framing);
        assert(process_effective_quota_2m_fold_sum(post.ctn_mp.spec_index(container_page).view().owned_processes.view(), post.prc_mp,) == 0) by {
            let child_processes = post.ctn_mp.spec_index(container_page).view().owned_processes.view();
            let value = |p_ptr: RwLockProcessPtr|
                process_effective_quota_2m(post.prc_mp.spec_index(p_ptr));
            lemma_set_fold_int_sum_singleton(child_processes, process_page, value,);
            let fold = |sum: int, p_ptr: RwLockProcessPtr| sum + value(p_ptr);
            let direct_fold = |sum: int, p_ptr: RwLockProcessPtr|
                sum + process_effective_quota_2m(post.prc_mp.spec_index(p_ptr));
            assert(fold =~= direct_fold);
            reveal(process_effective_quota_2m);
            reveal(process_effective_quota_2m_fold_sum);
        };
        assert(thread_effective_quota_2m_fold_sum(post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view(), pre.thr_mp,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
            let value = |t_ptr: RwLockThreadPtr|
                thread_effective_quota_2m(pre.thr_mp.spec_index(t_ptr));
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + thread_effective_quota_2m(pre.thr_mp.spec_index(t_ptr));
            assert(fold =~= direct_fold);
            reveal(thread_effective_quota_2m_fold_sum);
        };
        assert(thread_direct_pending_2m_fold_sum(post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view(), pre.thr_mp,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
            let value = |t_ptr: RwLockThreadPtr|
                pre.thr_mp.spec_index(t_ptr).view().direct_free_quota_pending_2m.view() as int;
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + pre.thr_mp.spec_index(t_ptr).view().direct_free_quota_pending_2m.view();
            assert(fold =~= direct_fold);
            reveal(thread_direct_pending_2m_fold_sum);
        };
        assert(thread_indirect_pending_2m_fold_sum_at_depth(post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view(), pre.thr_mp, post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view();
            let depth = post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int;
            let value = |t_ptr: RwLockThreadPtr|
                pre.thr_mp.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + pre.thr_mp.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth);
            assert(fold =~= direct_fold);
            reveal(thread_indirect_pending_2m_fold_sum_at_depth);
        };
        reveal(container_process_allocator_quota_2m_wf);
        reveal(container_process_wf);
        reveal(container_allocator_wf);
        reveal(process_effective_quota_2m);
        reveal(process_effective_quota_2m_fold_sum);
        lemma_process_effective_quota_2m_fold_sum_eq_forall();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_quota_2m_fields_unchanged(pre.thr_mp, post.thr_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_thread_wf); };
    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp,);
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_allocator_quota_1g_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(current_thread_ptr),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        forall|staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr)]
            #![trigger funding_pages.to_set().contains(staged_page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(staged_page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(staged_page_ptr) || funding_pages.to_set().contains(staged_page_ptr) || staged_page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp,),
{
    assert(container_process_allocator_quota_1g_wf(pre.ctn_mp, pre.prc_mp, pre.thr_mp, pre.allc_1g_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(container_process_allocator_quota_wf); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_1g_mp,)) by {
        assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
        assert(container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
        reveal(publish_staged_container_root_kernel_state_framing);
        assert(process_effective_quota_1g_fold_sum(post.ctn_mp.spec_index(container_page).view().owned_processes.view(), post.prc_mp,) == 0) by {
            let child_processes = post.ctn_mp.spec_index(container_page).view().owned_processes.view();
            let value = |p_ptr: RwLockProcessPtr|
                process_effective_quota_1g(post.prc_mp.spec_index(p_ptr));
            lemma_set_fold_int_sum_singleton(child_processes, process_page, value,);
            let fold = |sum: int, p_ptr: RwLockProcessPtr| sum + value(p_ptr);
            let direct_fold = |sum: int, p_ptr: RwLockProcessPtr|
                sum + process_effective_quota_1g(post.prc_mp.spec_index(p_ptr));
            assert(fold =~= direct_fold);
            reveal(process_effective_quota_1g);
            reveal(process_effective_quota_1g_fold_sum);
        };
        assert(thread_effective_quota_1g_fold_sum(post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view(), pre.thr_mp,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
            let value = |t_ptr: RwLockThreadPtr|
                thread_effective_quota_1g(pre.thr_mp.spec_index(t_ptr));
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + thread_effective_quota_1g(pre.thr_mp.spec_index(t_ptr));
            assert(fold =~= direct_fold);
            reveal(thread_effective_quota_1g_fold_sum);
        };
        assert(thread_direct_pending_1g_fold_sum(post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view(), pre.thr_mp,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
            let value = |t_ptr: RwLockThreadPtr|
                pre.thr_mp.spec_index(t_ptr).view().direct_free_quota_pending_1g.view() as int;
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + pre.thr_mp.spec_index(t_ptr).view().direct_free_quota_pending_1g.view();
            assert(fold =~= direct_fold);
            reveal(thread_direct_pending_1g_fold_sum);
        };
        assert(thread_indirect_pending_1g_fold_sum_at_depth(post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view(), pre.thr_mp, post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view();
            let depth = post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int;
            let value = |t_ptr: RwLockThreadPtr|
                pre.thr_mp.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + pre.thr_mp.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth);
            assert(fold =~= direct_fold);
            reveal(thread_indirect_pending_1g_fold_sum_at_depth);
        };
        reveal(container_process_allocator_quota_1g_wf);
        reveal(container_process_wf);
        reveal(container_allocator_wf);
        reveal(process_effective_quota_1g);
        reveal(process_effective_quota_1g_fold_sum);
        lemma_process_effective_quota_1g_fold_sum_eq_forall();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_quota_1g_fields_unchanged(pre.thr_mp, post.thr_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_thread_wf); };
    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp,);
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_allocator_quota_4k_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp,),
{
    assert(container_process_allocator_quota_4k_wf(pre.ctn_mp, pre.prc_mp, pre.thr_mp, pre.allc_4k_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(container_process_allocator_quota_wf); };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_4k_mp,)) by {
        assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
        assert(container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
        reveal(publish_staged_container_root_kernel_state_framing);
        assert(process_effective_quota_4k_fold_sum(post.ctn_mp.spec_index(container_page).view().owned_processes.view(), post.prc_mp,) == process_quota_4k) by {
            let child_processes = post.ctn_mp.spec_index(container_page).view().owned_processes.view();
            let value = |p_ptr: RwLockProcessPtr|
                process_effective_quota_4k(post.prc_mp.spec_index(p_ptr));
            lemma_set_fold_int_sum_singleton(child_processes, process_page, value,);
            let fold = |sum: int, p_ptr: RwLockProcessPtr| sum + value(p_ptr);
            let direct_fold = |sum: int, p_ptr: RwLockProcessPtr|
                sum + process_effective_quota_4k(post.prc_mp.spec_index(p_ptr));
            assert(fold =~= direct_fold);
            reveal(process_effective_quota_4k);
            reveal(process_effective_quota_4k_fold_sum);
        };
        assert(thread_effective_quota_4k_fold_sum(post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view(), pre.thr_mp,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
            let value = |t_ptr: RwLockThreadPtr|
                thread_effective_quota_4k(pre.thr_mp.spec_index(t_ptr));
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + thread_effective_quota_4k(pre.thr_mp.spec_index(t_ptr));
            assert(fold =~= direct_fold);
            reveal(thread_effective_quota_4k_fold_sum);
        };
        assert(thread_direct_pending_4k_fold_sum(post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view(), pre.thr_mp,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
            let value = |t_ptr: RwLockThreadPtr|
                pre.thr_mp.spec_index(t_ptr).view().direct_free_quota_pending_4k.view() as int;
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + pre.thr_mp.spec_index(t_ptr).view().direct_free_quota_pending_4k.view();
            assert(fold =~= direct_fold);
            reveal(thread_direct_pending_4k_fold_sum);
        };
        assert(thread_indirect_pending_4k_fold_sum_at_depth(post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view(), pre.thr_mp, post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int,) == 0) by {
            let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view();
            let depth = post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int;
            let value = |t_ptr: RwLockThreadPtr|
                pre.thr_mp.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
            lemma_set_fold_int_sum_empty(child_threads, value);
            let fold = |sum: int, t_ptr: RwLockThreadPtr| sum + value(t_ptr);
            let direct_fold = |sum: int, t_ptr: RwLockThreadPtr|
                sum + pre.thr_mp.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth);
            assert(fold =~= direct_fold);
            reveal(thread_indirect_pending_4k_fold_sum_at_depth);
        };
        reveal(container_process_allocator_quota_4k_wf);
        reveal(container_process_wf);
        reveal(container_allocator_wf);
        reveal(process_effective_quota_4k);
        reveal(process_effective_quota_4k_fold_sum);
        lemma_process_effective_quota_4k_fold_sum_eq_forall();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_quota_4k_fields_unchanged(pre.thr_mp, post.thr_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(container_thread_wf(post.ctn_mp, pre.thr_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_thread_wf); };
    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp,);
}


}

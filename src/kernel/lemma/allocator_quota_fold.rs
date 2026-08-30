use vstd::prelude::*;
use crate::*;

verus! {

/// Preserve 2M quota conservation across a process-map mutation that leaves
/// every process's 2M effective quota unchanged.
pub proof fn container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(
    container_map: ContainerLockedMap,
    thread_map: ThreadLockedMap,
    allocator_2m_map: PageAllocatorUnLockedMap,
    old_process_map: ProcessLockedMap,
    new_process_map: ProcessLockedMap,
)
    requires
        container_process_allocator_quota_2m_wf(
            container_map, old_process_map, thread_map, allocator_2m_map,
        ),
        container_process_wf(container_map, old_process_map),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_2m(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==>
                process_effective_quota_2m(new_process_map.spec_index(p))
                    == process_effective_quota_2m(old_process_map.spec_index(p)),
    ensures
        container_process_allocator_quota_2m_wf(
            container_map, new_process_map, thread_map, allocator_2m_map,
        ),
{
    assert(container_process_allocator_quota_2m_wf(
        container_map, new_process_map, thread_map, allocator_2m_map,
    )) by {
        reveal(container_process_allocator_quota_2m_wf);
        reveal(container_process_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
            container_map.dom().contains(c_ptr)
        implies
            container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(new_process_map.spec_index(p_ptr))})
                + thread_effective_quota_2m_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    thread_map,
                )
                + container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                + container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                + allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                == allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
        by {
            assert(container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(old_process_map.dom())) by {
                reveal(container_process_wf);
            };
            lemma_process_effective_quota_2m_fold_eq(
                container_map.spec_index(c_ptr).view().owned_processes.view(),
                old_process_map, new_process_map);
        };
    };
}

/// Preserve 1G quota conservation across a process-map mutation that leaves
/// every process's 1G effective quota unchanged.
pub proof fn container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(
    container_map: ContainerLockedMap,
    thread_map: ThreadLockedMap,
    allocator_1g_map: PageAllocatorUnLockedMap,
    old_process_map: ProcessLockedMap,
    new_process_map: ProcessLockedMap,
)
    requires
        container_process_allocator_quota_1g_wf(
            container_map, old_process_map, thread_map, allocator_1g_map,
        ),
        container_process_wf(container_map, old_process_map),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_1g(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==>
                process_effective_quota_1g(new_process_map.spec_index(p))
                    == process_effective_quota_1g(old_process_map.spec_index(p)),
    ensures
        container_process_allocator_quota_1g_wf(
            container_map, new_process_map, thread_map, allocator_1g_map,
        ),
{
    assert(container_process_allocator_quota_1g_wf(
        container_map, new_process_map, thread_map, allocator_1g_map,
    )) by {
        reveal(container_process_allocator_quota_1g_wf);
        reveal(container_process_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
            container_map.dom().contains(c_ptr)
        implies
            container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_1g(new_process_map.spec_index(p_ptr))})
                + thread_effective_quota_1g_fold_sum(
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                    thread_map,
                )
                + container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                + container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                + allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                == allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
        by {
            assert(container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(old_process_map.dom())) by {
                reveal(container_process_wf);
            };
            lemma_process_effective_quota_1g_fold_eq(
                container_map.spec_index(c_ptr).view().owned_processes.view(),
                old_process_map, new_process_map);
        };
    };
}

/// Forall-wrapped `lemma_process_effective_quota_4k_fold_eq`, triggered on the
/// `process_effective_quota_4k_fold_sum` terms so it fires directly off a
/// revealed `container_process_allocator_quota_4k_wf`.
pub proof fn lemma_process_effective_quota_4k_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_4k_fold_sum(s, post), process_effective_quota_4k_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
            ==>
            process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|  #![auto]
        (forall|p: RwLockProcessPtr|  #![auto]
            s.contains(p) ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
    implies
        process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre)
    by {
        lemma_process_effective_quota_4k_fold_eq(s, pre, post);
    };
}

pub proof fn lemma_process_effective_quota_2m_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_2m_fold_sum(s, post), process_effective_quota_2m_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_2m(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_2m(post.spec_index(p)) == process_effective_quota_2m(pre.spec_index(p)))
            ==>
            process_effective_quota_2m_fold_sum(s, post) == process_effective_quota_2m_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (forall|p: RwLockProcessPtr| #![auto]
            s.contains(p) ==> process_effective_quota_2m(post.spec_index(p)) == process_effective_quota_2m(pre.spec_index(p)))
    implies
        process_effective_quota_2m_fold_sum(s, post) == process_effective_quota_2m_fold_sum(s, pre)
    by {
        lemma_process_effective_quota_2m_fold_eq(s, pre, post);
    };
}

pub proof fn lemma_process_effective_quota_1g_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_1g_fold_sum(s, post), process_effective_quota_1g_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_1g(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_1g(post.spec_index(p)) == process_effective_quota_1g(pre.spec_index(p)))
            ==>
            process_effective_quota_1g_fold_sum(s, post) == process_effective_quota_1g_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (forall|p: RwLockProcessPtr| #![auto]
            s.contains(p) ==> process_effective_quota_1g(post.spec_index(p)) == process_effective_quota_1g(pre.spec_index(p)))
    implies
        process_effective_quota_1g_fold_sum(s, post) == process_effective_quota_1g_fold_sum(s, pre)
    by {
        lemma_process_effective_quota_1g_fold_eq(s, pre, post);
    };
}

/// Forall-wrapped `lemma_process_effective_quota_4k_fold_change_by`, triggered on
/// the `process_effective_quota_4k_fold_sum` terms so it fires directly off a
/// revealed `container_process_allocator_quota_4k_wf`. `mod_p`/`x` are params
/// (the delta `x` can only appear additively in the conclusion, so it cannot be
/// trigger-bound).
pub proof fn lemma_process_effective_quota_4k_fold_change_by_forall(mod_p: RwLockProcessPtr, x: int)
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_4k_fold_sum(s, post), process_effective_quota_4k_fold_sum(s, pre)]
            (s.contains(mod_p)
            && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x
            && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(pre.spec_index(p))]
                s.contains(p) && p != mod_p ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
            ==>
            process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|  #![auto]
        (s.contains(mod_p)
        && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x
        && forall|p: RwLockProcessPtr|  #![auto]
            s.contains(p) && p != mod_p ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
    implies
        process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre) + x
    by {
        lemma_process_effective_quota_4k_fold_change_by(s, pre, post, mod_p, x);
    };
}

pub proof fn lemma_thread_effective_quota_4k_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_4k_fold_sum(s, post), thread_effective_quota_4k_fold_sum(s, pre)]
            (forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_4k(pre.spec_index(t))]
                s.contains(t) ==> thread_effective_quota_4k(post.spec_index(t))
                    == thread_effective_quota_4k(pre.spec_index(t)))
            ==> thread_effective_quota_4k_fold_sum(s, post)
                == thread_effective_quota_4k_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (forall|t: RwLockThreadPtr| #![auto]
            s.contains(t) ==> thread_effective_quota_4k(post.spec_index(t))
                == thread_effective_quota_4k(pre.spec_index(t)))
        implies thread_effective_quota_4k_fold_sum(s, post)
            == thread_effective_quota_4k_fold_sum(s, pre)
    by {
        lemma_thread_effective_quota_4k_fold_eq(s, pre, post);
    };
}
pub proof fn lemma_thread_effective_quota_4k_fold_change_by_forall(
    mod_t: RwLockThreadPtr,
    x: int,
)
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_4k_fold_sum(s, post), thread_effective_quota_4k_fold_sum(s, pre)]
            (s.contains(mod_t)
            && thread_effective_quota_4k(post.spec_index(mod_t))
                == thread_effective_quota_4k(pre.spec_index(mod_t)) + x
            && forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_4k(pre.spec_index(t))]
                s.contains(t) && t != mod_t ==> thread_effective_quota_4k(post.spec_index(t))
                    == thread_effective_quota_4k(pre.spec_index(t)))
            ==> thread_effective_quota_4k_fold_sum(s, post)
                == thread_effective_quota_4k_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (s.contains(mod_t)
        && thread_effective_quota_4k(post.spec_index(mod_t))
            == thread_effective_quota_4k(pre.spec_index(mod_t)) + x
        && forall|t: RwLockThreadPtr| #![auto]
            s.contains(t) && t != mod_t ==> thread_effective_quota_4k(post.spec_index(t))
                == thread_effective_quota_4k(pre.spec_index(t)))
        implies thread_effective_quota_4k_fold_sum(s, post)
            == thread_effective_quota_4k_fold_sum(s, pre) + x
    by {
        lemma_thread_effective_quota_4k_fold_change_by(s, pre, post, mod_t, x);
    };
}

pub proof fn lemma_container_thread_quota_folds_insert_zero_forall(
    pre_ctn: ContainerLockedMap,
    post_ctn: ContainerLockedMap,
    pre_thr: ThreadLockedMap,
    post_thr: ThreadLockedMap,
    dc: RwLockContainerPtr,
    new_t: RwLockThreadPtr,
    uppers: Set<RwLockContainerPtr>,
)
    requires
        container_thread_wf(pre_ctn, pre_thr),
        pre_ctn.dom().contains(dc),
        post_ctn.dom() == pre_ctn.dom(),
        post_ctn.spec_index(dc).view_user_ghost().owned_threads.view() =~= pre_ctn.spec_index(dc).view_user_ghost().owned_threads.view().insert(new_t),
        forall|c: RwLockContainerPtr|
            #![trigger pre_ctn.spec_index(c).view_user_ghost().owned_threads]
            #![trigger post_ctn.spec_index(c).view_user_ghost().owned_threads]
            pre_ctn.dom().contains(c) && c != dc ==>
                post_ctn.spec_index(c).view_user_ghost().owned_threads == pre_ctn.spec_index(c).view_user_ghost().owned_threads,
        forall|c: RwLockContainerPtr|
            #![trigger pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            #![trigger post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            uppers.contains(c) ==>
                post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view() =~= pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(new_t),
        forall|c: RwLockContainerPtr|
            #![trigger pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            #![trigger post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            pre_ctn.dom().contains(c) && !uppers.contains(c) ==>
                post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads == pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads,
        forall|c: RwLockContainerPtr| #![auto]
            pre_ctn.dom().contains(c) ==>
                post_ctn.spec_index(c).view() == pre_ctn.spec_index(c).view()
                && post_ctn.spec_index(c).view_rodata() == pre_ctn.spec_index(c).view_rodata(),
        !pre_thr.dom().contains(new_t),
        forall|t: RwLockThreadPtr|
            #![trigger post_thr.spec_index(t).view()]
            pre_thr.dom().contains(t) ==>
                thread_effective_quota_4k(post_thr.spec_index(t)) == thread_effective_quota_4k(pre_thr.spec_index(t))
                && thread_effective_quota_2m(post_thr.spec_index(t)) == thread_effective_quota_2m(pre_thr.spec_index(t))
                && thread_effective_quota_1g(post_thr.spec_index(t)) == thread_effective_quota_1g(pre_thr.spec_index(t))
                && post_thr.spec_index(t).view().direct_free_quota_pending_4k == pre_thr.spec_index(t).view().direct_free_quota_pending_4k
                && post_thr.spec_index(t).view().direct_free_quota_pending_2m == pre_thr.spec_index(t).view().direct_free_quota_pending_2m
                && post_thr.spec_index(t).view().direct_free_quota_pending_1g == pre_thr.spec_index(t).view().direct_free_quota_pending_1g
                && post_thr.spec_index(t).view().indirect_free_quota_pending_4k == pre_thr.spec_index(t).view().indirect_free_quota_pending_4k
                && post_thr.spec_index(t).view().indirect_free_quota_pending_2m == pre_thr.spec_index(t).view().indirect_free_quota_pending_2m
                && post_thr.spec_index(t).view().indirect_free_quota_pending_1g == pre_thr.spec_index(t).view().indirect_free_quota_pending_1g,
        thread_effective_quota_4k(post_thr.spec_index(new_t)) == 0,
        thread_effective_quota_2m(post_thr.spec_index(new_t)) == 0,
        thread_effective_quota_1g(post_thr.spec_index(new_t)) == 0,
        post_thr.spec_index(new_t).view().direct_free_quota_pending_4k.view() == 0,
        post_thr.spec_index(new_t).view().direct_free_quota_pending_2m.view() == 0,
        post_thr.spec_index(new_t).view().direct_free_quota_pending_1g.view() == 0,
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().depth]
            uppers.contains(c) ==>
                post_thr.spec_index(new_t).view().indirect_free_quota_pending_4k.view().spec_index(post_ctn.spec_index(c).view_rodata().view().depth as int) == 0
                && post_thr.spec_index(new_t).view().indirect_free_quota_pending_2m.view().spec_index(post_ctn.spec_index(c).view_rodata().view().depth as int) == 0
                && post_thr.spec_index(new_t).view().indirect_free_quota_pending_1g.view().spec_index(post_ctn.spec_index(c).view_rodata().view().depth as int) == 0,
    ensures
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.dom().contains(c)]
            post_ctn.dom().contains(c) ==> {
                let pre_direct = pre_ctn.spec_index(c).view_user_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_user_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& thread_effective_quota_4k_fold_sum(post_direct, post_thr) == thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
                &&& thread_effective_quota_2m_fold_sum(post_direct, post_thr) == thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
                &&& thread_effective_quota_1g_fold_sum(post_direct, post_thr) == thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
{
    assert forall|c: RwLockContainerPtr|
        #![trigger post_ctn.dom().contains(c)]
        post_ctn.dom().contains(c) implies {
            let pre_direct = pre_ctn.spec_index(c).view_user_ghost().owned_threads.view();
            let post_direct = post_ctn.spec_index(c).view_user_ghost().owned_threads.view();
            let pre_indirect = pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view();
            let post_indirect = post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view();
            let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
            &&& thread_effective_quota_4k_fold_sum(post_direct, post_thr) == thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            &&& thread_effective_quota_2m_fold_sum(post_direct, post_thr) == thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            &&& thread_effective_quota_1g_fold_sum(post_direct, post_thr) == thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
        }
    by {
        reveal(container_thread_wf);
        let pre_direct = pre_ctn.spec_index(c).view_user_ghost().owned_threads.view();
        let post_direct = post_ctn.spec_index(c).view_user_ghost().owned_threads.view();
        let pre_indirect = pre_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view();
        let post_indirect = post_ctn.spec_index(c).view_kernel_ghost().owned_indirect_threads.view();
        let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
        if c == dc {
            vstd::set::axiom_set_ext_equal(post_direct, pre_direct.insert(new_t));
            lemma_thread_effective_quota_4k_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_direct_pending_4k_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_effective_quota_2m_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_direct_pending_2m_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_effective_quota_1g_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_direct_pending_1g_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
        } else {
            vstd::set::axiom_set_ext_equal(post_direct, pre_direct);
            lemma_thread_effective_quota_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_1g_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_1g_fold_eq(pre_direct, pre_thr, post_thr);
        }
        if uppers.contains(c) {
            vstd::set::axiom_set_ext_equal(post_indirect, pre_indirect.insert(new_t));
            lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(pre_indirect, pre_thr, post_thr, new_t, depth);
            lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(pre_indirect, pre_thr, post_thr, new_t, depth);
            lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(pre_indirect, pre_thr, post_thr, new_t, depth);
        } else {
            vstd::set::axiom_set_ext_equal(post_indirect, pre_indirect);
            lemma_thread_indirect_pending_4k_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_2m_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_1g_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
        }
    };
}

/// Transport the two 4K pending-quota folds when every thread's pending
/// counters are unchanged. This is a fold lemma: pointwise equality alone is
/// intentionally not expanded at allocation callsites.
pub proof fn lemma_thread_pending_4k_folds_eq_forall(
    container_map: ContainerLockedMap,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        container_thread_wf(container_map, pre),
        post.dom() =~= pre.dom(),
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t)]
            pre.dom().contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_4k
                    == pre.spec_index(t).view().direct_free_quota_pending_4k
                && post.spec_index(t).view().indirect_free_quota_pending_4k
                    == pre.spec_index(t).view().indirect_free_quota_pending_4k,
    ensures
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) ==> {
                let direct = container_map.spec_index(c_ptr)
                    .view_user_ghost().owned_threads.view();
                let indirect = container_map.spec_index(c_ptr)
                    .view_kernel_ghost().owned_indirect_threads.view();
                let depth = container_map.spec_index(c_ptr)
                    .view_rodata().view().depth as int;
                &&& thread_direct_pending_4k_fold_sum(direct, post)
                    == thread_direct_pending_4k_fold_sum(direct, pre)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(indirect, post, depth)
                    == thread_indirect_pending_4k_fold_sum_at_depth(indirect, pre, depth)
            },
{
    assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) implies {
                let direct = container_map.spec_index(c_ptr)
                    .view_user_ghost().owned_threads.view();
                let indirect = container_map.spec_index(c_ptr)
                    .view_kernel_ghost().owned_indirect_threads.view();
                let depth = container_map.spec_index(c_ptr)
                    .view_rodata().view().depth as int;
                &&& thread_direct_pending_4k_fold_sum(direct, post)
                    == thread_direct_pending_4k_fold_sum(direct, pre)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(indirect, post, depth)
                    == thread_indirect_pending_4k_fold_sum_at_depth(indirect, pre, depth)
            }
        by {
            let direct = container_map.spec_index(c_ptr)
                .view_user_ghost().owned_threads.view();
            let indirect = container_map.spec_index(c_ptr)
                .view_kernel_ghost().owned_indirect_threads.view();
            let depth = container_map.spec_index(c_ptr)
                .view_rodata().view().depth as int;
            assert(direct.subset_of(pre.dom())) by {
                reveal(container_thread_wf);
            };
            assert(indirect.subset_of(pre.dom())) by {
                reveal(container_thread_wf);
            };
            lemma_thread_direct_pending_4k_fold_eq(direct, pre, post);
            lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                indirect,
                pre,
                post,
                depth,
            );
    };
}

}

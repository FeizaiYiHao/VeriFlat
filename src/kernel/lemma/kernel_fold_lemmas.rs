use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {
// ===== Verified set/thread-fold lemmas =====
// Consumed by the kernel-preservation lemmas in this module tree.

// ============================================================
//   Verified narrow set-fold facts
// ============================================================
//
// Each lemma captures a pure fact about `Set::fold` of the shape
// `s.fold(0, |sum: int, p| sum + pmap.spec_index(p).view().quota_*)`
// — i.e. "summing a process quota over a finite set of process pointers".
// The lambda body is inlined to match exactly the lambda used in the
// `container_process_allocator_quota_*_wf` spec. The proofs reduce them to
// generic finite-set induction over vstd's `lemma_fold_insert` and
// `lemma_fold_empty`.

/// The sum-fold of `process_effective_quota_4k` over a set is preserved when
/// each process's effective quota is preserved.
pub proof fn lemma_process_effective_quota_4k_fold_eq(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(pre.spec_index(p))]
            s.contains(p) ==>
                process_effective_quota_4k(post.spec_index(p))
                    == process_effective_quota_4k(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(pre.spec_index(p_ptr))),
{
    let post_value =
        |p: RwLockProcessPtr| process_effective_quota_4k(post.spec_index(p));
    let pre_value =
        |p: RwLockProcessPtr| process_effective_quota_4k(pre.spec_index(p));
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, p: RwLockProcessPtr| sum + post_value(p);
    let pre_fold = |sum: int, p: RwLockProcessPtr| sum + pre_value(p);
    let direct_post_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_4k(post.spec_index(p));
    let direct_pre_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_4k(pre.spec_index(p));
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_process_effective_quota_2m_fold_eq(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_2m(pre.spec_index(p))]
            s.contains(p) ==>
                process_effective_quota_2m(post.spec_index(p))
                    == process_effective_quota_2m(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(pre.spec_index(p_ptr))),
{
    let post_value =
        |p: RwLockProcessPtr| process_effective_quota_2m(post.spec_index(p));
    let pre_value =
        |p: RwLockProcessPtr| process_effective_quota_2m(pre.spec_index(p));
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, p: RwLockProcessPtr| sum + post_value(p);
    let pre_fold = |sum: int, p: RwLockProcessPtr| sum + pre_value(p);
    let direct_post_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_2m(post.spec_index(p));
    let direct_pre_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_2m(pre.spec_index(p));
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_process_effective_quota_1g_fold_eq(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_1g(pre.spec_index(p))]
            s.contains(p) ==>
                process_effective_quota_1g(post.spec_index(p))
                    == process_effective_quota_1g(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(pre.spec_index(p_ptr))),
{
    let post_value =
        |p: RwLockProcessPtr| process_effective_quota_1g(post.spec_index(p));
    let pre_value =
        |p: RwLockProcessPtr| process_effective_quota_1g(pre.spec_index(p));
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, p: RwLockProcessPtr| sum + post_value(p);
    let pre_fold = |sum: int, p: RwLockProcessPtr| sum + pre_value(p);
    let direct_post_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_1g(post.spec_index(p));
    let direct_pre_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_1g(pre.spec_index(p));
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

/// When exactly one process's effective quota changes by
/// `x` (e.g. its `quota_4k` shifts by `x` with `temp_alloc_cache_4k`
/// unchanged), the fold sum shifts by the same `x`.
pub proof fn lemma_process_effective_quota_4k_fold_change_by(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    mod_p: RwLockProcessPtr,
    x: int,
)
    requires
        s.contains(mod_p),
        process_effective_quota_4k(post.spec_index(mod_p))
            == process_effective_quota_4k(pre.spec_index(mod_p)) + x,
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(pre.spec_index(p))]
            s.contains(p) && p != mod_p ==>
                process_effective_quota_4k(post.spec_index(p))
                    == process_effective_quota_4k(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(pre.spec_index(p_ptr))) + x,
{
    let pre_value =
        |p: RwLockProcessPtr| process_effective_quota_4k(pre.spec_index(p));
    let post_value =
        |p: RwLockProcessPtr| process_effective_quota_4k(post.spec_index(p));
    lemma_set_fold_int_sum_change_by(s, pre_value, post_value, mod_p, x);
    let pre_fold = |sum: int, p: RwLockProcessPtr| sum + pre_value(p);
    let post_fold = |sum: int, p: RwLockProcessPtr| sum + post_value(p);
    let direct_pre_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_4k(pre.spec_index(p));
    let direct_post_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_4k(post.spec_index(p));
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_process_effective_quota_4k_fold_nonneg(
    s: Set<RwLockProcessPtr>,
    process_map: ProcessLockedMap,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(process_map.spec_index(p))]
            s.contains(p) ==> process_effective_quota_4k(process_map.spec_index(p)) >= 0,
    ensures
        process_effective_quota_4k_fold_sum(s, process_map) >= 0,
{
    let value =
        |p: RwLockProcessPtr| process_effective_quota_4k(process_map.spec_index(p));
    lemma_set_fold_int_sum_nonneg(s, value);
    let fold = |sum: int, p: RwLockProcessPtr| sum + value(p);
    let direct_fold = |sum: int, p: RwLockProcessPtr|
        sum + process_effective_quota_4k(process_map.spec_index(p));
    assert(fold =~= direct_fold);
}

/// Fold facts for the independent per-thread quota tier. These have
/// the same finite-set semantics as the process-quota fold facts above.
pub proof fn lemma_thread_effective_quota_4k_fold_eq(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_4k(pre.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_4k(post.spec_index(t))
                == thread_effective_quota_4k(pre.spec_index(t)),
    ensures
        thread_effective_quota_4k_fold_sum(s, post)
            == thread_effective_quota_4k_fold_sum(s, pre),
{
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(post.spec_index(t));
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(pre.spec_index(t));
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(post.spec_index(t));
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(pre.spec_index(t));
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_effective_quota_2m_fold_eq(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_2m(pre.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_2m(post.spec_index(t))
                == thread_effective_quota_2m(pre.spec_index(t)),
    ensures
        thread_effective_quota_2m_fold_sum(s, post)
            == thread_effective_quota_2m_fold_sum(s, pre),
{
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_2m(post.spec_index(t));
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_2m(pre.spec_index(t));
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_2m(post.spec_index(t));
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_2m(pre.spec_index(t));
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_effective_quota_1g_fold_eq(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_1g(pre.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_1g(post.spec_index(t))
                == thread_effective_quota_1g(pre.spec_index(t)),
    ensures
        thread_effective_quota_1g_fold_sum(s, post)
            == thread_effective_quota_1g_fold_sum(s, pre),
{
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_1g(post.spec_index(t));
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_1g(pre.spec_index(t));
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_1g(post.spec_index(t));
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_1g(pre.spec_index(t));
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_effective_quota_4k_fold_change_by(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    mod_t: RwLockThreadPtr,
    x: int,
)
    requires
        s.contains(mod_t),
        thread_effective_quota_4k(post.spec_index(mod_t))
            == thread_effective_quota_4k(pre.spec_index(mod_t)) + x,
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_4k(pre.spec_index(t))]
            s.contains(t) && t != mod_t ==> thread_effective_quota_4k(post.spec_index(t))
                == thread_effective_quota_4k(pre.spec_index(t)),
    ensures
        thread_effective_quota_4k_fold_sum(s, post)
            == thread_effective_quota_4k_fold_sum(s, pre) + x,
{
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(pre.spec_index(t));
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(post.spec_index(t));
    lemma_set_fold_int_sum_change_by(s, pre_value, post_value, mod_t, x);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(pre.spec_index(t));
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(post.spec_index(t));
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_effective_quota_4k_fold_ge_member(
    s: Set<RwLockThreadPtr>,
    thread_map: ThreadLockedMap,
    mem: RwLockThreadPtr,
)
    requires
        s.contains(mem),
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_4k(thread_map.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_4k(thread_map.spec_index(t)) >= 0,
    ensures
        thread_effective_quota_4k_fold_sum(s, thread_map)
            >= thread_effective_quota_4k(thread_map.spec_index(mem)),
{
    let value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(thread_map.spec_index(t));
    lemma_set_fold_int_sum_ge_member(s, value, mem);
    let fold = |sum: int, t: RwLockThreadPtr| sum + value(t);
    let direct_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(thread_map.spec_index(t));
    assert(fold =~= direct_fold);
}

pub proof fn lemma_thread_effective_quota_4k_fold_insert_zero(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
)
    requires
        s.contains(new_t) == false,
        thread_effective_quota_4k(post.spec_index(new_t)) == 0,
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_4k(pre.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_4k(post.spec_index(t))
                == thread_effective_quota_4k(pre.spec_index(t)),
    ensures
        thread_effective_quota_4k_fold_sum(s.insert(new_t), post)
            == thread_effective_quota_4k_fold_sum(s, pre),
{
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(pre.spec_index(t));
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_4k(post.spec_index(t));
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(pre.spec_index(t));
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_4k(post.spec_index(t));
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_effective_quota_2m_fold_insert_zero(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
)
    requires
        s.contains(new_t) == false,
        thread_effective_quota_2m(post.spec_index(new_t)) == 0,
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_2m(pre.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_2m(post.spec_index(t))
                == thread_effective_quota_2m(pre.spec_index(t)),
    ensures
        thread_effective_quota_2m_fold_sum(s.insert(new_t), post)
            == thread_effective_quota_2m_fold_sum(s, pre),
{
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_2m(pre.spec_index(t));
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_2m(post.spec_index(t));
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_2m(pre.spec_index(t));
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_2m(post.spec_index(t));
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_effective_quota_1g_fold_insert_zero(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
)
    requires
        s.contains(new_t) == false,
        thread_effective_quota_1g(post.spec_index(new_t)) == 0,
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_1g(pre.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_1g(post.spec_index(t))
                == thread_effective_quota_1g(pre.spec_index(t)),
    ensures
        thread_effective_quota_1g_fold_sum(s.insert(new_t), post)
            == thread_effective_quota_1g_fold_sum(s, pre),
{
    let pre_value =
        |t: RwLockThreadPtr| thread_effective_quota_1g(pre.spec_index(t));
    let post_value =
        |t: RwLockThreadPtr| thread_effective_quota_1g(post.spec_index(t));
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_1g(pre.spec_index(t));
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_effective_quota_1g(post.spec_index(t));
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

/// The thread direct free-quota-pending fold is preserved when per-thread
/// values are unchanged.
pub proof fn lemma_thread_direct_pending_4k_fold_eq(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().direct_free_quota_pending_4k]
            s.contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_4k.view()
                    == pre.spec_index(t).view().direct_free_quota_pending_4k.view(),
    ensures
        thread_direct_pending_4k_fold_sum(s, post)
            == thread_direct_pending_4k_fold_sum(s, pre),
{
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().direct_free_quota_pending_4k.view();
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().direct_free_quota_pending_4k.view();
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_direct_pending_2m_fold_eq(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().direct_free_quota_pending_2m]
            s.contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_2m.view()
                    == pre.spec_index(t).view().direct_free_quota_pending_2m.view(),
    ensures
        thread_direct_pending_2m_fold_sum(s, post)
            == thread_direct_pending_2m_fold_sum(s, pre),
{
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().direct_free_quota_pending_2m.view() as int;
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().direct_free_quota_pending_2m.view() as int;
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().direct_free_quota_pending_2m.view();
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().direct_free_quota_pending_2m.view();
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_direct_pending_1g_fold_eq(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().direct_free_quota_pending_1g]
            s.contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_1g.view()
                    == pre.spec_index(t).view().direct_free_quota_pending_1g.view(),
    ensures
        thread_direct_pending_1g_fold_sum(s, post)
            == thread_direct_pending_1g_fold_sum(s, pre),
{
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().direct_free_quota_pending_1g.view();
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().direct_free_quota_pending_1g.view();
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

/// The indirect free-quota-pending fold at a specific depth is preserved
/// when per-thread values at that depth are unchanged.
pub proof fn lemma_thread_indirect_pending_4k_fold_eq_at_depth(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    depth: int,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().indirect_free_quota_pending_4k]
            s.contains(t) ==>
                post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth)
                    == pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth),
    ensures
        thread_indirect_pending_4k_fold_sum_at_depth(s, post, depth)
            == thread_indirect_pending_4k_fold_sum_at_depth(s, pre, depth),
{
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth);
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_indirect_pending_2m_fold_eq_at_depth(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    depth: int,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().indirect_free_quota_pending_2m]
            s.contains(t) ==>
                post.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth)
                    == pre.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth),
    ensures
        thread_indirect_pending_2m_fold_sum_at_depth(s, post, depth)
            == thread_indirect_pending_2m_fold_sum_at_depth(s, pre, depth),
{
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth);
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

pub proof fn lemma_thread_indirect_pending_1g_fold_eq_at_depth(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    depth: int,
)
    requires
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().indirect_free_quota_pending_1g]
            s.contains(t) ==>
                post.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth)
                    == pre.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth),
    ensures
        thread_indirect_pending_1g_fold_sum_at_depth(s, post, depth)
            == thread_indirect_pending_1g_fold_sum_at_depth(s, pre, depth),
{
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_congruence(s, post_value, pre_value);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth);
    assert(post_fold =~= direct_post_fold);
    assert(pre_fold =~= direct_pre_fold);
}

/// Direct free-quota-pending fold when a fresh thread
/// `new_t` with zero direct pending is inserted into the folded set. The new
/// element contributes `0`; every pre-existing element's value is preserved;
/// so the fold sum is unchanged. The set-growth twin of
/// `lemma_thread_direct_pending_4k_fold_eq`, for the thread-create case where
/// a container's `owned_threads` gains the fresh thread.
pub proof fn lemma_thread_direct_pending_4k_fold_insert_zero(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
)
    requires
        s.contains(new_t) == false,
        post.spec_index(new_t).view().direct_free_quota_pending_4k.view() == 0,
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().direct_free_quota_pending_4k]
            s.contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_4k.view()
                    == pre.spec_index(t).view().direct_free_quota_pending_4k.view(),
    ensures
        thread_direct_pending_4k_fold_sum(s.insert(new_t), post)
            == thread_direct_pending_4k_fold_sum(s, pre),
{
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().direct_free_quota_pending_4k.view();
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().direct_free_quota_pending_4k.view();
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_direct_pending_2m_fold_insert_zero(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
)
    requires
        s.contains(new_t) == false,
        post.spec_index(new_t).view().direct_free_quota_pending_2m.view() == 0,
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().direct_free_quota_pending_2m]
            s.contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_2m.view()
                    == pre.spec_index(t).view().direct_free_quota_pending_2m.view(),
    ensures
        thread_direct_pending_2m_fold_sum(s.insert(new_t), post)
            == thread_direct_pending_2m_fold_sum(s, pre),
{
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().direct_free_quota_pending_2m.view() as int;
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().direct_free_quota_pending_2m.view() as int;
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().direct_free_quota_pending_2m.view();
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().direct_free_quota_pending_2m.view();
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_direct_pending_1g_fold_insert_zero(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
)
    requires
        s.contains(new_t) == false,
        post.spec_index(new_t).view().direct_free_quota_pending_1g.view() == 0,
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().direct_free_quota_pending_1g]
            s.contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_1g.view()
                    == pre.spec_index(t).view().direct_free_quota_pending_1g.view(),
    ensures
        thread_direct_pending_1g_fold_sum(s.insert(new_t), post)
            == thread_direct_pending_1g_fold_sum(s, pre),
{
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().direct_free_quota_pending_1g.view();
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().direct_free_quota_pending_1g.view();
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

/// Indirect free-quota-pending fold (at a fixed container
/// depth) when a fresh thread `new_t` with zero indirect pending at that depth
/// is inserted into the folded set. The set-growth twin of
/// `lemma_thread_indirect_pending_4k_fold_eq_at_depth`, for the thread-create
/// case where an ancestor container's `owned_indirect_threads` gains the fresh
/// thread.
pub proof fn lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
    depth: int,
)
    requires
        s.contains(new_t) == false,
        post.spec_index(new_t).view().indirect_free_quota_pending_4k.view().spec_index(depth) == 0,
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().indirect_free_quota_pending_4k]
            s.contains(t) ==>
                post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth)
                    == pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth),
    ensures
        thread_indirect_pending_4k_fold_sum_at_depth(s.insert(new_t), post, depth)
            == thread_indirect_pending_4k_fold_sum_at_depth(s, pre, depth),
{
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth);
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
    depth: int,
)
    requires
        s.contains(new_t) == false,
        post.spec_index(new_t).view().indirect_free_quota_pending_2m.view().spec_index(depth) == 0,
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().indirect_free_quota_pending_2m]
            s.contains(t) ==>
                post.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth)
                    == pre.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth),
    ensures
        thread_indirect_pending_2m_fold_sum_at_depth(
            s.insert(new_t), post, depth,
        ) == thread_indirect_pending_2m_fold_sum_at_depth(s, pre, depth),
{
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth);
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

pub proof fn lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(
    s: Set<RwLockThreadPtr>,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    new_t: RwLockThreadPtr,
    depth: int,
)
    requires
        s.contains(new_t) == false,
        post.spec_index(new_t).view().indirect_free_quota_pending_1g.view().spec_index(depth) == 0,
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t).view().indirect_free_quota_pending_1g]
            s.contains(t) ==>
                post.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth)
                    == pre.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth),
    ensures
        thread_indirect_pending_1g_fold_sum_at_depth(
            s.insert(new_t), post, depth,
        ) == thread_indirect_pending_1g_fold_sum_at_depth(s, pre, depth),
{
    let pre_value = |t: RwLockThreadPtr|
        pre.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
    let post_value = |t: RwLockThreadPtr|
        post.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_insert_zero(s, pre_value, post_value, new_t);
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr|
        sum + pre.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth);
    let direct_post_fold = |sum: int, t: RwLockThreadPtr|
        sum + post.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth);
    assert(pre_fold =~= direct_pre_fold);
    assert(post_fold =~= direct_post_fold);
}

/// The direct-thread-pending fold in the container conservation law is
/// non-negative because every summand is a `usize`.
pub proof fn lemma_thread_direct_pending_4k_fold_nonneg(
    s: Set<RwLockThreadPtr>,
    thread_map: ThreadLockedMap,
)
    ensures
        thread_direct_pending_4k_fold_sum(s, thread_map) >= 0,
{
    let value = |t: RwLockThreadPtr|
        thread_map.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
    lemma_set_fold_int_sum_nonneg(s, value);
    let fold = |sum: int, t: RwLockThreadPtr| sum + value(t);
    let direct_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_map.spec_index(t).view().direct_free_quota_pending_4k.view();
    assert(fold =~= direct_fold);
}

/// The indirect-thread-pending fold at a fixed container depth is
/// non-negative because every summand is a `usize`.
pub proof fn lemma_thread_indirect_pending_4k_fold_nonneg(
    s: Set<RwLockThreadPtr>,
    thread_map: ThreadLockedMap,
    depth: int,
)
    ensures
        thread_indirect_pending_4k_fold_sum_at_depth(s, thread_map, depth) >= 0,
{
    let value = |t: RwLockThreadPtr|
        thread_map.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
    lemma_set_fold_int_sum_nonneg(s, value);
    let fold = |sum: int, t: RwLockThreadPtr| sum + value(t);
    let direct_fold = |sum: int, t: RwLockThreadPtr|
        sum + thread_map.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth);
    assert(fold =~= direct_fold);
}
}

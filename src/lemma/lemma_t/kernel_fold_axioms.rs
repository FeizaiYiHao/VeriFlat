use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// ===== Trusted set/thread-fold + staged-pages axioms (TCB) =====
// Moved out of kernel/spec_util.rs (which holds only spec fns).
// Consumed by the kernel-preservation lemmas in lemma_u::kernel_preservation.

// ============================================================
//   Trusted axioms: narrow set-fold facts
// ============================================================
//
// These are the ONLY external_body lemmas used by the
// `container_process_allocator_quota_wf` preservation proofs below.
// Each captures a pure fact about `Set::fold` of the shape
// `s.fold(0, |sum: int, p| sum + pmap.spec_index(p).view().quota_*)`
// — i.e. "summing a process quota over a finite set of process pointers".
// The lambda body is inlined to match exactly the lambda used in the
// `container_process_allocator_quota_*_wf` spec, so unification at call
// sites is trivial. Same shape and granularity as the user's
// `fold_change_mem_4k_lemma` reference template.
//
// Each could in principle be derived from vstd's `lemma_fold_insert` /
// `lemma_fold_empty` by induction on the set, but vstd doesn't ship the
// induction step as a broadcast lemma so we expose them here as narrow
// axioms instead.

/// Trusted axiom (TCB): sum-fold of `process_effective_quota_4k` over a set
/// is preserved when each process's effective quota is preserved.
/// Soundness: induct on the set; per-element equality closes the step.
#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

/// Trusted axiom (TCB): when exactly one process's effective quota changes,
/// the fold sum shifts by the per-element delta.
#[verifier::external_body]
pub proof fn lemma_process_effective_quota_4k_fold_change_one(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    mod_p: RwLockProcessPtr,
)
    requires
        s.contains(mod_p),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(pre.spec_index(p))]
            s.contains(p) && p != mod_p ==>
                process_effective_quota_4k(post.spec_index(p))
                    == process_effective_quota_4k(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(pre.spec_index(p_ptr)))
                - process_effective_quota_4k(pre.spec_index(mod_p))
                + process_effective_quota_4k(post.spec_index(mod_p)),
{
}

/// Trusted axiom (TCB): when exactly one process's effective quota changes by
/// `x` (e.g. its `quota_4k` shifts by `x` with `temp_alloc_cache_4k`
/// unchanged), the fold sum shifts by the same `x`. The explicit-`x` form of
/// `lemma_process_effective_quota_4k_fold_change_one`, for callers that know
/// the increment directly.
/// Soundness: induct on the set; the one changed element contributes `+x`,
/// every other element is unchanged.
#[verifier::external_body]
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
}

/// Trusted axiom (TCB): the sum-fold of `process_effective_quota_4k` over a set
/// is at least any single member's effective quota, provided every member's
/// effective quota is non-negative. Pins the container conservation fold from
/// below: a held process with `effective_quota_4k >= 1` forces the fold — and
/// thus `total_free_pages` — to be `>= 1`.
/// Soundness: induct on the set; the member contributes its own value, every
/// other element contributes a non-negative summand.
#[verifier::external_body]
pub proof fn lemma_process_effective_quota_4k_fold_ge_member(
    s: Set<RwLockProcessPtr>,
    pm: ProcessLockedMap,
    mem: RwLockProcessPtr,
)
    requires
        s.contains(mem),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(pm.spec_index(p))]
            s.contains(p) ==> process_effective_quota_4k(pm.spec_index(p)) >= 0,
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(pm.spec_index(p_ptr)))
            >= process_effective_quota_4k(pm.spec_index(mem)),
{
}

#[verifier::external_body]
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
}

#[verifier::external_body]
pub proof fn lemma_process_effective_quota_2m_fold_change_by(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    mod_p: RwLockProcessPtr,
    x: int,
)
    requires
        s.contains(mod_p),
        process_effective_quota_2m(post.spec_index(mod_p))
            == process_effective_quota_2m(pre.spec_index(mod_p)) + x,
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_2m(pre.spec_index(p))]
            s.contains(p) && p != mod_p ==>
                process_effective_quota_2m(post.spec_index(p))
                    == process_effective_quota_2m(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(pre.spec_index(p_ptr))) + x,
{
}

#[verifier::external_body]
pub proof fn lemma_process_effective_quota_1g_fold_change_by(
    s: Set<RwLockProcessPtr>,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    mod_p: RwLockProcessPtr,
    x: int,
)
    requires
        s.contains(mod_p),
        process_effective_quota_1g(post.spec_index(mod_p))
            == process_effective_quota_1g(pre.spec_index(mod_p)) + x,
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_1g(pre.spec_index(p))]
            s.contains(p) && p != mod_p ==>
                process_effective_quota_1g(post.spec_index(p))
                    == process_effective_quota_1g(pre.spec_index(p)),
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.spec_index(p_ptr)))
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(pre.spec_index(p_ptr))) + x,
{
}

/// Trusted fold facts for the independent per-thread quota tier. These have
/// the same finite-set semantics as the process-quota fold facts above.
#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

#[verifier::external_body]
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
}

/// Trusted axiom (TCB): thread direct free-quota-pending fold preserved
/// when per-thread values are unchanged.
#[verifier::external_body]
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
}

#[verifier::external_body]
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
        s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().direct_free_quota_pending_2m.view())
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()),
{
}

#[verifier::external_body]
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
        s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().direct_free_quota_pending_1g.view())
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()),
{
}

/// Trusted axiom (TCB): indirect free-quota-pending fold at a specific
/// depth is preserved when per-thread values at that depth are unchanged.
#[verifier::external_body]
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
}

#[verifier::external_body]
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
        s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth))
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth)),
{
}

#[verifier::external_body]
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
        s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth))
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth)),
{
}

/// Trusted axiom (TCB): direct free-quota-pending fold when a fresh thread
/// `new_t` with zero direct pending is inserted into the folded set. The new
/// element contributes `0`; every pre-existing element's value is preserved;
/// so the fold sum is unchanged. The set-growth twin of
/// `lemma_thread_direct_pending_4k_fold_eq`, for the thread-create case where
/// a container's `owned_threads` gains the fresh thread.
/// Soundness: induct on the set (vstd `lemma_fold_insert`); the inserted
/// element contributes `+0`, every other element matches per-element.
#[verifier::external_body]
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
}

#[verifier::external_body]
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
        s.insert(new_t).fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().direct_free_quota_pending_2m.view())
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()),
{
}

#[verifier::external_body]
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
        s.insert(new_t).fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().direct_free_quota_pending_1g.view())
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()),
{
}

/// Trusted axiom (TCB): indirect free-quota-pending fold (at a fixed container
/// depth) when a fresh thread `new_t` with zero indirect pending at that depth
/// is inserted into the folded set. The set-growth twin of
/// `lemma_thread_indirect_pending_4k_fold_eq_at_depth`, for the thread-create
/// case where an ancestor container's `owned_indirect_threads` gains the fresh
/// thread.
/// Soundness: induct on the set (vstd `lemma_fold_insert`); the inserted
/// element contributes `+0` at `depth`, every other element matches per-element.
#[verifier::external_body]
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
}

#[verifier::external_body]
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
        s.insert(new_t).fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth))
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(depth)),
{
}

#[verifier::external_body]
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
        s.insert(new_t).fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth))
            == s.fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + pre.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth)),
{
}

/// Trusted axiom (TCB): `thread_staged_pages_wf` is preserved when
/// page_array is unchanged and per-thread views (which contain
/// temp_alloc_cache) are unchanged. Narrow: the quantifiers in
/// `thread_staged_pages_{4k,2m,1g}_wf` evaluate identically when their
/// only free variables (page_array entries and thread views) are equal.
#[verifier::external_body]
pub proof fn lemma_thread_staged_pages_wf_preserved_for_view_eq(
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    page_array: PageLockedArray,
)
    requires
        thread_staged_pages_wf(pre_thread_map, page_array),
        post_thread_map.dom() == pre_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger post_thread_map.spec_index(t_ptr).view().temp_alloc_cache_4k]
            post_thread_map.dom().contains(t_ptr) ==>
                post_thread_map.spec_index(t_ptr).view().temp_alloc_cache_4k.view()
                    == pre_thread_map.spec_index(t_ptr).view().temp_alloc_cache_4k.view()
                && post_thread_map.spec_index(t_ptr).view().temp_alloc_cache_2m.view()
                    == pre_thread_map.spec_index(t_ptr).view().temp_alloc_cache_2m.view()
                && post_thread_map.spec_index(t_ptr).view().temp_alloc_cache_1g.view()
                    == pre_thread_map.spec_index(t_ptr).view().temp_alloc_cache_1g.view(),
    ensures
        thread_staged_pages_wf(post_thread_map, page_array),
{
}

/// Trusted axiom (TCB): the direct-thread-pending fold in the container
/// conservation law is non-negative (every summand is a `usize`).
/// Soundness: induct on the set; each summand is a `usize` length.
#[verifier::external_body]
pub proof fn lemma_thread_direct_pending_4k_fold_nonneg(
    s: Set<RwLockThreadPtr>,
    thread_map: ThreadLockedMap,
)
    ensures
        thread_direct_pending_4k_fold_sum(s, thread_map) >= 0,
{
}

/// Trusted axiom (TCB): the indirect-thread-pending fold (at a fixed container
/// depth) in the conservation law is non-negative (every summand is a `usize`).
/// Soundness: induct on the set; each summand is a `usize` length.
#[verifier::external_body]
pub proof fn lemma_thread_indirect_pending_4k_fold_nonneg(
    s: Set<RwLockThreadPtr>,
    thread_map: ThreadLockedMap,
    depth: int,
)
    ensures
        thread_indirect_pending_4k_fold_sum_at_depth(s, thread_map, depth) >= 0,
{
}

}

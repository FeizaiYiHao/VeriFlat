use vstd::prelude::*;
use crate::*;

verus! {
proof fn lemma_iset_fold_int_sum_congruence<A>(s: ISet<A>, lhs: spec_fn(A) -> int, rhs: spec_fn(A) -> int)
    requires
        s.finite(),
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) ==> lhs(a) == rhs(a),
    ensures
        s.fold(0int, |sum: int, a: A| sum + lhs(a)) == s.fold(0int, |sum: int, a: A| sum + rhs(a)),
    decreases s.len(),
{
    let lhs_fold = |sum: int, a: A| sum + lhs(a);
    let rhs_fold = |sum: int, a: A| sum + rhs(a);
    let pred = |part: ISet<A>| part.subset_of(s) ==> part.fold(0int, lhs_fold) == part.fold(0int, rhs_fold);
    assert(pred(ISet::empty())) by { vstd::iset::fold::lemma_fold_empty(0int, lhs_fold); vstd::iset::fold::lemma_fold_empty(0int, rhs_fold); };
    assert forall|part: ISet<A>, a: A|
        pred(part) && part.finite() && !part.contains(a)
        implies #[trigger] pred(part.insert(a)) by {
        if part.insert(a).subset_of(s) {
            assert(s.contains(a));
            vstd::iset::fold::lemma_fold_insert(part, 0int, lhs_fold, a);
            vstd::iset::fold::lemma_fold_insert(part, 0int, rhs_fold, a);
        }
    };
    vstd::iset::fold::lemma_finite_set_induct(s, pred);
}

pub proof fn lemma_set_fold_int_sum_congruence<A>(s: Set<A>, lhs: spec_fn(A) -> int, rhs: spec_fn(A) -> int)
    requires
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) ==> lhs(a) == rhs(a),
    ensures
        s.fold(0int, |sum: int, a: A| sum + lhs(a)) == s.fold(0int, |sum: int, a: A| sum + rhs(a)),
{ vstd::set::lemma_to_iset_finite(s); lemma_iset_fold_int_sum_congruence(s.to_iset(), lhs, rhs); }

pub proof fn lemma_set_fold_int_sum_empty<A>(s: Set<A>, value: spec_fn(A) -> int)
    requires
        s =~= Set::<A>::empty(),
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) == 0,
{
    let fold = |sum: int, a: A| sum + value(a);
    vstd::iset::fold::lemma_fold_empty(0int, fold);
    assert(s.to_iset() =~= ISet::<A>::empty());
}

pub proof fn lemma_set_fold_int_sum_singleton<A>(s: Set<A>, member: A, value: spec_fn(A) -> int)
    requires
        s =~= Set::<A>::empty().insert(member),
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) == value(member),
{
    let fold = |sum: int, a: A| sum + value(a);
    vstd::iset::fold::lemma_fold_empty(0int, fold);
    vstd::iset::fold::lemma_fold_insert(ISet::<A>::empty(), 0int, fold, member);
    assert(s.to_iset() =~= ISet::<A>::empty().insert(member));
}

proof fn lemma_iset_fold_int_sum_nonneg<A>(s: ISet<A>, value: spec_fn(A) -> int)
    requires
        s.finite(),
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) ==> value(a) >= 0,
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) >= 0,
    decreases s.len(),
{
    let fold = |sum: int, a: A| sum + value(a);
    let pred = |part: ISet<A>| part.subset_of(s) ==> part.fold(0int, fold) >= 0;
    assert(pred(ISet::empty())) by { vstd::iset::fold::lemma_fold_empty(0int, fold); };
    assert forall|part: ISet<A>, a: A|
        pred(part) && part.finite() && !part.contains(a)
        implies #[trigger] pred(part.insert(a)) by { if part.insert(a).subset_of(s) { assert(s.contains(a)); vstd::iset::fold::lemma_fold_insert(part, 0int, fold, a); }; };
    vstd::iset::fold::lemma_finite_set_induct(s, pred);
}

pub proof fn lemma_set_fold_int_sum_nonneg<A>(s: Set<A>, value: spec_fn(A) -> int)
    requires
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) ==> value(a) >= 0,
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) >= 0,
{ vstd::set::lemma_to_iset_finite(s); lemma_iset_fold_int_sum_nonneg(s.to_iset(), value); }

pub proof fn lemma_set_fold_int_sum_ge_member<A>(s: Set<A>, value: spec_fn(A) -> int, member: A)
    requires
        s.contains(member),
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) ==> value(a) >= 0,
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) >= value(member),
{
    let is = s.to_iset();
    let rest = is.remove(member);
    let fold = |sum: int, a: A| sum + value(a);
    vstd::set::lemma_to_iset_finite(s);
    lemma_iset_fold_int_sum_nonneg(rest, value);
    vstd::iset::fold::lemma_fold_insert(rest, 0int, fold, member);
}

pub proof fn lemma_set_fold_int_sum_change_by<A>(s: Set<A>, pre: spec_fn(A) -> int, post: spec_fn(A) -> int, changed: A, delta: int)
    requires
        s.contains(changed),
        post(changed) == pre(changed) + delta,
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) && a != changed ==> post(a) == pre(a),
    ensures
        s.fold(0int, |sum: int, a: A| sum + post(a)) == s.fold(0int, |sum: int, a: A| sum + pre(a)) + delta,
{
    let is = s.to_iset();
    let rest = is.remove(changed);
    let pre_fold = |sum: int, a: A| sum + pre(a);
    let post_fold = |sum: int, a: A| sum + post(a);
    vstd::set::lemma_to_iset_finite(s);
    vstd::iset::lemma_iset_remove_finite(is, changed);
    lemma_iset_fold_int_sum_congruence(rest, pre, post);
    vstd::iset::fold::lemma_fold_insert(rest, 0int, pre_fold, changed);
    vstd::iset::fold::lemma_fold_insert(rest, 0int, post_fold, changed);
}

pub proof fn lemma_set_fold_int_sum_insert_zero<A>(s: Set<A>, pre: spec_fn(A) -> int, post: spec_fn(A) -> int, inserted: A)
    requires
        !s.contains(inserted),
        post(inserted) == 0,
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) ==> post(a) == pre(a),
    ensures
        s.insert(inserted).fold(0int, |sum: int, a: A| sum + post(a)) == s.fold(0int, |sum: int, a: A| sum + pre(a)),
{
    let post_fold = |sum: int, a: A| sum + post(a);
    lemma_set_fold_int_sum_congruence(s, post, pre);
    vstd::iset::fold::lemma_fold_insert(s.to_iset(), 0int, post_fold, inserted);
    assert(s.insert(inserted).to_iset() =~= s.to_iset().insert(inserted));
}

pub proof fn lemma_set_fold_int_sum_remove<A>(s: Set<A>, pre: spec_fn(A) -> int, post: spec_fn(A) -> int, removed: A)
    requires
        s.contains(removed),
        forall|a: A| #![trigger s.contains(a)]
            s.contains(a) && a != removed ==> post(a) == pre(a),
    ensures
        s.remove(removed).fold(0int, |sum: int, a: A| sum + post(a)) == s.fold(0int, |sum: int, a: A| sum + pre(a)) - pre(removed),
{
    let rest = s.remove(removed);
    let pre_fold = |sum: int, a: A| sum + pre(a);
    lemma_set_fold_int_sum_congruence(rest, post, pre);
    vstd::set::lemma_to_iset_finite(rest);
    vstd::iset::fold::lemma_fold_insert(rest.to_iset(), 0int, pre_fold, removed);
    assert(s.to_iset() =~= rest.to_iset().insert(removed));
}

pub proof fn lemma_thread_effective_quota_2m_fold_change_by(s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap, changed: RwLockThreadPtr, delta: int)
    requires
        s.contains(changed),
        thread_effective_quota_2m(post.spec_index(changed)) == thread_effective_quota_2m(pre.spec_index(changed)) + delta,
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_2m(pre.spec_index(t))]
            s.contains(t) && t != changed ==> thread_effective_quota_2m(post.spec_index(t)) == thread_effective_quota_2m(pre.spec_index(t)),
    ensures
        thread_effective_quota_2m_fold_sum(s, post) == thread_effective_quota_2m_fold_sum(s, pre) + delta,
{
    let pre_value = |t: RwLockThreadPtr| thread_effective_quota_2m(pre.spec_index(t));
    let post_value = |t: RwLockThreadPtr| thread_effective_quota_2m(post.spec_index(t));
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_2m(pre.spec_index(t));
    let direct_post_fold = |sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_2m(post.spec_index(t));
    assert(pre_fold =~= direct_pre_fold && post_fold =~= direct_post_fold && s.fold(0int, post_fold) == s.fold(0int, pre_fold) + delta) by { lemma_set_fold_int_sum_change_by(s, pre_value, post_value, changed, delta); };
}

pub proof fn lemma_process_effective_quota_2m_fold_nonneg(s: Set<RwLockProcessPtr>, process_map: ProcessLockedMap)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_2m(process_map.spec_index(p))]
            s.contains(p) ==> process_effective_quota_2m(process_map.spec_index(p)) >= 0,
    ensures
        process_effective_quota_2m_fold_sum(s, process_map) >= 0,
{
    let value = |p: RwLockProcessPtr| process_effective_quota_2m(process_map.spec_index(p));
    let value_fold = |sum: int, p: RwLockProcessPtr| sum + value(p);
    let direct_fold = |sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(process_map.spec_index(p));
    assert(value_fold =~= direct_fold && s.fold(0int, value_fold) >= 0) by { lemma_set_fold_int_sum_nonneg(s, value); };
}

pub proof fn lemma_thread_effective_quota_2m_fold_ge_member(s: Set<RwLockThreadPtr>, thread_map: ThreadLockedMap, member: RwLockThreadPtr)
    requires
        s.contains(member),
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_2m(thread_map.spec_index(t))]
            s.contains(t) ==> thread_effective_quota_2m(thread_map.spec_index(t)) >= 0,
    ensures
        thread_effective_quota_2m_fold_sum(s, thread_map) >= thread_effective_quota_2m(thread_map.spec_index(member)),
{
    let value = |t: RwLockThreadPtr| thread_effective_quota_2m(thread_map.spec_index(t));
    let value_fold = |sum: int, t: RwLockThreadPtr| sum + value(t);
    let direct_fold = |sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_2m(thread_map.spec_index(t));
    assert(value_fold =~= direct_fold && s.fold(0int, value_fold) >= value(member)) by { lemma_set_fold_int_sum_ge_member(s, value, member); };
}

pub proof fn lemma_thread_direct_pending_2m_fold_nonneg(s: Set<RwLockThreadPtr>, thread_map: ThreadLockedMap)
    ensures
        thread_direct_pending_2m_fold_sum(s, thread_map) >= 0,
{
    let value = |t: RwLockThreadPtr| thread_map.spec_index(t).view().direct_free_quota_pending_2m.view() as int;
    let value_fold = |sum: int, t: RwLockThreadPtr| sum + value(t);
    let direct_fold = |sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().direct_free_quota_pending_2m.view();
    assert(value_fold =~= direct_fold && s.fold(0int, value_fold) >= 0) by { lemma_set_fold_int_sum_nonneg(s, value); };
}

pub proof fn lemma_thread_indirect_pending_2m_fold_nonneg(s: Set<RwLockThreadPtr>, thread_map: ThreadLockedMap, depth: int)
    ensures
        thread_indirect_pending_2m_fold_sum_at_depth(s, thread_map, depth) >= 0,
{
    let value = |t: RwLockThreadPtr| thread_map.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
    let value_fold = |sum: int, t: RwLockThreadPtr| sum + value(t);
    let direct_fold = |sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth);
    assert(value_fold =~= direct_fold && s.fold(0int, value_fold) >= 0) by { lemma_set_fold_int_sum_nonneg(s, value); };
}

pub proof fn container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, allocator_2m_map: PageAllocatorUnLockedMap, old_process_map: ProcessLockedMap, new_process_map: ProcessLockedMap)
    requires
        container_process_allocator_quota_2m_wf(container_map, old_process_map, thread_map, allocator_2m_map),
        container_process_wf(container_map, old_process_map),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_2m(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==> process_effective_quota_2m(new_process_map.spec_index(p)) == process_effective_quota_2m(old_process_map.spec_index(p)),
    ensures
        container_process_allocator_quota_2m_wf(container_map, new_process_map, thread_map, allocator_2m_map),
{ reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); lemma_process_effective_quota_2m_fold_sum_eq_forall(); }

pub proof fn container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, allocator_1g_map: PageAllocatorUnLockedMap, old_process_map: ProcessLockedMap, new_process_map: ProcessLockedMap)
    requires
        container_process_allocator_quota_1g_wf(container_map, old_process_map, thread_map, allocator_1g_map),
        container_process_wf(container_map, old_process_map),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_1g(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==> process_effective_quota_1g(new_process_map.spec_index(p)) == process_effective_quota_1g(old_process_map.spec_index(p)),
    ensures
        container_process_allocator_quota_1g_wf(container_map, new_process_map, thread_map, allocator_1g_map),
{ reveal(container_process_allocator_quota_1g_wf); reveal(container_process_wf); lemma_process_effective_quota_1g_fold_sum_eq_forall(); }

pub proof fn container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, allocator_4k_map: PageAllocatorUnLockedMap, old_process_map: ProcessLockedMap, new_process_map: ProcessLockedMap)
    requires
        container_process_allocator_quota_4k_wf(container_map, old_process_map, thread_map, allocator_4k_map),
        container_process_wf(container_map, old_process_map),
        forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==> process_effective_quota_4k(new_process_map.spec_index(p)) == process_effective_quota_4k(old_process_map.spec_index(p)),
    ensures
        container_process_allocator_quota_4k_wf(container_map, new_process_map, thread_map, allocator_4k_map),
{ reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); lemma_process_effective_quota_4k_fold_sum_eq_forall(); }

// container_allocator_wf(old) is needed only to know each container's allocator_ptr_4k is in the old allocator dom.
pub proof fn container_process_allocator_quota_4k_wf_preserved_for_container_allocator_eq(
    old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, process_map: ProcessLockedMap, thread_map: ThreadLockedMap,
    old_allocator_4k_map: PageAllocatorUnLockedMap, new_allocator_4k_map: PageAllocatorUnLockedMap, allocator_2m_map: PageAllocatorUnLockedMap, allocator_1g_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_4k_wf(old_container_map, process_map, thread_map, old_allocator_4k_map),
        container_allocator_wf(old_container_map, old_allocator_4k_map, allocator_2m_map, allocator_1g_map),
        new_container_map.dom() == old_container_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> {
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_processes.view() == old_container_map.spec_index(c_ptr).view_ghost().owned_processes.view()
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_threads.view() == old_container_map.spec_index(c_ptr).view_ghost().owned_threads.view()
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view() == old_container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view()
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().depth == old_container_map.spec_index(c_ptr).view_rodata().view().depth
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k == old_container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k
            },
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger new_allocator_4k_map.spec_index(a_ptr)]
            old_allocator_4k_map.dom().contains(a_ptr) ==> {
                &&& new_allocator_4k_map.spec_index(a_ptr).quota.view().view() == old_allocator_4k_map.spec_index(a_ptr).quota.view().view()
                &&& new_allocator_4k_map.spec_index(a_ptr).total_free_pages.view() == old_allocator_4k_map.spec_index(a_ptr).total_free_pages.view()
            },
    ensures
        container_process_allocator_quota_4k_wf(new_container_map, process_map, thread_map, new_allocator_4k_map),
{ reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); }

// container_allocator_wf(old) is needed only to know each container's allocator_ptr_2m is in the old allocator dom.
pub proof fn container_process_allocator_quota_2m_wf_preserved_for_container_allocator_eq(
    old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, process_map: ProcessLockedMap, thread_map: ThreadLockedMap,
    old_allocator_2m_map: PageAllocatorUnLockedMap, new_allocator_2m_map: PageAllocatorUnLockedMap, allocator_4k_map: PageAllocatorUnLockedMap, allocator_1g_map: PageAllocatorUnLockedMap,
)
    requires
        container_process_allocator_quota_2m_wf(old_container_map, process_map, thread_map, old_allocator_2m_map),
        container_allocator_wf(old_container_map, allocator_4k_map, old_allocator_2m_map, allocator_1g_map),
        new_container_map.dom() == old_container_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> {
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_processes.view() == old_container_map.spec_index(c_ptr).view_ghost().owned_processes.view()
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_threads.view() == old_container_map.spec_index(c_ptr).view_ghost().owned_threads.view()
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view() == old_container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view()
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().depth == old_container_map.spec_index(c_ptr).view_rodata().view().depth
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m == old_container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m
            },
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger new_allocator_2m_map.spec_index(a_ptr)]
            old_allocator_2m_map.dom().contains(a_ptr) ==> {
                &&& new_allocator_2m_map.spec_index(a_ptr).quota.view().view() == old_allocator_2m_map.spec_index(a_ptr).quota.view().view()
                &&& new_allocator_2m_map.spec_index(a_ptr).total_free_pages.view() == old_allocator_2m_map.spec_index(a_ptr).total_free_pages.view()
            },
    ensures
        container_process_allocator_quota_2m_wf(new_container_map, process_map, thread_map, new_allocator_2m_map),
{ reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); }

pub proof fn lemma_process_effective_quota_4k_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_4k_fold_sum(s, post), process_effective_quota_4k_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p))) ==> process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (forall|p: RwLockProcessPtr| #![auto] s.contains(p) ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
    implies
        process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre)
    by { lemma_process_effective_quota_4k_fold_eq(s, pre, post); };
}

pub proof fn lemma_process_effective_quota_2m_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_2m_fold_sum(s, post), process_effective_quota_2m_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_2m(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_2m(post.spec_index(p)) == process_effective_quota_2m(pre.spec_index(p))) ==> process_effective_quota_2m_fold_sum(s, post) == process_effective_quota_2m_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (forall|p: RwLockProcessPtr| #![auto] s.contains(p) ==> process_effective_quota_2m(post.spec_index(p)) == process_effective_quota_2m(pre.spec_index(p)))
    implies
        process_effective_quota_2m_fold_sum(s, post) == process_effective_quota_2m_fold_sum(s, pre)
    by { lemma_process_effective_quota_2m_fold_eq(s, pre, post); };
}

pub proof fn lemma_process_effective_quota_1g_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_1g_fold_sum(s, post), process_effective_quota_1g_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_1g(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_1g(post.spec_index(p)) == process_effective_quota_1g(pre.spec_index(p))) ==> process_effective_quota_1g_fold_sum(s, post) == process_effective_quota_1g_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (forall|p: RwLockProcessPtr| #![auto] s.contains(p) ==> process_effective_quota_1g(post.spec_index(p)) == process_effective_quota_1g(pre.spec_index(p)))
    implies
        process_effective_quota_1g_fold_sum(s, post) == process_effective_quota_1g_fold_sum(s, pre)
    by { lemma_process_effective_quota_1g_fold_eq(s, pre, post); };
}

pub proof fn lemma_process_effective_quota_4k_fold_change_by_forall(mod_p: RwLockProcessPtr, x: int)
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_4k_fold_sum(s, post), process_effective_quota_4k_fold_sum(s, pre)]
            (s.contains(mod_p) && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(pre.spec_index(p))]
                s.contains(p) && p != mod_p ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
            ==> process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (s.contains(mod_p) && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x && forall|p: RwLockProcessPtr| #![auto] s.contains(p) && p != mod_p
            ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
    implies
        process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre) + x
    by { lemma_process_effective_quota_4k_fold_change_by(s, pre, post, mod_p, x); };
}

pub proof fn lemma_process_effective_quota_2m_fold_change_by_forall(mod_p: RwLockProcessPtr, x: int)
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_2m_fold_sum(s, post), process_effective_quota_2m_fold_sum(s, pre)]
            (s.contains(mod_p) && process_effective_quota_2m(post.spec_index(mod_p)) == process_effective_quota_2m(pre.spec_index(mod_p)) + x && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_2m(pre.spec_index(p))]
                s.contains(p) && p != mod_p ==> process_effective_quota_2m(post.spec_index(p)) == process_effective_quota_2m(pre.spec_index(p)))
            ==> process_effective_quota_2m_fold_sum(s, post) == process_effective_quota_2m_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (s.contains(mod_p) && process_effective_quota_2m(post.spec_index(mod_p)) == process_effective_quota_2m(pre.spec_index(mod_p)) + x && forall|p: RwLockProcessPtr| #![auto] s.contains(p) && p != mod_p
            ==> process_effective_quota_2m(post.spec_index(p)) == process_effective_quota_2m(pre.spec_index(p)))
    implies
        process_effective_quota_2m_fold_sum(s, post) == process_effective_quota_2m_fold_sum(s, pre) + x
    by { lemma_process_effective_quota_2m_fold_change_by(s, pre, post, mod_p, x); };
}

pub proof fn lemma_process_effective_quota_1g_fold_change_by_forall(mod_p: RwLockProcessPtr, x: int)
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_1g_fold_sum(s, post), process_effective_quota_1g_fold_sum(s, pre)]
            (s.contains(mod_p) && process_effective_quota_1g(post.spec_index(mod_p)) == process_effective_quota_1g(pre.spec_index(mod_p)) + x && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_1g(pre.spec_index(p))]
                s.contains(p) && p != mod_p ==> process_effective_quota_1g(post.spec_index(p)) == process_effective_quota_1g(pre.spec_index(p)))
            ==> process_effective_quota_1g_fold_sum(s, post) == process_effective_quota_1g_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap| #![auto]
        (s.contains(mod_p) && process_effective_quota_1g(post.spec_index(mod_p)) == process_effective_quota_1g(pre.spec_index(mod_p)) + x && forall|p: RwLockProcessPtr| #![auto] s.contains(p) && p != mod_p
            ==> process_effective_quota_1g(post.spec_index(p)) == process_effective_quota_1g(pre.spec_index(p)))
    implies
        process_effective_quota_1g_fold_sum(s, post) == process_effective_quota_1g_fold_sum(s, pre) + x
    by { lemma_process_effective_quota_1g_fold_change_by(s, pre, post, mod_p, x); };
}

pub proof fn lemma_thread_effective_quota_4k_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_4k_fold_sum(s, post), thread_effective_quota_4k_fold_sum(s, pre)]
            (forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_4k(pre.spec_index(t))]
                s.contains(t) ==> thread_effective_quota_4k(post.spec_index(t)) == thread_effective_quota_4k(pre.spec_index(t))) ==> thread_effective_quota_4k_fold_sum(s, post) == thread_effective_quota_4k_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (forall|t: RwLockThreadPtr| #![auto] s.contains(t) ==> thread_effective_quota_4k(post.spec_index(t)) == thread_effective_quota_4k(pre.spec_index(t)))
        implies thread_effective_quota_4k_fold_sum(s, post) == thread_effective_quota_4k_fold_sum(s, pre)
    by { lemma_thread_effective_quota_4k_fold_eq(s, pre, post); };
}
pub proof fn lemma_thread_effective_quota_4k_fold_change_by_forall(mod_t: RwLockThreadPtr, x: int)
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_4k_fold_sum(s, post), thread_effective_quota_4k_fold_sum(s, pre)]
            (s.contains(mod_t) && thread_effective_quota_4k(post.spec_index(mod_t)) == thread_effective_quota_4k(pre.spec_index(mod_t)) + x && forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_4k(pre.spec_index(t))]
                s.contains(t) && t != mod_t ==> thread_effective_quota_4k(post.spec_index(t)) == thread_effective_quota_4k(pre.spec_index(t)))
            ==> thread_effective_quota_4k_fold_sum(s, post) == thread_effective_quota_4k_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (s.contains(mod_t) && thread_effective_quota_4k(post.spec_index(mod_t)) == thread_effective_quota_4k(pre.spec_index(mod_t)) + x && forall|t: RwLockThreadPtr| #![auto] s.contains(t) && t != mod_t
            ==> thread_effective_quota_4k(post.spec_index(t)) == thread_effective_quota_4k(pre.spec_index(t)))
        implies thread_effective_quota_4k_fold_sum(s, post) == thread_effective_quota_4k_fold_sum(s, pre) + x
    by { lemma_thread_effective_quota_4k_fold_change_by(s, pre, post, mod_t, x); };
}

pub proof fn lemma_thread_effective_quota_2m_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_2m_fold_sum(s, post), thread_effective_quota_2m_fold_sum(s, pre)]
            (forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_2m(pre.spec_index(t))]
                s.contains(t) ==> thread_effective_quota_2m(post.spec_index(t)) == thread_effective_quota_2m(pre.spec_index(t))) ==> thread_effective_quota_2m_fold_sum(s, post) == thread_effective_quota_2m_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (forall|t: RwLockThreadPtr| #![auto] s.contains(t) ==> thread_effective_quota_2m(post.spec_index(t)) == thread_effective_quota_2m(pre.spec_index(t)))
        implies thread_effective_quota_2m_fold_sum(s, post) == thread_effective_quota_2m_fold_sum(s, pre)
    by { lemma_thread_effective_quota_2m_fold_eq(s, pre, post); };
}

pub proof fn lemma_thread_effective_quota_2m_fold_change_by_forall(mod_t: RwLockThreadPtr, x: int)
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_2m_fold_sum(s, post), thread_effective_quota_2m_fold_sum(s, pre)]
            (s.subset_of(pre.dom()) && post.dom() == pre.dom() && s.contains(mod_t) && thread_effective_quota_2m(post.spec_index(mod_t)) == thread_effective_quota_2m(pre.spec_index(mod_t)) + x && forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_2m(pre.spec_index(t))]
                s.contains(t) && t != mod_t ==> thread_effective_quota_2m(post.spec_index(t)) == thread_effective_quota_2m(pre.spec_index(t)))
            ==> thread_effective_quota_2m_fold_sum(s, post) == thread_effective_quota_2m_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (s.subset_of(pre.dom()) && post.dom() == pre.dom() && s.contains(mod_t) && thread_effective_quota_2m(post.spec_index(mod_t)) == thread_effective_quota_2m(pre.spec_index(mod_t)) + x
            && forall|t: RwLockThreadPtr| #![auto] s.contains(t) && t != mod_t ==> thread_effective_quota_2m(post.spec_index(t)) == thread_effective_quota_2m(pre.spec_index(t)))
        implies thread_effective_quota_2m_fold_sum(s, post) == thread_effective_quota_2m_fold_sum(s, pre) + x
    by { lemma_thread_effective_quota_2m_fold_change_by(s, pre, post, mod_t, x); };
}

pub proof fn lemma_container_process_thread_quota_folds_insert_zero_forall(
    root: RwLockContainerPtr, pre_ctn: ContainerLockedMap, post_ctn: ContainerLockedMap, pre_prc: ProcessLockedMap, post_prc: ProcessLockedMap,
    pre_thr: ThreadLockedMap, post_thr: ThreadLockedMap, dc: RwLockContainerPtr, new_t: RwLockThreadPtr,
)
    requires
        container_process_wf(pre_ctn, pre_prc),
        container_thread_wf(pre_ctn, pre_thr),
        container_uppertree_seq_wf(root, pre_ctn),
        pre_ctn.dom().contains(dc),
        post_ctn.dom() == pre_ctn.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c)]
            pre_ctn.dom().contains(c) ==> {
                &&& post_ctn.spec_index(c).view() == pre_ctn.spec_index(c).view()
                &&& post_ctn.spec_index(c).view_rodata() == pre_ctn.spec_index(c).view_rodata()
                &&& post_ctn.spec_index(c).view_ghost() == ContainerGhost {
                        uppertree_seq: pre_ctn.spec_index(c).view_ghost().uppertree_seq,
                        subtree_set: pre_ctn.spec_index(c).view_ghost().subtree_set,
                        owned_processes: pre_ctn.spec_index(c).view_ghost().owned_processes,
                        owned_threads: if c == dc {
                            Ghost(pre_ctn.spec_index(c).view_ghost().owned_threads.view().insert(new_t))
                        } else {
                            pre_ctn.spec_index(c).view_ghost().owned_threads
                        },
                        owned_indirect_threads: if pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set().contains(c) {
                            Ghost(pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view().insert(new_t))
                        } else {
                            pre_ctn.spec_index(c).view_ghost().owned_indirect_threads
                        },
                        owned_endpoints: pre_ctn.spec_index(c).view_ghost().owned_endpoints,
                    }
            },
        pre_prc.dom().subset_of(post_prc.dom()),
        forall|p: RwLockProcessPtr|
            #![trigger post_prc.spec_index(p).view()]
            pre_prc.dom().contains(p) ==> {
                &&& process_effective_quota_4k(post_prc.spec_index(p)) == process_effective_quota_4k(pre_prc.spec_index(p))
                &&& process_effective_quota_2m(post_prc.spec_index(p)) == process_effective_quota_2m(pre_prc.spec_index(p))
                &&& process_effective_quota_1g(post_prc.spec_index(p)) == process_effective_quota_1g(pre_prc.spec_index(p))
            },
        !pre_thr.dom().contains(new_t),
        pre_thr.dom().subset_of(post_thr.dom()),
        post_thr.dom().contains(new_t),
        post_thr.spec_index(new_t).inv(),
        post_thr.spec_index(new_t).view().upper_container_seq == pre_ctn.spec_index(dc).view_ghost().uppertree_seq,
        forall|t: RwLockThreadPtr|
            #![trigger post_thr.spec_index(t).view()]
            pre_thr.dom().contains(t) ==> {
                &&& thread_effective_quota_4k(post_thr.spec_index(t)) == thread_effective_quota_4k(pre_thr.spec_index(t))
                &&& thread_effective_quota_2m(post_thr.spec_index(t)) == thread_effective_quota_2m(pre_thr.spec_index(t))
                &&& thread_effective_quota_1g(post_thr.spec_index(t)) == thread_effective_quota_1g(pre_thr.spec_index(t))
                &&& post_thr.spec_index(t).view().free_quota_pending_fields_unchanged(&pre_thr.spec_index(t).view())
            },
        thread_effective_quota_4k(post_thr.spec_index(new_t)) == 0,
        thread_effective_quota_2m(post_thr.spec_index(new_t)) == 0,
        thread_effective_quota_1g(post_thr.spec_index(new_t)) == 0,
        post_thr.spec_index(new_t).view().free_quota_pending_clean(),
    ensures
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_4k]
            post_ctn.dom().contains(c) ==> {
                let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
                let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_4k_fold_sum(post_processes, post_prc) == process_effective_quota_4k_fold_sum(pre_processes, pre_prc)
                &&& thread_effective_quota_4k_fold_sum(post_direct, post_thr) == thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_2m]
            post_ctn.dom().contains(c) ==> {
                let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
                let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_2m_fold_sum(post_processes, post_prc) == process_effective_quota_2m_fold_sum(pre_processes, pre_prc)
                &&& thread_effective_quota_2m_fold_sum(post_direct, post_thr) == thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_1g]
            post_ctn.dom().contains(c) ==> {
                let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
                let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_1g_fold_sum(post_processes, post_prc) == process_effective_quota_1g_fold_sum(pre_processes, pre_prc)
                &&& thread_effective_quota_1g_fold_sum(post_direct, post_thr) == thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
{
    let uppers = pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set();
    assert forall|c: RwLockContainerPtr|
        #![trigger post_ctn.dom().contains(c)]
        post_ctn.dom().contains(c) implies {
            let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
            let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
            let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
            let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
            let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
            let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
            let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
            &&& process_effective_quota_4k_fold_sum(post_processes, post_prc) == process_effective_quota_4k_fold_sum(pre_processes, pre_prc)
            &&& thread_effective_quota_4k_fold_sum(post_direct, post_thr) == thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            &&& process_effective_quota_2m_fold_sum(post_processes, post_prc) == process_effective_quota_2m_fold_sum(pre_processes, pre_prc)
            &&& thread_effective_quota_2m_fold_sum(post_direct, post_thr) == thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            &&& process_effective_quota_1g_fold_sum(post_processes, post_prc) == process_effective_quota_1g_fold_sum(pre_processes, pre_prc)
            &&& thread_effective_quota_1g_fold_sum(post_direct, post_thr) == thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
        }
    by {
        reveal(container_process_wf);
        reveal(container_thread_wf);
        let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
        let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
        let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
        let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
        let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
        lemma_process_effective_quota_4k_fold_eq(pre_processes, pre_prc, post_prc);
        lemma_process_effective_quota_2m_fold_eq(pre_processes, pre_prc, post_prc);
        lemma_process_effective_quota_1g_fold_eq(pre_processes, pre_prc, post_prc);
        if c == dc {
            lemma_thread_effective_quota_4k_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_direct_pending_4k_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_effective_quota_2m_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_direct_pending_2m_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_effective_quota_1g_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
            lemma_thread_direct_pending_1g_fold_insert_zero(pre_direct, pre_thr, post_thr, new_t);
        } else {
            lemma_thread_effective_quota_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_1g_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_1g_fold_eq(pre_direct, pre_thr, post_thr);
        }
        if uppers.contains(c) {
            assert({
                &&& 0 <= depth < post_thr.spec_index(new_t).view().indirect_free_quota_pending_4k.view().len()
                &&& 0 <= depth < post_thr.spec_index(new_t).view().indirect_free_quota_pending_2m.view().len()
                &&& 0 <= depth < post_thr.spec_index(new_t).view().indirect_free_quota_pending_1g.view().len()
                &&& post_thr.spec_index(new_t).view().indirect_free_quota_pending_4k.view().spec_index(depth) == 0
                &&& post_thr.spec_index(new_t).view().indirect_free_quota_pending_2m.view().spec_index(depth) == 0
                &&& post_thr.spec_index(new_t).view().indirect_free_quota_pending_1g.view().spec_index(depth) == 0
            }) by { pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set_ensures(); reveal(container_uppertree_seq_wf); };
            lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(pre_indirect, pre_thr, post_thr, new_t, depth);
            lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(pre_indirect, pre_thr, post_thr, new_t, depth);
            lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(pre_indirect, pre_thr, post_thr, new_t, depth);
        } else {
            lemma_thread_indirect_pending_4k_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_2m_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_1g_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
        }
    };
}

/// Removing exiting thread `old_t` from its direct container `dc` and every upper container while its
/// quota moves to its process `proc_ptr` keeps every container's process-plus-thread folds and pending folds.
pub proof fn lemma_container_process_thread_quota_folds_remove_thread_forall(
    root: RwLockContainerPtr, pre_ctn: ContainerLockedMap, post_ctn: ContainerLockedMap, pre_prc: ProcessLockedMap, post_prc: ProcessLockedMap,
    pre_thr: ThreadLockedMap, post_thr: ThreadLockedMap, dc: RwLockContainerPtr, old_t: RwLockThreadPtr, proc_ptr: RwLockProcessPtr,
)
    requires
        container_process_wf(pre_ctn, pre_prc),
        container_thread_wf(pre_ctn, pre_thr),
        container_uppertree_seq_wf(root, pre_ctn),
        pre_ctn.dom().contains(dc),
        pre_thr.dom().contains(old_t),
        pre_thr.spec_index(old_t).view().owning_container == dc,
        pre_thr.spec_index(old_t).inv(),
        pre_thr.spec_index(old_t).view().free_quota_pending_clean(),
        pre_prc.dom().contains(proc_ptr),
        pre_prc.spec_index(proc_ptr).view_rodata().view().owning_container == dc,
        post_ctn.dom() == pre_ctn.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c)]
            pre_ctn.dom().contains(c) ==> {
                &&& post_ctn.spec_index(c).view_rodata() == pre_ctn.spec_index(c).view_rodata()
                &&& post_ctn.spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: pre_ctn.spec_index(c).view_ghost().uppertree_seq, subtree_set: pre_ctn.spec_index(c).view_ghost().subtree_set,
                    owned_processes: pre_ctn.spec_index(c).view_ghost().owned_processes,
                    owned_threads: if c == dc { Ghost(pre_ctn.spec_index(c).view_ghost().owned_threads.view().remove(old_t)) } else { pre_ctn.spec_index(c).view_ghost().owned_threads },
                    owned_indirect_threads: if pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set().contains(c) {
                        Ghost(pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view().remove(old_t))
                    } else { pre_ctn.spec_index(c).view_ghost().owned_indirect_threads },
                    owned_endpoints: pre_ctn.spec_index(c).view_ghost().owned_endpoints,
                }
            },
        post_prc.dom() == pre_prc.dom(),
        forall|p: RwLockProcessPtr|
            #![trigger post_prc.spec_index(p).view()]
            pre_prc.dom().contains(p) && p != proc_ptr ==> {
                &&& process_effective_quota_4k(post_prc.spec_index(p)) == process_effective_quota_4k(pre_prc.spec_index(p))
                &&& process_effective_quota_2m(post_prc.spec_index(p)) == process_effective_quota_2m(pre_prc.spec_index(p))
                &&& process_effective_quota_1g(post_prc.spec_index(p)) == process_effective_quota_1g(pre_prc.spec_index(p))
            },
        process_effective_quota_4k(post_prc.spec_index(proc_ptr)) == process_effective_quota_4k(pre_prc.spec_index(proc_ptr)) + thread_effective_quota_4k(pre_thr.spec_index(old_t)),
        process_effective_quota_2m(post_prc.spec_index(proc_ptr)) == process_effective_quota_2m(pre_prc.spec_index(proc_ptr)) + thread_effective_quota_2m(pre_thr.spec_index(old_t)),
        process_effective_quota_1g(post_prc.spec_index(proc_ptr)) == process_effective_quota_1g(pre_prc.spec_index(proc_ptr)) + thread_effective_quota_1g(pre_thr.spec_index(old_t)),
        post_thr.dom() == pre_thr.dom().remove(old_t),
        forall|t: RwLockThreadPtr|
            #![trigger post_thr.spec_index(t).view()]
            post_thr.dom().contains(t) ==> {
                &&& thread_effective_quota_4k(post_thr.spec_index(t)) == thread_effective_quota_4k(pre_thr.spec_index(t))
                &&& thread_effective_quota_2m(post_thr.spec_index(t)) == thread_effective_quota_2m(pre_thr.spec_index(t))
                &&& thread_effective_quota_1g(post_thr.spec_index(t)) == thread_effective_quota_1g(pre_thr.spec_index(t))
                &&& post_thr.spec_index(t).view().free_quota_pending_fields_unchanged(&pre_thr.spec_index(t).view())
            },
    ensures
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_4k]
            post_ctn.dom().contains(c) ==> {
                let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
                let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_4k_fold_sum(post_processes, post_prc) + thread_effective_quota_4k_fold_sum(post_direct, post_thr) == process_effective_quota_4k_fold_sum(pre_processes, pre_prc) + thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_2m]
            post_ctn.dom().contains(c) ==> {
                let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
                let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_2m_fold_sum(post_processes, post_prc) + thread_effective_quota_2m_fold_sum(post_direct, post_thr) == process_effective_quota_2m_fold_sum(pre_processes, pre_prc) + thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_1g]
            post_ctn.dom().contains(c) ==> {
                let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
                let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_1g_fold_sum(post_processes, post_prc) + thread_effective_quota_1g_fold_sum(post_direct, post_thr) == process_effective_quota_1g_fold_sum(pre_processes, pre_prc) + thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
{
    let uppers = pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set();
    assert forall|c: RwLockContainerPtr|
        #![trigger post_ctn.dom().contains(c)]
        post_ctn.dom().contains(c) implies {
            let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
            let post_processes = post_ctn.spec_index(c).view_ghost().owned_processes.view();
            let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
            let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
            let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
            let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
            let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
            &&& process_effective_quota_4k_fold_sum(post_processes, post_prc) + thread_effective_quota_4k_fold_sum(post_direct, post_thr) == process_effective_quota_4k_fold_sum(pre_processes, pre_prc) + thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            &&& process_effective_quota_2m_fold_sum(post_processes, post_prc) + thread_effective_quota_2m_fold_sum(post_direct, post_thr) == process_effective_quota_2m_fold_sum(pre_processes, pre_prc) + thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            &&& process_effective_quota_1g_fold_sum(post_processes, post_prc) + thread_effective_quota_1g_fold_sum(post_direct, post_thr) == process_effective_quota_1g_fold_sum(pre_processes, pre_prc) + thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
            &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
            &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
        }
    by {
        reveal(container_process_wf);
        reveal(container_thread_wf);
        let pre_processes = pre_ctn.spec_index(c).view_ghost().owned_processes.view();
        let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
        let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
        let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
        if c == dc {
            let x4k = thread_effective_quota_4k(pre_thr.spec_index(old_t));
            let x2m = thread_effective_quota_2m(pre_thr.spec_index(old_t));
            let x1g = thread_effective_quota_1g(pre_thr.spec_index(old_t));
            lemma_process_effective_quota_4k_fold_change_by(pre_processes, pre_prc, post_prc, proc_ptr, x4k);
            lemma_process_effective_quota_2m_fold_change_by(pre_processes, pre_prc, post_prc, proc_ptr, x2m);
            lemma_process_effective_quota_1g_fold_change_by(pre_processes, pre_prc, post_prc, proc_ptr, x1g);
            lemma_thread_effective_quota_4k_fold_remove(pre_direct, pre_thr, post_thr, old_t);
            lemma_thread_effective_quota_2m_fold_remove(pre_direct, pre_thr, post_thr, old_t);
            lemma_thread_effective_quota_1g_fold_remove(pre_direct, pre_thr, post_thr, old_t);
            assert(pre_direct.remove(old_t).insert(old_t) =~= pre_direct);
            lemma_thread_direct_pending_4k_fold_insert_zero(post_direct, post_thr, pre_thr, old_t);
            lemma_thread_direct_pending_2m_fold_insert_zero(post_direct, post_thr, pre_thr, old_t);
            lemma_thread_direct_pending_1g_fold_insert_zero(post_direct, post_thr, pre_thr, old_t);
        } else {
            lemma_process_effective_quota_4k_fold_eq(pre_processes, pre_prc, post_prc);
            lemma_process_effective_quota_2m_fold_eq(pre_processes, pre_prc, post_prc);
            lemma_process_effective_quota_1g_fold_eq(pre_processes, pre_prc, post_prc);
            lemma_thread_effective_quota_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_1g_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_1g_fold_eq(pre_direct, pre_thr, post_thr);
        }
        if uppers.contains(c) {
            assert({
                &&& 0 <= depth < pre_thr.spec_index(old_t).view().indirect_free_quota_pending_4k.view().len()
                &&& 0 <= depth < pre_thr.spec_index(old_t).view().indirect_free_quota_pending_2m.view().len()
                &&& 0 <= depth < pre_thr.spec_index(old_t).view().indirect_free_quota_pending_1g.view().len()
                &&& pre_indirect.contains(old_t)
            }) by { pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set_ensures(); reveal(container_uppertree_seq_wf); };
            assert(pre_indirect.remove(old_t).insert(old_t) =~= pre_indirect);
            lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(post_indirect, post_thr, pre_thr, old_t, depth);
            lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(post_indirect, post_thr, pre_thr, old_t, depth);
            lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(post_indirect, post_thr, pre_thr, old_t, depth);
        } else {
            assert(!pre_indirect.contains(old_t)) by { pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set_ensures(); };
            lemma_thread_indirect_pending_4k_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_2m_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_1g_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
        }
    };
}

/// Removing thread `old_t`, which holds no quota and no pending free, from its direct container `dc` and every upper
/// container keeps every container's thread folds and pending folds.
pub proof fn lemma_container_thread_quota_folds_remove_empty_thread_forall(
    root: RwLockContainerPtr, pre_ctn: ContainerLockedMap, post_ctn: ContainerLockedMap, pre_thr: ThreadLockedMap, post_thr: ThreadLockedMap,
    dc: RwLockContainerPtr, old_t: RwLockThreadPtr,
)
    requires
        container_thread_wf(pre_ctn, pre_thr),
        container_uppertree_seq_wf(root, pre_ctn),
        pre_ctn.dom().contains(dc),
        pre_thr.dom().contains(old_t),
        pre_thr.spec_index(old_t).view().owning_container == dc,
        pre_thr.spec_index(old_t).inv(),
        pre_thr.spec_index(old_t).view().free_quota_pending_clean(),
        thread_effective_quota_4k(pre_thr.spec_index(old_t)) == 0,
        thread_effective_quota_2m(pre_thr.spec_index(old_t)) == 0,
        thread_effective_quota_1g(pre_thr.spec_index(old_t)) == 0,
        post_ctn.dom() == pre_ctn.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c)]
            pre_ctn.dom().contains(c) ==> {
                &&& post_ctn.spec_index(c).view_rodata() == pre_ctn.spec_index(c).view_rodata()
                &&& post_ctn.spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: pre_ctn.spec_index(c).view_ghost().uppertree_seq, subtree_set: pre_ctn.spec_index(c).view_ghost().subtree_set,
                    owned_processes: pre_ctn.spec_index(c).view_ghost().owned_processes,
                    owned_threads: if c == dc { Ghost(pre_ctn.spec_index(c).view_ghost().owned_threads.view().remove(old_t)) } else { pre_ctn.spec_index(c).view_ghost().owned_threads },
                    owned_indirect_threads: if pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set().contains(c) {
                        Ghost(pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view().remove(old_t))
                    } else { pre_ctn.spec_index(c).view_ghost().owned_indirect_threads },
                    owned_endpoints: pre_ctn.spec_index(c).view_ghost().owned_endpoints,
                }
            },
        post_thr.dom() == pre_thr.dom().remove(old_t),
        forall|t: RwLockThreadPtr|
            #![trigger post_thr.spec_index(t).view()]
            post_thr.dom().contains(t) ==> {
                &&& thread_effective_quota_4k(post_thr.spec_index(t)) == thread_effective_quota_4k(pre_thr.spec_index(t))
                &&& thread_effective_quota_2m(post_thr.spec_index(t)) == thread_effective_quota_2m(pre_thr.spec_index(t))
                &&& thread_effective_quota_1g(post_thr.spec_index(t)) == thread_effective_quota_1g(pre_thr.spec_index(t))
                &&& post_thr.spec_index(t).view().free_quota_pending_fields_unchanged(&pre_thr.spec_index(t).view())
            },
    ensures
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_4k]
            post_ctn.dom().contains(c) ==> {
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& thread_effective_quota_4k_fold_sum(post_direct, post_thr) == thread_effective_quota_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_4k_fold_sum(post_direct, post_thr) == thread_direct_pending_4k_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_2m]
            post_ctn.dom().contains(c) ==> {
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& thread_effective_quota_2m_fold_sum(post_direct, post_thr) == thread_effective_quota_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_2m_fold_sum(post_direct, post_thr) == thread_direct_pending_2m_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_2m_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger post_ctn.spec_index(c).view_rodata().view().allocator_ptr_1g]
            post_ctn.dom().contains(c) ==> {
                let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
                let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
                let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
                &&& thread_effective_quota_1g_fold_sum(post_direct, post_thr) == thread_effective_quota_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_direct_pending_1g_fold_sum(post_direct, post_thr) == thread_direct_pending_1g_fold_sum(pre_direct, pre_thr)
                &&& thread_indirect_pending_1g_fold_sum_at_depth(post_indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(pre_indirect, pre_thr, depth)
            },
{
    let uppers = pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set();
    assert forall|c: RwLockContainerPtr|
        #![trigger post_ctn.dom().contains(c)]
        post_ctn.dom().contains(c) implies {
            let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
            let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
            let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
            let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
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
        let pre_direct = pre_ctn.spec_index(c).view_ghost().owned_threads.view();
        let post_direct = post_ctn.spec_index(c).view_ghost().owned_threads.view();
        let pre_indirect = pre_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let post_indirect = post_ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let depth = post_ctn.spec_index(c).view_rodata().view().depth as int;
        if c == dc {
            lemma_thread_effective_quota_4k_fold_remove(pre_direct, pre_thr, post_thr, old_t);
            lemma_thread_effective_quota_2m_fold_remove(pre_direct, pre_thr, post_thr, old_t);
            lemma_thread_effective_quota_1g_fold_remove(pre_direct, pre_thr, post_thr, old_t);
            lemma_thread_direct_pending_4k_fold_insert_zero(post_direct, post_thr, pre_thr, old_t);
            lemma_thread_direct_pending_2m_fold_insert_zero(post_direct, post_thr, pre_thr, old_t);
            lemma_thread_direct_pending_1g_fold_insert_zero(post_direct, post_thr, pre_thr, old_t);
        } else {
            lemma_thread_effective_quota_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_4k_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_2m_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_effective_quota_1g_fold_eq(pre_direct, pre_thr, post_thr);
            lemma_thread_direct_pending_1g_fold_eq(pre_direct, pre_thr, post_thr);
        }
        if uppers.contains(c) {
            assert({
                &&& 0 <= depth < pre_thr.spec_index(old_t).view().indirect_free_quota_pending_4k.view().len()
                &&& 0 <= depth < pre_thr.spec_index(old_t).view().indirect_free_quota_pending_2m.view().len()
                &&& 0 <= depth < pre_thr.spec_index(old_t).view().indirect_free_quota_pending_1g.view().len()
                &&& pre_indirect.contains(old_t)
            }) by { pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set_ensures(); reveal(container_uppertree_seq_wf); };
            lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(post_indirect, post_thr, pre_thr, old_t, depth);
            lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(post_indirect, post_thr, pre_thr, old_t, depth);
            lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(post_indirect, post_thr, pre_thr, old_t, depth);
        } else {
            assert(!pre_indirect.contains(old_t)) by { pre_ctn.spec_index(dc).view_ghost().uppertree_seq.view().to_set_ensures(); };
            lemma_thread_indirect_pending_4k_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_2m_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
            lemma_thread_indirect_pending_1g_fold_eq_at_depth(pre_indirect, pre_thr, post_thr, depth);
        }
    };
}

pub proof fn lemma_thread_pending_4k_folds_change_by_forall(mod_t: RwLockThreadPtr, direct_delta: int, changed_depth: int, indirect_delta: int)
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_direct_pending_4k_fold_sum(s, post), thread_direct_pending_4k_fold_sum(s, pre)]
            (forall|t: RwLockThreadPtr| #![trigger pre.spec_index(t).view().direct_free_quota_pending_4k.view()]
                s.contains(t) ==> post.spec_index(t).view().direct_free_quota_pending_4k.view() == pre.spec_index(t).view().direct_free_quota_pending_4k.view() + if t == mod_t { direct_delta } else { 0int })
            ==> thread_direct_pending_4k_fold_sum(s, post) == thread_direct_pending_4k_fold_sum(s, pre) + if s.contains(mod_t) { direct_delta } else { 0int },
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap, depth: int|
            #![trigger thread_indirect_pending_4k_fold_sum_at_depth(s, post, depth), thread_indirect_pending_4k_fold_sum_at_depth(s, pre, depth)]
            (forall|t: RwLockThreadPtr| #![trigger pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth)]
                s.contains(t) ==> post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) == pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) + if t == mod_t && depth == changed_depth { indirect_delta } else { 0int })
            ==> thread_indirect_pending_4k_fold_sum_at_depth(s, post, depth) == thread_indirect_pending_4k_fold_sum_at_depth(s, pre, depth) + if s.contains(mod_t) && depth == changed_depth { indirect_delta } else { 0int },
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (forall|t: RwLockThreadPtr| #![trigger pre.spec_index(t).view().direct_free_quota_pending_4k.view()]
                s.contains(t) ==> post.spec_index(t).view().direct_free_quota_pending_4k.view() == pre.spec_index(t).view().direct_free_quota_pending_4k.view() + if t == mod_t { direct_delta } else { 0int })
        implies thread_direct_pending_4k_fold_sum(s, post) == thread_direct_pending_4k_fold_sum(s, pre) + if s.contains(mod_t) { direct_delta } else { 0int }
    by {
        let pre_value = |t: RwLockThreadPtr| pre.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
        let post_value = |t: RwLockThreadPtr| post.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
        let delta = direct_delta;
        assert({
            &&& (|sum: int, t: RwLockThreadPtr| sum + pre_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + pre.spec_index(t).view().direct_free_quota_pending_4k.view())
            &&& (|sum: int, t: RwLockThreadPtr| sum + post_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + post.spec_index(t).view().direct_free_quota_pending_4k.view())
            &&& s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + post_value(t)) == s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + pre_value(t)) + if s.contains(mod_t) { delta } else { 0int }
        }) by {
            if s.contains(mod_t) { lemma_set_fold_int_sum_change_by(s, pre_value, post_value, mod_t, delta); }
            else { lemma_set_fold_int_sum_congruence(s, post_value, pre_value); }
        };
    };
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap, depth: int| #![auto]
        (forall|t: RwLockThreadPtr| #![trigger pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth)]
                s.contains(t) ==> post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) == pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) + if t == mod_t && depth == changed_depth { indirect_delta } else { 0int })
        implies thread_indirect_pending_4k_fold_sum_at_depth(s, post, depth) == thread_indirect_pending_4k_fold_sum_at_depth(s, pre, depth) + if s.contains(mod_t) && depth == changed_depth { indirect_delta } else { 0int }
    by {
        let pre_value = |t: RwLockThreadPtr| pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
        let post_value = |t: RwLockThreadPtr| post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
        let delta = if depth == changed_depth { indirect_delta } else { 0int };
        assert({
            &&& (|sum: int, t: RwLockThreadPtr| sum + pre_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + pre.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth))
            &&& (|sum: int, t: RwLockThreadPtr| sum + post_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + post.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth))
            &&& s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + post_value(t)) == s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + pre_value(t)) + if s.contains(mod_t) { delta } else { 0int }
        }) by {
            if s.contains(mod_t) { lemma_set_fold_int_sum_change_by(s, pre_value, post_value, mod_t, delta); }
            else { lemma_set_fold_int_sum_congruence(s, post_value, pre_value); }
        };
    };
}

pub proof fn lemma_thread_pending_4k_folds_eq_forall(container_map: ContainerLockedMap, pre: ThreadLockedMap, post: ThreadLockedMap)
    requires
        container_thread_wf(container_map, pre),
        post.dom() =~= pre.dom(),
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t)]
            pre.dom().contains(t)
                ==> post.spec_index(t).view().direct_free_quota_pending_4k == pre.spec_index(t).view().direct_free_quota_pending_4k
                && post.spec_index(t).view().indirect_free_quota_pending_4k == pre.spec_index(t).view().indirect_free_quota_pending_4k,
    ensures
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) ==> {
                let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
                let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
                let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                &&& thread_direct_pending_4k_fold_sum(direct, post) == thread_direct_pending_4k_fold_sum(direct, pre)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(indirect, post, depth) == thread_indirect_pending_4k_fold_sum_at_depth(indirect, pre, depth)
            },
{
    assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) implies {
                let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
                let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
                let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                &&& thread_direct_pending_4k_fold_sum(direct, post) == thread_direct_pending_4k_fold_sum(direct, pre)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(indirect, post, depth) == thread_indirect_pending_4k_fold_sum_at_depth(indirect, pre, depth)
            }
        by {
            let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
            let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
            let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
            assert(direct.subset_of(pre.dom())) by { reveal(container_thread_wf); };
            assert(indirect.subset_of(pre.dom())) by { reveal(container_thread_wf); };
            lemma_thread_direct_pending_4k_fold_eq(direct, pre, post);
            lemma_thread_indirect_pending_4k_fold_eq_at_depth(indirect, pre, post, depth);
    };
}

pub proof fn lemma_thread_pending_2m_folds_eq_forall(container_map: ContainerLockedMap, pre: ThreadLockedMap, post: ThreadLockedMap)
    requires
        container_thread_wf(container_map, pre),
        post.dom() =~= pre.dom(),
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t)]
            pre.dom().contains(t)
                ==> post.spec_index(t).view().direct_free_quota_pending_2m == pre.spec_index(t).view().direct_free_quota_pending_2m
                && post.spec_index(t).view().indirect_free_quota_pending_2m == pre.spec_index(t).view().indirect_free_quota_pending_2m,
    ensures
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) ==> {
                let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
                let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
                let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                &&& thread_direct_pending_2m_fold_sum(direct, post) == thread_direct_pending_2m_fold_sum(direct, pre)
                &&& thread_indirect_pending_2m_fold_sum_at_depth(indirect, post, depth) == thread_indirect_pending_2m_fold_sum_at_depth(indirect, pre, depth)
            },
{
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr) implies {
            let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
            let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
            let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
            &&& thread_direct_pending_2m_fold_sum(direct, post) == thread_direct_pending_2m_fold_sum(direct, pre)
            &&& thread_indirect_pending_2m_fold_sum_at_depth(indirect, post, depth) == thread_indirect_pending_2m_fold_sum_at_depth(indirect, pre, depth)
        }
    by {
        let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
        let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
        let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
        assert(direct.subset_of(pre.dom())) by { reveal(container_thread_wf); };
        assert(indirect.subset_of(pre.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_2m_fold_eq(direct, pre, post);
        lemma_thread_indirect_pending_2m_fold_eq_at_depth(indirect, pre, post, depth);
    };
}

pub proof fn lemma_thread_effective_quota_1g_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap|
            #![trigger thread_effective_quota_1g_fold_sum(s, post), thread_effective_quota_1g_fold_sum(s, pre)]
            (forall|t: RwLockThreadPtr|
                #![trigger thread_effective_quota_1g(pre.spec_index(t))]
                s.contains(t) ==> thread_effective_quota_1g(post.spec_index(t)) == thread_effective_quota_1g(pre.spec_index(t))) ==> thread_effective_quota_1g_fold_sum(s, post) == thread_effective_quota_1g_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap| #![auto]
        (forall|t: RwLockThreadPtr| #![auto] s.contains(t) ==> thread_effective_quota_1g(post.spec_index(t)) == thread_effective_quota_1g(pre.spec_index(t)))
        implies thread_effective_quota_1g_fold_sum(s, post) == thread_effective_quota_1g_fold_sum(s, pre)
    by { lemma_thread_effective_quota_1g_fold_eq(s, pre, post); };
}

pub proof fn lemma_thread_pending_1g_folds_eq_forall(container_map: ContainerLockedMap, pre: ThreadLockedMap, post: ThreadLockedMap)
    requires
        container_thread_wf(container_map, pre),
        post.dom() =~= pre.dom(),
        forall|t: RwLockThreadPtr|
            #![trigger pre.spec_index(t)]
            pre.dom().contains(t) ==>
                post.spec_index(t).view().direct_free_quota_pending_1g == pre.spec_index(t).view().direct_free_quota_pending_1g
                && post.spec_index(t).view().indirect_free_quota_pending_1g == pre.spec_index(t).view().indirect_free_quota_pending_1g,
    ensures
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) ==> {
                let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
                let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
                let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                &&& thread_direct_pending_1g_fold_sum(direct, post) == thread_direct_pending_1g_fold_sum(direct, pre)
                &&& thread_indirect_pending_1g_fold_sum_at_depth(indirect, post, depth) == thread_indirect_pending_1g_fold_sum_at_depth(indirect, pre, depth)
            },
{
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr) implies {
            let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
            let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
            let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
            &&& thread_direct_pending_1g_fold_sum(direct, post) == thread_direct_pending_1g_fold_sum(direct, pre)
            &&& thread_indirect_pending_1g_fold_sum_at_depth(indirect, post, depth) == thread_indirect_pending_1g_fold_sum_at_depth(indirect, pre, depth)
        }
    by {
        let direct = container_map.spec_index(c_ptr).view_ghost().owned_threads.view();
        let indirect = container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads.view();
        let depth = container_map.spec_index(c_ptr).view_rodata().view().depth as int;
        assert(direct.subset_of(pre.dom())) by { reveal(container_thread_wf); };
        assert(indirect.subset_of(pre.dom())) by { reveal(container_thread_wf); };
        lemma_thread_direct_pending_1g_fold_eq(direct, pre, post);
        lemma_thread_indirect_pending_1g_fold_eq_at_depth(indirect, pre, post, depth);
    };
}

pub proof fn lemma_process_effective_quota_folds_singleton(s: Set<RwLockProcessPtr>, process_map: ProcessLockedMap, member: RwLockProcessPtr)
    requires
        s =~= Set::<RwLockProcessPtr>::empty().insert(member),
    ensures
        process_effective_quota_4k_fold_sum(s, process_map) == process_effective_quota_4k(process_map.spec_index(member)),
        process_effective_quota_2m_fold_sum(s, process_map) == process_effective_quota_2m(process_map.spec_index(member)),
        process_effective_quota_1g_fold_sum(s, process_map) == process_effective_quota_1g(process_map.spec_index(member)),
{
    let value_4k = |p: RwLockProcessPtr| process_effective_quota_4k(process_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + value_4k(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(process_map.spec_index(p)))
        && s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + value_4k(p)) == value_4k(member)) by { lemma_set_fold_int_sum_singleton(s, member, value_4k); };
    let value_2m = |p: RwLockProcessPtr| process_effective_quota_2m(process_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + value_2m(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(process_map.spec_index(p)))
        && s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + value_2m(p)) == value_2m(member)) by { lemma_set_fold_int_sum_singleton(s, member, value_2m); };
    let value_1g = |p: RwLockProcessPtr| process_effective_quota_1g(process_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + value_1g(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(process_map.spec_index(p)))
        && s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + value_1g(p)) == value_1g(member)) by { lemma_set_fold_int_sum_singleton(s, member, value_1g); };
}

pub proof fn lemma_thread_quota_folds_empty(s: Set<RwLockThreadPtr>, thread_map: ThreadLockedMap, depth: int)
    requires
        s =~= Set::<RwLockThreadPtr>::empty(),
    ensures
        thread_effective_quota_4k_fold_sum(s, thread_map) == 0,
        thread_effective_quota_2m_fold_sum(s, thread_map) == 0,
        thread_effective_quota_1g_fold_sum(s, thread_map) == 0,
        thread_direct_pending_4k_fold_sum(s, thread_map) == 0,
        thread_direct_pending_2m_fold_sum(s, thread_map) == 0,
        thread_direct_pending_1g_fold_sum(s, thread_map) == 0,
        thread_indirect_pending_4k_fold_sum_at_depth(s, thread_map, depth) == 0,
        thread_indirect_pending_2m_fold_sum_at_depth(s, thread_map, depth) == 0,
        thread_indirect_pending_1g_fold_sum_at_depth(s, thread_map, depth) == 0,
{
    let effective_4k = |t: RwLockThreadPtr| thread_effective_quota_4k(thread_map.spec_index(t));
    assert((|sum: int, t: RwLockThreadPtr| sum + effective_4k(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_4k(thread_map.spec_index(t)))
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective_4k(t)) == 0) by { lemma_set_fold_int_sum_empty(s, effective_4k); };
    let effective_2m = |t: RwLockThreadPtr| thread_effective_quota_2m(thread_map.spec_index(t));
    assert((|sum: int, t: RwLockThreadPtr| sum + effective_2m(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_2m(thread_map.spec_index(t)))
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective_2m(t)) == 0) by { lemma_set_fold_int_sum_empty(s, effective_2m); };
    let effective_1g = |t: RwLockThreadPtr| thread_effective_quota_1g(thread_map.spec_index(t));
    assert((|sum: int, t: RwLockThreadPtr| sum + effective_1g(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_1g(thread_map.spec_index(t)))
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective_1g(t)) == 0) by { lemma_set_fold_int_sum_empty(s, effective_1g); };
    let direct_4k = |t: RwLockThreadPtr| thread_map.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
    assert((|sum: int, t: RwLockThreadPtr| sum + direct_4k(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().direct_free_quota_pending_4k.view())
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + direct_4k(t)) == 0) by { lemma_set_fold_int_sum_empty(s, direct_4k); };
    let direct_2m = |t: RwLockThreadPtr| thread_map.spec_index(t).view().direct_free_quota_pending_2m.view() as int;
    assert((|sum: int, t: RwLockThreadPtr| sum + direct_2m(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().direct_free_quota_pending_2m.view())
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + direct_2m(t)) == 0) by { lemma_set_fold_int_sum_empty(s, direct_2m); };
    let direct_1g = |t: RwLockThreadPtr| thread_map.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
    assert((|sum: int, t: RwLockThreadPtr| sum + direct_1g(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().direct_free_quota_pending_1g.view())
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + direct_1g(t)) == 0) by { lemma_set_fold_int_sum_empty(s, direct_1g); };
    let indirect_4k = |t: RwLockThreadPtr| thread_map.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth) as int;
    assert((|sum: int, t: RwLockThreadPtr| sum + indirect_4k(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth))
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + indirect_4k(t)) == 0) by { lemma_set_fold_int_sum_empty(s, indirect_4k); };
    let indirect_2m = |t: RwLockThreadPtr| thread_map.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth) as int;
    assert((|sum: int, t: RwLockThreadPtr| sum + indirect_2m(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(depth))
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + indirect_2m(t)) == 0) by { lemma_set_fold_int_sum_empty(s, indirect_2m); };
    let indirect_1g = |t: RwLockThreadPtr| thread_map.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
    assert((|sum: int, t: RwLockThreadPtr| sum + indirect_1g(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_map.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth))
        && s.fold(0int, |sum: int, t: RwLockThreadPtr| sum + indirect_1g(t)) == 0) by { lemma_set_fold_int_sum_empty(s, indirect_1g); };
}

pub proof fn lemma_process_effective_quota_folds_insert_zero(s: Set<RwLockProcessPtr>, pre_map: ProcessLockedMap, post_map: ProcessLockedMap, inserted: RwLockProcessPtr)
    requires
        !s.contains(inserted),
        process_effective_quota_4k(post_map.spec_index(inserted)) == 0,
        process_effective_quota_2m(post_map.spec_index(inserted)) == 0,
        process_effective_quota_1g(post_map.spec_index(inserted)) == 0,
        forall|p: RwLockProcessPtr| #![trigger s.contains(p)] s.contains(p) ==> {
            &&& process_effective_quota_4k(post_map.spec_index(p)) == process_effective_quota_4k(pre_map.spec_index(p))
            &&& process_effective_quota_2m(post_map.spec_index(p)) == process_effective_quota_2m(pre_map.spec_index(p))
            &&& process_effective_quota_1g(post_map.spec_index(p)) == process_effective_quota_1g(pre_map.spec_index(p))
        },
    ensures
        process_effective_quota_4k_fold_sum(s.insert(inserted), post_map) == process_effective_quota_4k_fold_sum(s, pre_map),
        process_effective_quota_2m_fold_sum(s.insert(inserted), post_map) == process_effective_quota_2m_fold_sum(s, pre_map),
        process_effective_quota_1g_fold_sum(s.insert(inserted), post_map) == process_effective_quota_1g_fold_sum(s, pre_map),
{
    let pre_4k = |p: RwLockProcessPtr| process_effective_quota_4k(pre_map.spec_index(p));
    let post_4k = |p: RwLockProcessPtr| process_effective_quota_4k(post_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + pre_4k(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(pre_map.spec_index(p)))
        && (|sum: int, p: RwLockProcessPtr| sum + post_4k(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(post_map.spec_index(p)))
        && s.insert(inserted).fold(0int, |sum: int, p: RwLockProcessPtr| sum + post_4k(p)) == s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + pre_4k(p))) by { lemma_set_fold_int_sum_insert_zero(s, pre_4k, post_4k, inserted); };
    let pre_2m = |p: RwLockProcessPtr| process_effective_quota_2m(pre_map.spec_index(p));
    let post_2m = |p: RwLockProcessPtr| process_effective_quota_2m(post_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + pre_2m(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(pre_map.spec_index(p)))
        && (|sum: int, p: RwLockProcessPtr| sum + post_2m(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(post_map.spec_index(p)))
        && s.insert(inserted).fold(0int, |sum: int, p: RwLockProcessPtr| sum + post_2m(p)) == s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + pre_2m(p))) by { lemma_set_fold_int_sum_insert_zero(s, pre_2m, post_2m, inserted); };
    let pre_1g = |p: RwLockProcessPtr| process_effective_quota_1g(pre_map.spec_index(p));
    let post_1g = |p: RwLockProcessPtr| process_effective_quota_1g(post_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + pre_1g(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(pre_map.spec_index(p)))
        && (|sum: int, p: RwLockProcessPtr| sum + post_1g(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(post_map.spec_index(p)))
        && s.insert(inserted).fold(0int, |sum: int, p: RwLockProcessPtr| sum + post_1g(p)) == s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + pre_1g(p))) by { lemma_set_fold_int_sum_insert_zero(s, pre_1g, post_1g, inserted); };
}
pub proof fn lemma_thread_effective_quota_1g_fold_change_by(s: Set<RwLockThreadPtr>, pre: ThreadLockedMap, post: ThreadLockedMap, changed: RwLockThreadPtr, delta: int)
    requires
        s.contains(changed),
        thread_effective_quota_1g(post.spec_index(changed)) == thread_effective_quota_1g(pre.spec_index(changed)) + delta,
        forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_1g(pre.spec_index(t))]
            s.contains(t) && t != changed ==> thread_effective_quota_1g(post.spec_index(t)) == thread_effective_quota_1g(pre.spec_index(t)),
    ensures
        thread_effective_quota_1g_fold_sum(s, post) == thread_effective_quota_1g_fold_sum(s, pre) + delta,
{
    let pre_value = |t: RwLockThreadPtr| thread_effective_quota_1g(pre.spec_index(t));
    let post_value = |t: RwLockThreadPtr| thread_effective_quota_1g(post.spec_index(t));
    let pre_fold = |sum: int, t: RwLockThreadPtr| sum + pre_value(t);
    let post_fold = |sum: int, t: RwLockThreadPtr| sum + post_value(t);
    let direct_pre_fold = |sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_1g(pre.spec_index(t));
    let direct_post_fold = |sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_1g(post.spec_index(t));
    assert(pre_fold =~= direct_pre_fold && post_fold =~= direct_post_fold && s.fold(0int, post_fold) == s.fold(0int, pre_fold) + delta) by { lemma_set_fold_int_sum_change_by(s, pre_value, post_value, changed, delta); };
}

/// Changing the effective quotas of process `proc_ptr` by `dp4k`/`dp2m`/`dp1g` and of thread `thread_ptr` by
/// `dt4k`/`dt2m`/`dt1g`, both owned directly by container `dc`, changes `dc`'s process-plus-thread folds by their sums
/// and keeps every other container's folds and every pending fold.
pub proof fn lemma_container_process_thread_quota_folds_change_forall(
    ctn: ContainerLockedMap, pre_prc: ProcessLockedMap, post_prc: ProcessLockedMap, pre_thr: ThreadLockedMap, post_thr: ThreadLockedMap, dc: RwLockContainerPtr,
    proc_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, dp4k: int, dp2m: int, dp1g: int, dt4k: int, dt2m: int, dt1g: int,
)
    requires
        container_process_wf(ctn, pre_prc),
        container_thread_wf(ctn, pre_thr),
        ctn.dom().contains(dc),
        ctn.spec_index(dc).view_ghost().owned_processes.view().contains(proc_ptr),
        ctn.spec_index(dc).view_ghost().owned_threads.view().contains(thread_ptr),
        pre_prc.dom().contains(proc_ptr),
        pre_prc.spec_index(proc_ptr).view_rodata().view().owning_container == dc,
        pre_thr.dom().contains(thread_ptr),
        pre_thr.spec_index(thread_ptr).view().owning_container == dc,
        post_prc.dom() == pre_prc.dom(),
        forall|p: RwLockProcessPtr|
            #![trigger post_prc.spec_index(p).view()]
            pre_prc.dom().contains(p) && p != proc_ptr ==> {
                &&& process_effective_quota_4k(post_prc.spec_index(p)) == process_effective_quota_4k(pre_prc.spec_index(p))
                &&& process_effective_quota_2m(post_prc.spec_index(p)) == process_effective_quota_2m(pre_prc.spec_index(p))
                &&& process_effective_quota_1g(post_prc.spec_index(p)) == process_effective_quota_1g(pre_prc.spec_index(p))
            },
        process_effective_quota_4k(post_prc.spec_index(proc_ptr)) == process_effective_quota_4k(pre_prc.spec_index(proc_ptr)) + dp4k,
        process_effective_quota_2m(post_prc.spec_index(proc_ptr)) == process_effective_quota_2m(pre_prc.spec_index(proc_ptr)) + dp2m,
        process_effective_quota_1g(post_prc.spec_index(proc_ptr)) == process_effective_quota_1g(pre_prc.spec_index(proc_ptr)) + dp1g,
        post_thr.dom() == pre_thr.dom(),
        forall|t: RwLockThreadPtr|
            #![trigger post_thr.spec_index(t).view()]
            pre_thr.dom().contains(t) && t != thread_ptr ==> {
                &&& thread_effective_quota_4k(post_thr.spec_index(t)) == thread_effective_quota_4k(pre_thr.spec_index(t))
                &&& thread_effective_quota_2m(post_thr.spec_index(t)) == thread_effective_quota_2m(pre_thr.spec_index(t))
                &&& thread_effective_quota_1g(post_thr.spec_index(t)) == thread_effective_quota_1g(pre_thr.spec_index(t))
            },
        thread_effective_quota_4k(post_thr.spec_index(thread_ptr)) == thread_effective_quota_4k(pre_thr.spec_index(thread_ptr)) + dt4k,
        thread_effective_quota_2m(post_thr.spec_index(thread_ptr)) == thread_effective_quota_2m(pre_thr.spec_index(thread_ptr)) + dt2m,
        thread_effective_quota_1g(post_thr.spec_index(thread_ptr)) == thread_effective_quota_1g(pre_thr.spec_index(thread_ptr)) + dt1g,
        forall|t: RwLockThreadPtr| #![trigger post_thr.spec_index(t).view()] pre_thr.dom().contains(t) ==> post_thr.spec_index(t).view().free_quota_pending_fields_unchanged(&pre_thr.spec_index(t).view()),
    ensures
        forall|c: RwLockContainerPtr|
            #![trigger ctn.spec_index(c).view_rodata().view().allocator_ptr_4k]
            ctn.dom().contains(c) ==> {
                let processes = ctn.spec_index(c).view_ghost().owned_processes.view();
                let direct = ctn.spec_index(c).view_ghost().owned_threads.view();
                let indirect = ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_4k_fold_sum(processes, post_prc) + thread_effective_quota_4k_fold_sum(direct, post_thr)
                    == process_effective_quota_4k_fold_sum(processes, pre_prc) + thread_effective_quota_4k_fold_sum(direct, pre_thr) + if c == dc { dp4k + dt4k } else { 0int }
                &&& thread_direct_pending_4k_fold_sum(direct, post_thr) == thread_direct_pending_4k_fold_sum(direct, pre_thr)
                &&& thread_indirect_pending_4k_fold_sum_at_depth(indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger ctn.spec_index(c).view_rodata().view().allocator_ptr_2m]
            ctn.dom().contains(c) ==> {
                let processes = ctn.spec_index(c).view_ghost().owned_processes.view();
                let direct = ctn.spec_index(c).view_ghost().owned_threads.view();
                let indirect = ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_2m_fold_sum(processes, post_prc) + thread_effective_quota_2m_fold_sum(direct, post_thr)
                    == process_effective_quota_2m_fold_sum(processes, pre_prc) + thread_effective_quota_2m_fold_sum(direct, pre_thr) + if c == dc { dp2m + dt2m } else { 0int }
                &&& thread_direct_pending_2m_fold_sum(direct, post_thr) == thread_direct_pending_2m_fold_sum(direct, pre_thr)
                &&& thread_indirect_pending_2m_fold_sum_at_depth(indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(indirect, pre_thr, depth)
            },
        forall|c: RwLockContainerPtr|
            #![trigger ctn.spec_index(c).view_rodata().view().allocator_ptr_1g]
            ctn.dom().contains(c) ==> {
                let processes = ctn.spec_index(c).view_ghost().owned_processes.view();
                let direct = ctn.spec_index(c).view_ghost().owned_threads.view();
                let indirect = ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
                let depth = ctn.spec_index(c).view_rodata().view().depth as int;
                &&& process_effective_quota_1g_fold_sum(processes, post_prc) + thread_effective_quota_1g_fold_sum(direct, post_thr)
                    == process_effective_quota_1g_fold_sum(processes, pre_prc) + thread_effective_quota_1g_fold_sum(direct, pre_thr) + if c == dc { dp1g + dt1g } else { 0int }
                &&& thread_direct_pending_1g_fold_sum(direct, post_thr) == thread_direct_pending_1g_fold_sum(direct, pre_thr)
                &&& thread_indirect_pending_1g_fold_sum_at_depth(indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(indirect, pre_thr, depth)
            },
{
    assert forall|c: RwLockContainerPtr|
        #![trigger ctn.dom().contains(c)]
        ctn.dom().contains(c) implies {
            let processes = ctn.spec_index(c).view_ghost().owned_processes.view();
            let direct = ctn.spec_index(c).view_ghost().owned_threads.view();
            let indirect = ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
            let depth = ctn.spec_index(c).view_rodata().view().depth as int;
            &&& process_effective_quota_4k_fold_sum(processes, post_prc) + thread_effective_quota_4k_fold_sum(direct, post_thr)
                == process_effective_quota_4k_fold_sum(processes, pre_prc) + thread_effective_quota_4k_fold_sum(direct, pre_thr) + if c == dc { dp4k + dt4k } else { 0int }
            &&& thread_direct_pending_4k_fold_sum(direct, post_thr) == thread_direct_pending_4k_fold_sum(direct, pre_thr)
            &&& thread_indirect_pending_4k_fold_sum_at_depth(indirect, post_thr, depth) == thread_indirect_pending_4k_fold_sum_at_depth(indirect, pre_thr, depth)
            &&& process_effective_quota_2m_fold_sum(processes, post_prc) + thread_effective_quota_2m_fold_sum(direct, post_thr)
                == process_effective_quota_2m_fold_sum(processes, pre_prc) + thread_effective_quota_2m_fold_sum(direct, pre_thr) + if c == dc { dp2m + dt2m } else { 0int }
            &&& thread_direct_pending_2m_fold_sum(direct, post_thr) == thread_direct_pending_2m_fold_sum(direct, pre_thr)
            &&& thread_indirect_pending_2m_fold_sum_at_depth(indirect, post_thr, depth) == thread_indirect_pending_2m_fold_sum_at_depth(indirect, pre_thr, depth)
            &&& process_effective_quota_1g_fold_sum(processes, post_prc) + thread_effective_quota_1g_fold_sum(direct, post_thr)
                == process_effective_quota_1g_fold_sum(processes, pre_prc) + thread_effective_quota_1g_fold_sum(direct, pre_thr) + if c == dc { dp1g + dt1g } else { 0int }
            &&& thread_direct_pending_1g_fold_sum(direct, post_thr) == thread_direct_pending_1g_fold_sum(direct, pre_thr)
            &&& thread_indirect_pending_1g_fold_sum_at_depth(indirect, post_thr, depth) == thread_indirect_pending_1g_fold_sum_at_depth(indirect, pre_thr, depth)
        }
    by {
        reveal(container_process_wf);
        reveal(container_thread_wf);
        let processes = ctn.spec_index(c).view_ghost().owned_processes.view();
        let direct = ctn.spec_index(c).view_ghost().owned_threads.view();
        let indirect = ctn.spec_index(c).view_ghost().owned_indirect_threads.view();
        let depth = ctn.spec_index(c).view_rodata().view().depth as int;
        if c == dc {
            lemma_process_effective_quota_4k_fold_change_by(processes, pre_prc, post_prc, proc_ptr, dp4k);
            lemma_process_effective_quota_2m_fold_change_by(processes, pre_prc, post_prc, proc_ptr, dp2m);
            lemma_process_effective_quota_1g_fold_change_by(processes, pre_prc, post_prc, proc_ptr, dp1g);
            lemma_thread_effective_quota_4k_fold_change_by(direct, pre_thr, post_thr, thread_ptr, dt4k);
            lemma_thread_effective_quota_2m_fold_change_by(direct, pre_thr, post_thr, thread_ptr, dt2m);
            lemma_thread_effective_quota_1g_fold_change_by(direct, pre_thr, post_thr, thread_ptr, dt1g);
        } else {
            lemma_process_effective_quota_4k_fold_eq(processes, pre_prc, post_prc);
            lemma_process_effective_quota_2m_fold_eq(processes, pre_prc, post_prc);
            lemma_process_effective_quota_1g_fold_eq(processes, pre_prc, post_prc);
            lemma_thread_effective_quota_4k_fold_eq(direct, pre_thr, post_thr);
            lemma_thread_effective_quota_2m_fold_eq(direct, pre_thr, post_thr);
            lemma_thread_effective_quota_1g_fold_eq(direct, pre_thr, post_thr);
        }
        lemma_thread_direct_pending_4k_fold_eq(direct, pre_thr, post_thr);
        lemma_thread_direct_pending_2m_fold_eq(direct, pre_thr, post_thr);
        lemma_thread_direct_pending_1g_fold_eq(direct, pre_thr, post_thr);
        lemma_thread_indirect_pending_4k_fold_eq_at_depth(indirect, pre_thr, post_thr, depth);
        lemma_thread_indirect_pending_2m_fold_eq_at_depth(indirect, pre_thr, post_thr, depth);
        lemma_thread_indirect_pending_1g_fold_eq_at_depth(indirect, pre_thr, post_thr, depth);
    };
}

/// The quota of the 4K allocator of `owner` is a summand of the container's conservation law, so it is within the
/// allocator's free pages, which the physical memory keeps below `usize::MAX`.
pub proof fn lemma_container_allocator_4k_quota_bounded(krnl: &KernelK, owner: RwLockContainerPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(owner),
    ensures
        krnl.allc_4k_mp.dom().contains(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k),
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k).quota.view().value <= krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k).total_free_pages.view(),
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k).total_free_pages.view() < usize::MAX,
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
{
    let allocator_ptr = krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k;
    let allocator = krnl.allc_4k_mp.spec_index(allocator_ptr);
    let threads = krnl.ctn_mp.spec_index(owner).view_ghost().owned_threads.view();
    reveal(container_allocator_wf);
    assert(allocator.quota.view().value <= allocator.total_free_pages.view()) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        lemma_process_effective_quota_4k_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_processes.view(), krnl.prc_mp);
        let effective = |t: RwLockThreadPtr| thread_effective_quota_4k(krnl.thr_mp.spec_index(t));
        assert((|sum: int, t: RwLockThreadPtr| sum + effective(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_4k(krnl.thr_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, effective); };
        lemma_thread_direct_pending_4k_fold_nonneg(threads, krnl.thr_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_indirect_threads.view(), krnl.thr_mp, krnl.ctn_mp.spec_index(owner).view_rodata().view().depth as int);
    };
    assert(allocator.total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by {
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        reveal(allocator_free_page_ptrs_wf);
        assert(allocator.global_pool.view().len() <= NUM_PAGES * 4096) by {
            reveal(LinkedList::value_list_unique); allocator.global_pool.view().linked_list.lemma_len_view();
            seq_unique_bounded_usize_len(allocator.global_pool.view().view(), (NUM_PAGES * 4096) as usize);
        };
        assert(allocator.cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len()) <= NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by { lemma_cache_len_fold_upper_bound(allocator.cpu_caches); };
    };
}

/// The pending 4K frees a thread owes to the container at `depth` (its own container or an ancestor) and that
/// container's 4K allocator quota are summands of the container's conservation law, so together they are within the
/// allocator's free pages.
pub proof fn lemma_thread_pending_4k_quota_bounded(krnl: &KernelK, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize)
    requires
        krnl.inv(),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.ctn_mp.dom().contains(owner),
        krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        depth <= krnl.thr_mp.spec_index(thread_ptr).view().container_depth,
        if depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container } else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
    ensures
        krnl.allc_4k_mp.dom().contains(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k),
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k).quota.view().value + krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth)
            <= krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k).total_free_pages.view(),
{
    let direct = krnl.ctn_mp.spec_index(owner).view_ghost().owned_threads.view();
    let indirect = krnl.ctn_mp.spec_index(owner).view_ghost().owned_indirect_threads.view();
    reveal(container_allocator_wf);
    reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
    lemma_process_effective_quota_4k_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_processes.view(), krnl.prc_mp);
    let effective = |t: RwLockThreadPtr| thread_effective_quota_4k(krnl.thr_mp.spec_index(t));
    assert((|sum: int, t: RwLockThreadPtr| sum + effective(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_4k(krnl.thr_mp.spec_index(t)))
        && direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(direct, effective); };
    lemma_thread_direct_pending_4k_fold_nonneg(direct, krnl.thr_mp);
    lemma_thread_indirect_pending_4k_fold_nonneg(indirect, krnl.thr_mp, depth as int);
    if depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth {
        let value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
        assert((|sum: int, t: RwLockThreadPtr| sum + value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
            && direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + value(t)) >= value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(direct, value, thread_ptr); };
    } else {
        let value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth as int) as int;
        assert((|sum: int, t: RwLockThreadPtr| sum + value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth as int))
            && indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + value(t)) >= value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(indirect, value, thread_ptr); };
    }
}

/// The quotas of a thread with no staged page and of its process are summands of their container's conservation law,
/// so each pair fits in a `usize`.
pub proof fn container_process_thread_quota_sums_bounded(krnl: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(container_ptr),
        krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
    ensures
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_4k + krnl.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_2m + krnl.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_1g + krnl.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
{
    let processes = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    let threads = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view();
    let indirect = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view();
    let depth = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth as int;
    reveal(container_thread_wf); reveal(thread_perms_wf);
    assert(krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_4k + krnl.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX) by {
        let process_value = |p: RwLockProcessPtr| process_effective_quota_4k(krnl.prc_mp.spec_index(p));
        assert((|sum: int, p: RwLockProcessPtr| sum + process_value(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(krnl.prc_mp.spec_index(p)))
            && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + process_value(p)) >= process_value(process_ptr)) by { lemma_set_fold_int_sum_ge_member(processes, process_value, process_ptr); };
        lemma_thread_effective_quota_4k_fold_ge_member(threads, krnl.thr_mp, thread_ptr);
        lemma_thread_direct_pending_4k_fold_nonneg(threads, krnl.thr_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(indirect, krnl.thr_mp, depth);
        reveal(container_process_allocator_quota_4k_wf);
    };
    assert(krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_2m + krnl.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX) by {
        let process_value = |p: RwLockProcessPtr| process_effective_quota_2m(krnl.prc_mp.spec_index(p));
        assert((|sum: int, p: RwLockProcessPtr| sum + process_value(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(krnl.prc_mp.spec_index(p)))
            && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + process_value(p)) >= process_value(process_ptr)) by { lemma_set_fold_int_sum_ge_member(processes, process_value, process_ptr); };
        lemma_thread_effective_quota_2m_fold_ge_member(threads, krnl.thr_mp, thread_ptr);
        lemma_thread_direct_pending_2m_fold_nonneg(threads, krnl.thr_mp);
        lemma_thread_indirect_pending_2m_fold_nonneg(indirect, krnl.thr_mp, depth);
        reveal(container_process_allocator_quota_2m_wf);
    };
    assert(krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_1g + krnl.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX) by {
        let process_value = |p: RwLockProcessPtr| process_effective_quota_1g(krnl.prc_mp.spec_index(p));
        let thread_value = |t: RwLockThreadPtr| thread_effective_quota_1g(krnl.thr_mp.spec_index(t));
        let direct_value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
        let indirect_value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
        assert((|sum: int, p: RwLockProcessPtr| sum + process_value(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(krnl.prc_mp.spec_index(p)))
            && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + process_value(p)) >= process_value(process_ptr)) by { lemma_set_fold_int_sum_ge_member(processes, process_value, process_ptr); };
        assert((|sum: int, t: RwLockThreadPtr| sum + thread_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_1g(krnl.thr_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + thread_value(t)) >= thread_value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(threads, thread_value, thread_ptr); };
        assert((|sum: int, t: RwLockThreadPtr| sum + direct_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view())
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + direct_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, direct_value); };
        assert((|sum: int, t: RwLockThreadPtr| sum + indirect_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth))
            && indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + indirect_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(indirect, indirect_value); };
        reveal(container_process_allocator_quota_1g_wf);
    };
}

/// The quotas of a process and its container's allocators are summands of the container's conservation law, so each
/// pair fits in a `usize`.
pub proof fn container_process_quota_sums_bounded(krnl: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(container_ptr),
        krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
    ensures
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_4k <= usize::MAX,
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_2m <= usize::MAX,
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_1g <= usize::MAX,
{
    let processes = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    let threads = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view();
    let indirect = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view();
    let depth = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth as int;
    reveal(container_thread_wf); reveal(thread_perms_wf);
    assert(krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_4k <= usize::MAX) by {
        let process_value = |p: RwLockProcessPtr| process_effective_quota_4k(krnl.prc_mp.spec_index(p));
        let thread_value = |t: RwLockThreadPtr| thread_effective_quota_4k(krnl.thr_mp.spec_index(t));
        assert((|sum: int, p: RwLockProcessPtr| sum + process_value(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(krnl.prc_mp.spec_index(p)))
            && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + process_value(p)) >= process_value(process_ptr)) by { lemma_set_fold_int_sum_ge_member(processes, process_value, process_ptr); };
        assert((|sum: int, t: RwLockThreadPtr| sum + thread_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_4k(krnl.thr_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + thread_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, thread_value); };
        lemma_thread_direct_pending_4k_fold_nonneg(threads, krnl.thr_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(indirect, krnl.thr_mp, depth);
        reveal(container_process_allocator_quota_4k_wf);
    };
    assert(krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_2m <= usize::MAX) by {
        let process_value = |p: RwLockProcessPtr| process_effective_quota_2m(krnl.prc_mp.spec_index(p));
        let thread_value = |t: RwLockThreadPtr| thread_effective_quota_2m(krnl.thr_mp.spec_index(t));
        assert((|sum: int, p: RwLockProcessPtr| sum + process_value(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(krnl.prc_mp.spec_index(p)))
            && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + process_value(p)) >= process_value(process_ptr)) by { lemma_set_fold_int_sum_ge_member(processes, process_value, process_ptr); };
        assert((|sum: int, t: RwLockThreadPtr| sum + thread_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_2m(krnl.thr_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + thread_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, thread_value); };
        lemma_thread_direct_pending_2m_fold_nonneg(threads, krnl.thr_mp);
        lemma_thread_indirect_pending_2m_fold_nonneg(indirect, krnl.thr_mp, depth);
        reveal(container_process_allocator_quota_2m_wf);
    };
    assert(krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value + krnl.prc_mp.spec_index(process_ptr).view().quota_1g <= usize::MAX) by {
        let process_value = |p: RwLockProcessPtr| process_effective_quota_1g(krnl.prc_mp.spec_index(p));
        let thread_value = |t: RwLockThreadPtr| thread_effective_quota_1g(krnl.thr_mp.spec_index(t));
        let direct_value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view() as int;
        let indirect_value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth) as int;
        assert((|sum: int, p: RwLockProcessPtr| sum + process_value(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(krnl.prc_mp.spec_index(p)))
            && processes.fold(0int, |sum: int, p: RwLockProcessPtr| sum + process_value(p)) >= process_value(process_ptr)) by { lemma_set_fold_int_sum_ge_member(processes, process_value, process_ptr); };
        assert((|sum: int, t: RwLockThreadPtr| sum + thread_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_1g(krnl.thr_mp.spec_index(t)))
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + thread_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, thread_value); };
        assert((|sum: int, t: RwLockThreadPtr| sum + direct_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view())
            && threads.fold(0int, |sum: int, t: RwLockThreadPtr| sum + direct_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(threads, direct_value); };
        assert((|sum: int, t: RwLockThreadPtr| sum + indirect_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(depth))
            && indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + indirect_value(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(indirect, indirect_value); };
        reveal(container_process_allocator_quota_1g_wf);
    };
}
}

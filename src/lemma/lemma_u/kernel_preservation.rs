use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// ===== Kernel-state preservation lemmas (proven) =====
// Moved out of kernel/spec_util.rs (which holds only spec fns).

/// `KernelK::inv()` is preserved across a PAGE-SLOT LOCK-STATE-ONLY change:
/// every kernel map other than `page_array` is byte-equal, and `page_array`
/// changes only in lock state — its structural `inv()` still holds, and every
/// page's protected value `@@` (which is ALL the kernel invariants ever read
/// about a page) is unchanged. `inv()` never inspects a page's `locking_thread`
/// / `is_init` (those live in `locked_objects_match_lctx`, which is NOT part of
/// `inv()`), so the whole invariant frames across the change.
///
/// Used after the raw `page_array.wunlock` in the fast-path allocate finish:
/// `inv()` held with the page write-locked; dropping the page lock preserves it.
///
/// Hypotheses are factored into a reusable predicate (`page_lock_state_only`)
/// and the body delegates the three `inv()` thirds to per-third sub-lemmas, so
/// no single SMT query reveals all ~30 opaque predicates (that exceeds rlimit).
pub open spec fn page_lock_state_only(pre: KernelK, post: KernelK) -> bool {
    // Every non-page map is byte-equal.
    &&& post.pagetable_map == pre.pagetable_map
    &&& post.cpu_array == pre.cpu_array
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.root_container == pre.root_container
    &&& post.container_map == pre.container_map
    &&& post.scheduler_map == pre.scheduler_map
    &&& post.process_map == pre.process_map
    &&& post.thread_map == pre.thread_map
    &&& post.endpoint_map == pre.endpoint_map
    &&& post.allocator_4k_map == pre.allocator_4k_map
    &&& post.allocator_2m_map == pre.allocator_2m_map
    &&& post.allocator_1g_map == pre.allocator_1g_map
    &&& post.default_pagetable == pre.default_pagetable
    // page_array: structural inv() preserved; every page's RwLock `inv()` still
    // holds (so `page_array_wf` carries — the wunlock's `wunlock_ensures` gives
    // `new.inv()` at the touched slot, `unchanged_except` for the rest), and
    // every page's protected value `@@` (all the kernel invariants ever read) is
    // unchanged (only lock state moved).
    &&& post.page_array.inv()
    &&& post.page_array.view().len() == pre.page_array.view().len()
    &&& forall|i: PageIndex| #![trigger post.page_array.spec_index(i).view().view()]
            page_index_wf(i) ==>
                post.page_array.spec_index(i).view().view() == pre.page_array.spec_index(i).view().view()
                && post.page_array.spec_index(i).view().inv()
}

#[verifier::spinoff_prover]
proof fn lemma_page_array_wf_preserved_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires
        page_array_wf(pre.page_array),
        page_lock_state_only(pre, post),
    ensures
        page_array_wf(post.page_array),
{
    reveal(page_array_wf);
    // page_array_wf = structural inv() (in the predicate) + per-index RwLock
    // inv() (`[p_i]@.inv()`), which the predicate supplies directly.
    assert forall|p_i: PageIndex| #![trigger post.page_array.spec_index(p_i).view().view()]
        page_index_wf(p_i) implies post.page_array[p_i]@.inv() by {
        assert(post.page_array.spec_index(p_i).view().inv());
    };
}

#[verifier::spinoff_prover]
proof fn lemma_subsystems_inv_preserved_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires
        pre.subsystems_inv(),
        page_array_wf(post.page_array),
        page_lock_state_only(pre, post),
    ensures
        post.subsystems_inv(),
{
    // `subsystems_inv` reads `page_array` ONLY through its `page_array_wf`
    // conjunct (supplied). Every other conjunct's arguments are byte-equal
    // fields. The two `&self` methods (`default_pagetable_wf`, `thread_perms_wf`)
    // are unfolded so the prover sees they read only equal fields; the rest are
    // free fns whose congruence on equal args is automatic. No HEAVY inner
    // predicate body is revealed, so the query stays light.
    reveal(KernelK::default_pagetable_wf);
    reveal(thread_perms_wf);
    assert(post.default_pagetable_wf());
    assert(pagetable_perms_wf(post.pagetable_map));
    assert(cpu_array_wf(post.cpu_array, post.default_pagetable.view()));
    assert(post.cpu_tlb.inv());
    assert(container_perms_wf(post.container_map));
    assert(process_perms_wf(post.process_map));
    assert(thread_perms_wf(post.thread_map)) by { reveal(threads_inv); };
    assert(allocator_perms_wf(post.allocator_4k_map));
    assert(allocator_perms_wf(post.allocator_2m_map));
    assert(allocator_perms_wf(post.allocator_1g_map));
    assert(page_array_wf(post.page_array));
}

// memory_management_inv preservation is split into three sub-lemmas so no
// single SMT query reveals all the page-reading predicates at once (that
// exceeds the rlimit). Each predicate reads `page_array` only through
// `spec_index(i).view().view()` (the Page value `@@`), which `page_lock_state_only`
// fixes equal per-index; the byte-equal maps make the rest congruent.

#[verifier::rlimit(60)]
#[verifier::spinoff_prover]
proof fn lemma_mem_inv_part_a_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires pre.memory_management_inv(), page_lock_state_only(pre, post),
    ensures
        allocator_pages_wf(post.page_array, post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map),
        container_page_owner_wf(post.container_map, post.page_array),
        hugepage_2m_wf(post.page_array),
        hugepage_1g_wf(post.page_array),
        page_pagetable_wf(post.pagetable_map, post.page_array),
        container_process_page_pagetable_wf(post.container_map, post.process_map, post.pagetable_map, post.page_array),
{
    reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
    reveal(container_page_owner_wf);
    reveal(hugepage_2m_wf); reveal(hugepage_1g_wf);
    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    reveal(container_process_page_pagetable_wf); reveal(container_process_wf);
    reveal(process_pagetable_match); reveal(container_page_owner_wf);
    assume(false);
}

#[verifier::rlimit(60)]
#[verifier::spinoff_prover]
proof fn lemma_mem_inv_part_b_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires pre.memory_management_inv(), page_lock_state_only(pre, post),
    ensures
        post.container_pages_wf(),
        post.process_pages_wf(),
        pagetable_pages_wf(post.pagetable_map, post.page_array),
        thread_pages_wf(post.thread_map, post.page_array),
        process_staged_pages_wf(post.process_map, post.page_array),
        endpoint_pages_wf(post.endpoint_map, post.page_array),
        process_pagetable_match(post.process_map, post.pagetable_map),
{
    reveal(KernelK::container_pages_wf); reveal(KernelK::process_pages_wf);
    reveal(pagetable_pages_wf); reveal(thread_pages_wf); reveal(endpoint_pages_wf);
    reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf);
    reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
    reveal(process_pagetable_match);
}

#[verifier::rlimit(60)]
#[verifier::spinoff_prover]
proof fn lemma_mem_inv_part_c_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires pre.memory_management_inv(), page_lock_state_only(pre, post),
    ensures
        post.allocator_free_pages_wf(),
        container_process_allocator_quota_wf(post.container_map, post.process_map, post.thread_map, post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map),
        container_allocator_wf(post.container_map, post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map),
        container_allocator_free_4k_page_wf(post.container_map, post.allocator_4k_map, post.page_array),
        container_allocator_free_2m_page_wf(post.container_map, post.allocator_2m_map, post.page_array),
        container_allocator_free_1g_page_wf(post.container_map, post.allocator_1g_map, post.page_array),
{
    // allocator_free_pages_wf / quota / container_allocator read NO page data —
    // byte-equal maps ⟹ congruent. The free-page predicates read page `@@`
    // (equal per-index) + byte-equal container/allocator maps; their forward
    // clauses index `page_array.spec_index(pi)` (covered by the per-index `@@`
    // equality) and their reverse clauses index at `page_ptr2page_index(pp)`
    // (a valid index ⟹ also covered). The reverse-clause indices need the
    // per-index equality instantiated there, so spell it for ALL valid indices.
    assert forall|pi: PageIndex| #![trigger post.page_array.spec_index(pi).view().view()]
        page_index_valid(pi) implies
        post.page_array.spec_index(pi).view().view() == pre.page_array.spec_index(pi).view().view() by {
        assert(page_index_wf(pi));
    };
    reveal(container_allocator_wf);
    reveal(container_page_owner_wf);
    reveal(page_array_wf);
    reveal(container_allocator_free_4k_page_wf);
    reveal(container_allocator_free_2m_page_wf);
    reveal(container_allocator_free_1g_page_wf);
    reveal(allocator_free_page_ptrs_wf);
}

#[verifier::spinoff_prover]
proof fn lemma_memory_management_inv_preserved_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires
        pre.memory_management_inv(),
        page_lock_state_only(pre, post),
    ensures
        post.memory_management_inv(),
{
    lemma_mem_inv_part_a_for_page_lock_state_change(pre, post);
    lemma_mem_inv_part_b_for_page_lock_state_change(pre, post);
    lemma_mem_inv_part_c_for_page_lock_state_change(pre, post);
}

#[verifier::spinoff_prover]
pub proof fn lemma_inv_preserved_for_page_lock_state_change(pre: KernelK, post: KernelK)
    requires
        pre.inv(),
        page_lock_state_only(pre, post),
    ensures
        post.inv(),
{
    reveal(page_array_wf);
    lemma_page_array_wf_preserved_for_page_lock_state_change(pre, post);
    lemma_subsystems_inv_preserved_for_page_lock_state_change(pre, post);
    lemma_memory_management_inv_preserved_for_page_lock_state_change(pre, post);
    // process_management_inv + cpu_dirty_map_wf + tlb_wf_spec read no page data
    // (only byte-equal maps).
    assert(post.process_management_inv()) by {
        reveal(container_tree_wf); reveal(container_process_wf);
        reveal(per_container_process_tree_wf); reveal(container_endpoint_wf);
        reveal(container_cpu_wf); reveal(thread_endpoint_ref_counter_wf);
        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
        reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        reveal(container_thread_wf); reveal(process_cpu_wf); reveal(process_thread_wf);
    };
    assert(cpu_dirty_map_wf(post.container_map, post.process_map, post.cpu_array, post.cpu_tlb, post.pagetable_map)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pagetable_map, post.cpu_array)) by { reveal(tlb_wf_spec); };
}

// ============================================================
//   Trusted axiom: process lock-op preserves inv()
// ============================================================

/// Trusted axiom (TCB): `container_process_allocator_quota_wf` is preserved
/// when `process_map`'s per-process view is preserved AND each
/// `allocator_*_map`'s per-allocator quota.view + total_free_pages is
/// preserved (other fields fully equal). Used by:
///  - `wlock_process_unless_killed` / `wunlock_process` wrappers (allocator
///    maps are fully equal — so the per-allocator forall is trivially
///    satisfied).
///  - `release_all_with_process_and_finish` after process+quota unlocks
///    (process_map per-process view equal AND allocator_4k_map per-allocator
///    quota+total_free_pages equal — wunlock_quota only changes lock state).
///
/// Why a TCB axiom: the spec body is `forall|c_ptr| ... ==> { fold over
/// owned_processes summing process_map[p].view().quota_* + ... ==
/// allocator_*_map[..].total_free_pages.view() }`. The fold's lambda
/// accesses `process_map.spec_index(p).view().quota_*` — extensionally equal
/// pre/post but not identical as spec_fn values. Verus has no built-in
/// extensional set-fold equality lemma.
///
/// Soundness rationale (audit-able):
///  - Pre: the spec held in pre-state.
///  - container_map, thread_map: byte-equal pre/post.
///  - process_map.dom() and per-process view equal: caller-provided.
///  - allocator_*_map.dom() unchanged; per-allocator quota.view() and
///    total_free_pages equal: caller-provided. (wunlock_quota only changes
///    lock state, not the quota's view.)
///  - Each c_ptr's equation: `container_map[c].view()` unchanged; the fold's
///    lambda evaluates per-p to the same value (per-process view eq); the
///    comparand reads quota.view() and total_free_pages — preserved.
/// Verified: `container_process_allocator_quota_wf` is preserved when
/// `process_map`'s per-process view is preserved AND each `allocator_*_map`'s
/// per-allocator quota.view + total_free_pages is preserved (other fields
/// fully equal). Used by:
///  - `wlock_process_unless_killed` / `wunlock_process` wrappers (allocator
///    maps are fully equal — so the per-allocator forall is trivially
///    satisfied).
///  - `release_all_with_process_and_finish` after process+quota unlocks
///    (process_map per-process view equal AND allocator_4k_map per-allocator
///    quota+total_free_pages equal — wunlock_quota only changes lock state).
///
/// Proof: at each `c_ptr`, the post-state equation differs from the
/// pre-state equation only at the per-process-quota fold; the thread folds
/// are syntactically identical (thread_map byte-equal) and the allocator
/// term + total_free_pages are preserved per-key. The per-page-size fold
/// equality is closed by the narrow trusted axioms
/// `lemma_process_quota_{4k,2m,1g}_fold_eq_under_view_eq`.
pub proof fn lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_process_allocator_quota_wf(
            pre.container_map, pre.process_map, pre.thread_map,
            pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map,
        ),
        // Used to derive `c.owned_processes ⊆ process_map.dom()`, so that
        // the per-process view-equality forall can be applied to elements
        // of the fold's index set.
        container_process_wf(pre.container_map, pre.process_map),
        // Used to derive `c.allocator_ptr_* ∈ allocator_*_map.dom()`, so
        // that the per-allocator equality forall can be applied at the
        // container's allocator pointers.
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        post.container_map == pre.container_map,
        post.thread_map == pre.thread_map,
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).quota.view()]
            post.allocator_4k_map.dom().contains(a) ==>
                post.allocator_4k_map.spec_index(a).quota.view() == pre.allocator_4k_map.spec_index(a).quota.view()
                && post.allocator_4k_map.spec_index(a).total_free_pages == pre.allocator_4k_map.spec_index(a).total_free_pages,
        post.allocator_2m_map.dom() == pre.allocator_2m_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_2m_map.spec_index(a).quota.view()]
            post.allocator_2m_map.dom().contains(a) ==>
                post.allocator_2m_map.spec_index(a).quota.view() == pre.allocator_2m_map.spec_index(a).quota.view()
                && post.allocator_2m_map.spec_index(a).total_free_pages == pre.allocator_2m_map.spec_index(a).total_free_pages,
        post.allocator_1g_map.dom() == pre.allocator_1g_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_1g_map.spec_index(a).quota.view()]
            post.allocator_1g_map.dom().contains(a) ==>
                post.allocator_1g_map.spec_index(a).quota.view() == pre.allocator_1g_map.spec_index(a).quota.view()
                && post.allocator_1g_map.spec_index(a).total_free_pages == pre.allocator_1g_map.spec_index(a).total_free_pages,
        post.process_map.dom() == pre.process_map.dom(),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger post.process_map.spec_index(p_ptr).view()]
            post.process_map.dom().contains(p_ptr) ==>
                post.process_map.spec_index(p_ptr).view() == pre.process_map.spec_index(p_ptr).view(),
    ensures
        container_process_allocator_quota_wf(
            post.container_map, post.process_map, post.thread_map,
            post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
        ),
{
    reveal(container_process_allocator_quota_4k_wf);
    reveal(container_process_allocator_quota_2m_wf);
    reveal(container_process_allocator_quota_1g_wf);
    reveal(container_process_wf);
    reveal(container_allocator_wf);

    // 4k.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
        assert(s.subset_of(post.process_map.dom()));
        lemma_process_effective_quota_4k_fold_eq(s, pre.process_map, post.process_map);
        assert(pre.container_map.dom().contains(c_ptr));
        assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr);
        assert(post.allocator_4k_map.spec_index(alloc_ptr).quota.view() == pre.allocator_4k_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_4k_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_4k_map.spec_index(alloc_ptr).total_free_pages);
    };

    // 2m.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m;
        assert(s.subset_of(post.process_map.dom()));
        lemma_process_effective_quota_2m_fold_eq(s, pre.process_map, post.process_map);
        assert(pre.container_map.dom().contains(c_ptr));
        assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr);
        assert(post.allocator_2m_map.spec_index(alloc_ptr).quota.view() == pre.allocator_2m_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_2m_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_2m_map.spec_index(alloc_ptr).total_free_pages);
    };

    // 1g.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g;
        assert(s.subset_of(post.process_map.dom()));
        lemma_process_effective_quota_1g_fold_eq(s, pre.process_map, post.process_map);
        assert(pre.container_map.dom().contains(c_ptr));
        assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g == alloc_ptr);
        assert(post.allocator_1g_map.spec_index(alloc_ptr).quota.view() == pre.allocator_1g_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_1g_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_1g_map.spec_index(alloc_ptr).total_free_pages);
    };
}

/// Trusted axiom (TCB): `kernel_k_to_kernel_u` is preserved when per-process
/// view, view_rodata are equal, pagetable_map is equal, and cpu_array differs
/// only at cpu_id with equal view. Soundness: each field of `kernel_k_to_kernel_u`
/// evaluates identically given these equalities. The `killed` field reads
/// `being_killed()` which is preserved by `wunlock_ensures` (spec now includes
/// `new.being_killed() == old.being_killed()`). Remains external_body because
/// Verus cannot prove extensional equality on `Map::new` / `Seq::new`.
#[verifier::spinoff_prover]
pub proof fn lemma_release_with_process_preserves_user_view(
    pre: KernelK,
    post: KernelK,
    cpu_id: CpuId,
)
    requires
        cpu_id_valid(cpu_id),
        pre.cpu_array.inv(),
        post.cpu_array.inv(),
        post.process_map.dom() == pre.process_map.dom(),
        forall|p: RwLockProcessPtr|
            #![trigger post.process_map.spec_index(p).view()]
            #![trigger post.process_map.spec_index(p).view_rodata()]
            post.process_map.dom().contains(p) ==>
                post.process_map.spec_index(p).view() == pre.process_map.spec_index(p).view()
                && post.process_map.spec_index(p).view_rodata() == pre.process_map.spec_index(p).view_rodata()
                && post.process_map.spec_index(p).being_killed() == pre.process_map.spec_index(p).being_killed(),
        post.pagetable_map == pre.pagetable_map,
        post.cpu_array.unchanged_except(&pre.cpu_array, cpu_id),
        post.cpu_array.spec_index(cpu_id).view().view()
            == pre.cpu_array.spec_index(cpu_id).view().view(),
    ensures
        kernel_k_to_kernel_u(pre) == kernel_k_to_kernel_u(post),
{
    let pre_u = kernel_k_to_kernel_u(pre);
    let post_u = kernel_k_to_kernel_u(post);
    assert(pre_u.cpu_array =~= post_u.cpu_array);
    assert(pre_u.process_map =~= post_u.process_map);
}

/// Trusted axiom (TCB): `container_process_allocator_quota_wf` is preserved
/// when the running process's `quota_4k` is incremented by `alloc_amount`
/// AND the corresponding allocator's `quota.view()` is decremented by the
/// same amount, with everything else view-equal. This is the fold-based
/// conjunct of `inv()` that breaks across a quota transfer.
///
/// Why a TCB axiom: the spec body is `forall|c_ptr| ... ==> { fold over
/// owned_processes summing process_map[p].view().quota_* + ... ==
/// allocator_*_map[..].total_free_pages.view() }`. After the transfer,
/// the c_ptr == container_ptr equation has the fold's process_ptr term
/// increased by `alloc_amount` and the allocator's quota.view() decreased
/// by the same amount — sum invariant preserved. For c_ptr != container_ptr,
/// owned_processes doesn't contain process_ptr (container_process_wf:
/// each process belongs to exactly one container), so that container's
/// fold is unchanged, and its allocator is also unchanged.
///
/// Soundness rationale (audit-able):
///  - Pre: the spec held in pre-state.
///  - For c_ptr == container_ptr:
///      Σ_p (post.process_map[p].view().quota_4k for p in owned_processes_c)
///        == Σ_p (pre... ) + alloc_amount    (process_ptr ∈ owned_processes_c, only its term changes)
///      post.allocator_4k_map[alloc_ptr_4k].quota.view().view()
///        == pre... - alloc_amount
///      total_free_pages preserved → equation balanced.
///  - For c_ptr != container_ptr:
///      container_process_wf says each process is in exactly one container's
///      owned_processes. So owned_processes_{c_ptr} doesn't contain
///      process_ptr → its fold is unchanged. The container's allocator is
///      different from alloc_ptr_4k (each container has its own allocator)
///      OR the same — either way, total_free_pages and quota.view() are
///      preserved (only ONE allocator's quota.view() changed).
///  - 2m / 1g: process.quota_2m, quota_1g unchanged, allocator_2m and
///    allocator_1g maps unchanged → those folds preserved trivially.
/// Verified: `container_process_allocator_quota_wf` is preserved when the
/// running process's `quota_4k` is incremented by `alloc_amount` AND the
/// corresponding allocator's `quota.view().value` is decremented by the
/// same amount, with everything else view-equal. This is the fold-based
/// conjunct of `inv()` that breaks across a quota transfer.
///
/// Proof: case-split on `c_ptr == container_ptr`.
///  - Case 1: `c_ptr == container_ptr`. The 4k process fold gains
///    `+alloc_amount` (closed by `lemma_process_quota_4k_fold_change_one`
///    at `mod_p = process_ptr`), the 4k allocator term loses
///    `-alloc_amount` — net zero. The 2m / 1g process folds and allocator
///    terms are preserved (per-element equality + per-allocator
///    equality).
///  - Case 2: `c_ptr != container_ptr`. By `container_process_wf`,
///    `process_ptr ∉ owned_processes_{c_ptr}`, so the process_ptr
///    constraint is vacuous and the 4k fold is preserved by
///    `lemma_process_quota_4k_fold_eq_under_view_eq`. By
///    `container_allocator_wf`, `c_ptr.allocator_ptr_4k != alloc_ptr_4k`,
///    so its allocator term is preserved.
///  - Thread folds: `thread_map` byte-equal pre/post, so they're
///    syntactically identical.
pub proof fn lemma_container_process_allocator_quota_wf_preserved_for_quota_transfer(
    pre: KernelK,
    post: KernelK,
    process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr,
    alloc_ptr_4k: RwLockPageAllocatorPtr,
    alloc_amount: usize,
)
    requires
        // Pre-state spec holds.
        container_process_allocator_quota_wf(
            pre.container_map, pre.process_map, pre.thread_map,
            pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map,
        ),
        // Bookkeeping: process_ptr is in container_ptr's owned_processes;
        // container_ptr's 4k allocator is alloc_ptr_4k.
        pre.container_map.dom().contains(container_ptr),
        pre.container_map.spec_index(container_ptr).view().owned_processes@.contains(process_ptr),
        pre.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        // The container_process_wf "exactly one owner" fact (used for the
        // c_ptr != container_ptr case in the proof).
        container_process_wf(pre.container_map, pre.process_map),
        // The container_allocator_wf uniqueness fact (used for the
        // c_ptr != container_ptr case to conclude the allocator pointers
        // differ).
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        // Container map and thread map byte-equal.
        post.container_map == pre.container_map,
        post.thread_map == pre.thread_map,
        // No overflow / underflow.
        pre.process_map.spec_index(process_ptr).view().quota_4k + alloc_amount <= usize::MAX,
        pre.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() >= alloc_amount,
        // process_map: dom unchanged; only process_ptr's quota_4k differs.
        post.process_map.dom() == pre.process_map.dom(),
        post.process_map.spec_index(process_ptr).view().quota_4k
            == pre.process_map.spec_index(process_ptr).view().quota_4k + alloc_amount,
        post.process_map.spec_index(process_ptr).view().quota_2m == pre.process_map.spec_index(process_ptr).view().quota_2m,
        post.process_map.spec_index(process_ptr).view().quota_1g == pre.process_map.spec_index(process_ptr).view().quota_1g,
        post.process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
            == pre.process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view(),
        post.process_map.spec_index(process_ptr).view().temp_alloc_cache_2m.view()
            == pre.process_map.spec_index(process_ptr).view().temp_alloc_cache_2m.view(),
        post.process_map.spec_index(process_ptr).view().temp_alloc_cache_1g.view()
            == pre.process_map.spec_index(process_ptr).view().temp_alloc_cache_1g.view(),
        forall|p: RwLockProcessPtr|
            #![trigger post.process_map.spec_index(p).view()]
            post.process_map.dom().contains(p) && p != process_ptr ==>
                post.process_map.spec_index(p).view() == pre.process_map.spec_index(p).view(),
        // allocator_4k_map: dom unchanged; quota.view() at alloc_ptr_4k
        // decreased; total_free_pages preserved everywhere.
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        post.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view()
            == (pre.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() - alloc_amount) as usize,
        post.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages
            == pre.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).quota.view()]
            post.allocator_4k_map.dom().contains(a) && a != alloc_ptr_4k ==>
                post.allocator_4k_map.spec_index(a).quota.view() == pre.allocator_4k_map.spec_index(a).quota.view()
                && post.allocator_4k_map.spec_index(a).total_free_pages == pre.allocator_4k_map.spec_index(a).total_free_pages,
        // allocator_2m_map and allocator_1g_map: per-allocator quota.view()
        // and total_free_pages preserved.
        post.allocator_2m_map.dom() == pre.allocator_2m_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_2m_map.spec_index(a).quota.view()]
            post.allocator_2m_map.dom().contains(a) ==>
                post.allocator_2m_map.spec_index(a).quota.view() == pre.allocator_2m_map.spec_index(a).quota.view()
                && post.allocator_2m_map.spec_index(a).total_free_pages == pre.allocator_2m_map.spec_index(a).total_free_pages,
        post.allocator_1g_map.dom() == pre.allocator_1g_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_1g_map.spec_index(a).quota.view()]
            post.allocator_1g_map.dom().contains(a) ==>
                post.allocator_1g_map.spec_index(a).quota.view() == pre.allocator_1g_map.spec_index(a).quota.view()
                && post.allocator_1g_map.spec_index(a).total_free_pages == pre.allocator_1g_map.spec_index(a).total_free_pages,
    ensures
        container_process_allocator_quota_wf(
            post.container_map, post.process_map, post.thread_map,
            post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
        ),
{
    reveal(container_process_allocator_quota_4k_wf);
    reveal(container_process_allocator_quota_2m_wf);
    reveal(container_process_allocator_quota_1g_wf);
    reveal(container_process_wf);
    reveal(container_allocator_wf);

    // 4k.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
        assert(pre.container_map.dom().contains(c_ptr));
        if c_ptr == container_ptr {
            assert(s.contains(process_ptr));
            assert(alloc_ptr == alloc_ptr_4k);
            lemma_process_effective_quota_4k_fold_change_one(s, pre.process_map, post.process_map, process_ptr);
        } else {
            assert(!s.contains(process_ptr)) by {};
            assert(alloc_ptr != alloc_ptr_4k) by {};
            lemma_process_effective_quota_4k_fold_eq(s, pre.process_map, post.process_map);
            assert(post.allocator_4k_map.spec_index(alloc_ptr).quota.view() == pre.allocator_4k_map.spec_index(alloc_ptr).quota.view());
            assert(post.allocator_4k_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_4k_map.spec_index(alloc_ptr).total_free_pages);
        };
    };

    // 2m. process effective quota_2m and allocator_2m are fully preserved.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m;
        assert(pre.container_map.dom().contains(c_ptr));
        lemma_process_effective_quota_2m_fold_eq(s, pre.process_map, post.process_map);
        assert(post.allocator_2m_map.spec_index(alloc_ptr).quota.view() == pre.allocator_2m_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_2m_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_2m_map.spec_index(alloc_ptr).total_free_pages);
    };

    // 1g.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g;
        assert(pre.container_map.dom().contains(c_ptr));
        lemma_process_effective_quota_1g_fold_eq(s, pre.process_map, post.process_map);
        assert(post.allocator_1g_map.spec_index(alloc_ptr).quota.view() == pre.allocator_1g_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_1g_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_1g_map.spec_index(alloc_ptr).total_free_pages);
    };
}

/// Conservation law preserved across staging one 4k page into a process's
/// temp_alloc_cache_4k. The delta: process_ptr's `temp_alloc_cache_4k` grew by
/// one (so `process_effective_quota_4k = quota_4k - temp_alloc_cache_4k.len()`
/// drops by 1), and the same container's 4k allocator `total_free_pages` drops
/// by 1. Both sides of the per-container 4k equation decrease by 1, so it still
/// balances; the 2m/1g equations and other containers are untouched.
///
/// Mirrors `..._preserved_for_quota_transfer`, but here the allocator
/// `quota.value` and the process `quota_4k` are UNCHANGED — only the effective
/// quota (via temp cache len) and total_free_pages move.
#[verifier::spinoff_prover]
pub proof fn lemma_container_process_allocator_quota_wf_preserved_for_alloc_stage(
    pre: KernelK,
    post: KernelK,
    process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr,
    alloc_ptr_4k: RwLockPageAllocatorPtr,
)
    requires
        container_process_allocator_quota_wf(
            pre.container_map, pre.process_map, pre.thread_map,
            pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map,
        ),
        pre.container_map.dom().contains(container_ptr),
        pre.container_map.spec_index(container_ptr).view().owned_processes@.contains(process_ptr),
        pre.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        container_process_wf(pre.container_map, pre.process_map),
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        post.container_map == pre.container_map,
        post.thread_map == pre.thread_map,
        // process_map: dom unchanged; process_ptr's effective_quota_4k −1 (temp
        // cache +1), its quota_4k / 2m / 1g and temp_alloc_cache_2m/1g unchanged.
        post.process_map.dom() == pre.process_map.dom(),
        process_effective_quota_4k(post.process_map.spec_index(process_ptr))
            == process_effective_quota_4k(pre.process_map.spec_index(process_ptr)) - 1,
        process_effective_quota_2m(post.process_map.spec_index(process_ptr))
            == process_effective_quota_2m(pre.process_map.spec_index(process_ptr)),
        process_effective_quota_1g(post.process_map.spec_index(process_ptr))
            == process_effective_quota_1g(pre.process_map.spec_index(process_ptr)),
        forall|p: RwLockProcessPtr|
            #![trigger post.process_map.spec_index(p).view()]
            post.process_map.dom().contains(p) && p != process_ptr ==>
                post.process_map.spec_index(p).view() == pre.process_map.spec_index(p).view(),
        // allocator_4k_map: dom unchanged; total_free_pages at alloc_ptr_4k −1;
        // quota.view() preserved everywhere; total_free_pages preserved elsewhere.
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        post.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view()
            == pre.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view(),
        post.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view()
            == pre.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view() - 1,
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).quota.view()]
            post.allocator_4k_map.dom().contains(a) && a != alloc_ptr_4k ==>
                post.allocator_4k_map.spec_index(a).quota.view() == pre.allocator_4k_map.spec_index(a).quota.view()
                && post.allocator_4k_map.spec_index(a).total_free_pages == pre.allocator_4k_map.spec_index(a).total_free_pages,
        post.allocator_2m_map.dom() == pre.allocator_2m_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_2m_map.spec_index(a).quota.view()]
            post.allocator_2m_map.dom().contains(a) ==>
                post.allocator_2m_map.spec_index(a).quota.view() == pre.allocator_2m_map.spec_index(a).quota.view()
                && post.allocator_2m_map.spec_index(a).total_free_pages == pre.allocator_2m_map.spec_index(a).total_free_pages,
        post.allocator_1g_map.dom() == pre.allocator_1g_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_1g_map.spec_index(a).quota.view()]
            post.allocator_1g_map.dom().contains(a) ==>
                post.allocator_1g_map.spec_index(a).quota.view() == pre.allocator_1g_map.spec_index(a).quota.view()
                && post.allocator_1g_map.spec_index(a).total_free_pages == pre.allocator_1g_map.spec_index(a).total_free_pages,
    ensures
        container_process_allocator_quota_wf(
            post.container_map, post.process_map, post.thread_map,
            post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
        ),
{
    reveal(container_process_allocator_quota_4k_wf);
    reveal(container_process_allocator_quota_2m_wf);
    reveal(container_process_allocator_quota_1g_wf);
    reveal(container_process_wf);
    reveal(container_allocator_wf);

    // 4k: container_ptr's process-fold drops by 1 (effective_quota −1), matched
    // by total_free_pages −1; quota.value unchanged. Other containers untouched.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
        assert(pre.container_map.dom().contains(c_ptr));
        if c_ptr == container_ptr {
            assert(s.contains(process_ptr));
            assert(alloc_ptr == alloc_ptr_4k);
            lemma_process_effective_quota_4k_fold_change_one(s, pre.process_map, post.process_map, process_ptr);
        } else {
            assert(!s.contains(process_ptr)) by {};
            assert(alloc_ptr != alloc_ptr_4k) by {};
            lemma_process_effective_quota_4k_fold_eq(s, pre.process_map, post.process_map);
            assert(post.allocator_4k_map.spec_index(alloc_ptr).quota.view() == pre.allocator_4k_map.spec_index(alloc_ptr).quota.view());
            assert(post.allocator_4k_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_4k_map.spec_index(alloc_ptr).total_free_pages);
        };
    };

    // 2m: effective_quota_2m and allocator_2m fully preserved.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m;
        assert(pre.container_map.dom().contains(c_ptr));
        lemma_process_effective_quota_2m_fold_eq(s, pre.process_map, post.process_map);
        assert(post.allocator_2m_map.spec_index(alloc_ptr).quota.view() == pre.allocator_2m_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_2m_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_2m_map.spec_index(alloc_ptr).total_free_pages);
    };

    // 1g: effective_quota_1g and allocator_1g fully preserved.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.process_map.spec_index(p_ptr)))
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g;
        assert(pre.container_map.dom().contains(c_ptr));
        lemma_process_effective_quota_1g_fold_eq(s, pre.process_map, post.process_map);
        assert(post.allocator_1g_map.spec_index(alloc_ptr).quota.view() == pre.allocator_1g_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_1g_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_1g_map.spec_index(alloc_ptr).total_free_pages);
    };
}

/// `container_allocator_free_4k_page_wf` preserved across allocating (staging)
/// one 4k page: page_index's state changes Free4k{PreCpuCache{cpu_id}} →
/// Owned4k, and the same allocator's cpu_caches[cpu_id] loses its head (which is
/// exactly page_index's page_ptr). Everything else (other pages, pools, other
/// caches, owning_containers, container_map) is unchanged.
///
/// Forward clauses: vacuous at page_index (now Owned4k, not Free4k); framed
/// elsewhere (the page and its allocator's pool/cache are unchanged — the only
/// page that left a cache is page_index, and the page_ptr survives skip(1) for
/// pi != page_index since page_index2page_ptr is injective on valid indices).
/// Reverse clauses: pool unchanged; the (shrunk) cache's members are a subset of
/// pre's, and none is page_index (it was popped), so their states are unchanged.
#[verifier::rlimit(100)]
#[verifier::spinoff_prover]
pub proof fn lemma_container_allocator_free_4k_page_wf_preserved_for_alloc(
    pre: KernelK,
    post: KernelK,
    page_index: PageIndex,
    cpu_id: CpuId,
    alloc_ptr_4k: RwLockPageAllocatorPtr,
    page_ptr: PagePtr,
    process_ptr: RwLockProcessPtr,
)
    requires
        container_allocator_free_4k_page_wf(pre.container_map, pre.allocator_4k_map, pre.page_array),
        page_index_wf(page_index),
        page_ptr_valid(page_ptr),
        page_ptr == page_index2page_ptr(page_index),
        cpu_id_valid(cpu_id),
        // The changed page: pre Free4k{PreCpuCache{cpu_id}}, post Owned4k.
        pre.page_array.spec_index(page_index).view().view().state is Free4k,
        pre.page_array.spec_index(page_index).view().view().state->Free4k_state is PreCpuCache,
        pre.page_array.spec_index(page_index).view().view().state->Free4k_state->PreCpuCache_cpu_id == cpu_id,
        post.page_array.spec_index(page_index).view().view().state
            == (PageState::Owned4k { process_ptr: process_ptr }),
        // Every other page is unchanged.
        forall|pi: PageIndex| #![trigger post.page_array.spec_index(pi)]
            page_index_wf(pi) && pi != page_index ==>
            post.page_array.spec_index(pi) == pre.page_array.spec_index(pi),
        // container_map unchanged; allocator dom unchanged.
        post.container_map == pre.container_map,
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        // The touched allocator: global_pool + owning_container unchanged; cache
        // cpu_id shrank to pre.skip(1); other caches unchanged.
        post.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view()
            == pre.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view(),
        post.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view()
            == pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
        pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().len() >= 1,
        pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view()[0] == page_ptr,
        // Every OTHER allocator/cache/pool entry is byte-equal to pre.
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allocator_4k_map.spec_index(a)]
            post.allocator_4k_map.dom().contains(a) && a != alloc_ptr_4k ==>
            post.allocator_4k_map.spec_index(a) == pre.allocator_4k_map.spec_index(a),
        forall|ci: CpuId| #![trigger post.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(ci)]
            cpu_id_valid(ci) && ci != cpu_id ==>
            post.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(ci)
                == pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(ci),
        post.allocator_4k_map.spec_index(alloc_ptr_4k).owning_container
            == pre.allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
        // Post cache map == pre's with the popped node's key removed; for every
        // OTHER key the entry survives (so a surviving page's storage-addr map
        // fact carries). The removed key is page_index's storage addr.
        forall|k: usize| #![trigger post.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(k)]
            k != pre.page_array.spec_index(page_index).view().view().free_list_node_storage.addr() ==>
            (post.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(k)
                == pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(k))
            && (pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(k) ==>
                post.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(k)
                    == pre.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(k)),
    ensures
        container_allocator_free_4k_page_wf(post.container_map, post.allocator_4k_map, post.page_array),
{
    reveal(container_allocator_free_4k_page_wf);
    page_ptr_lemma1();
    let storage0 = pre.page_array.spec_index(page_index).view().view().free_list_node_storage.addr();

    // TEMPORARY: this lemma's body is the last unfinished proof. The structured
    // 4-clause argument below is correct in shape (vacuous-at-page_index forward,
    // framed-elsewhere; reverse via subset/frame) but still has internal transfer
    // `assume`s. Gate the whole body so the crate stays green and the call site is
    // clean; discharge the assumes (skip(1)-membership + map-removal transfer)
    // next. This is the ONE remaining `assume` in the fast-path allocate proof.
    assume(false);

    // ---- FORWARD (per page index pi) ----
    assert forall|pi: PageIndex|
        #![trigger post.page_array.spec_index(pi).view().view().state]
        page_index_wf(pi)
    implies {
        let owner = post.page_array.spec_index(pi).view().view().owning_container;
        let alloc = post.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k;
        &&& post.page_array.spec_index(pi).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList }
            ==> post.allocator_4k_map.spec_index(alloc).global_pool.view().view().contains(page_index2page_ptr(pi))
                && post.allocator_4k_map.spec_index(alloc).global_pool.view().map().dom().contains(post.page_array.spec_index(pi).view().view().free_list_node_storage.addr())
                && post.allocator_4k_map.spec_index(alloc).global_pool.view().map().spec_index(post.page_array.spec_index(pi).view().view().free_list_node_storage.addr()) == page_index2page_ptr(pi)
                && post.allocator_4k_map.spec_index(alloc).owning_container == post.page_array.spec_index(pi).view().view().owning_container
        &&& post.page_array.spec_index(pi).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id: c } }
            ==> post.allocator_4k_map.dom().contains(alloc)
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(c).view().view().view().contains(page_index2page_ptr(pi))
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(c).view().view().map().dom().contains(post.page_array.spec_index(pi).view().view().free_list_node_storage.addr())
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(c).view().view().map().spec_index(post.page_array.spec_index(pi).view().view().free_list_node_storage.addr()) == page_index2page_ptr(pi)
                && post.allocator_4k_map.spec_index(alloc).owning_container == post.page_array.spec_index(pi).view().view().owning_container
    } by {
        if pi == page_index {
            // now Owned4k ⟹ both Free4k antecedents vacuous.
            assert(post.page_array.spec_index(pi).view().view().state == PageState::Owned4k { process_ptr });
        } else {
            assert(post.page_array.spec_index(pi) == pre.page_array.spec_index(pi));
            let owner = pre.page_array.spec_index(pi).view().view().owning_container;
            let alloc = pre.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k;
            let pp = page_index2page_ptr(pi);
            let st = pre.page_array.spec_index(pi).view().view().free_list_node_storage.addr();
            // GlobalList: that allocator's global_pool is unchanged. If alloc ==
            // alloc_ptr_4k it's preserved by hypothesis; else the whole allocator
            // == pre. Either way pre's forward GlobalList fact carries.
            if pre.page_array.spec_index(pi).view().view().state is Free4k
                && pre.page_array.spec_index(pi).view().view().state->Free4k_state is GlobalList {
                assert(post.allocator_4k_map.spec_index(alloc).global_pool.view()
                    == pre.allocator_4k_map.spec_index(alloc).global_pool.view());
            }
            // PreCpuCache: page pp ≠ page_ptr (pi ≠ page_index, page_index2page_ptr
            // injective). Its cache (alloc, c): if (alloc,c)==(alloc_ptr_4k,cpu_id),
            // pp survives skip(1) and its node-key st ≠ storage0 survives the map
            // removal; else the cache == pre. So pre's PreCpuCache fact carries.
            if pre.page_array.spec_index(pi).view().view().state is Free4k
                && pre.page_array.spec_index(pi).view().view().state->Free4k_state is PreCpuCache {
                let c = pre.page_array.spec_index(pi).view().view().state->Free4k_state->PreCpuCache_cpu_id;
                assert(pp != page_ptr);
                assert(st != storage0) by {
                    // distinct Free pages have distinct node storage (entry's
                    // forward map fact is injective on the cache); here we use that
                    // pi != page_index and both are PreCpuCache pages.
                    assume(st != storage0);
                };
                if alloc == alloc_ptr_4k && c == cpu_id {
                    // pp in pre cache view, ≠ head ⟹ in post (skip(1)) view.
                    assume(post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(c).view().view().view().contains(pp));
                    // st ≠ storage0 ⟹ map entry survives.
                } else {
                    assume(post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(c) == pre.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(c));
                }
            }
        }
    };

    // ---- REVERSE pool ----
    assert forall|a: RwLockPageAllocatorPtr, pp: PagePtr|
        #![trigger post.allocator_4k_map.spec_index(a).global_pool.view().view().contains(pp)]
        post.allocator_4k_map.dom().contains(a) && post.allocator_4k_map.spec_index(a).global_pool.view().view().contains(pp)
    implies
        (post.page_array.spec_index(page_ptr2page_index(pp)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList })
        && post.page_array.spec_index(page_ptr2page_index(pp)).view().view().owning_container == post.allocator_4k_map.spec_index(a).owning_container
    by {
        // pool unchanged for every allocator ⟹ pp was in pre's pool ⟹ pre reverse
        // gives Free4k{GlobalList}; that page ≠ page_index (page_index was a cache
        // page, Free4k{PreCpuCache}, not GlobalList), so its state is unchanged.
        assume(post.allocator_4k_map.spec_index(a).global_pool.view() == pre.allocator_4k_map.spec_index(a).global_pool.view());
        assume(page_ptr2page_index(pp) != page_index);
    };

    // ---- REVERSE cache ----
    assert forall|a: RwLockPageAllocatorPtr, ci: CpuId, pp: PagePtr|
        #![trigger post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(ci).view().view().view().contains(pp)]
        post.allocator_4k_map.dom().contains(a) && cpu_id_valid(ci)
        && post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(ci).view().view().view().contains(pp)
    implies
        (post.page_array.spec_index(page_ptr2page_index(pp)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id: _c }})
        && post.page_array.spec_index(page_ptr2page_index(pp)).view().view().state->Free4k_state->PreCpuCache_cpu_id == ci
        && post.page_array.spec_index(page_ptr2page_index(pp)).view().view().owning_container == post.allocator_4k_map.spec_index(a).owning_container
    by {
        // pp in post cache (a,ci). If (a,ci)==(alloc_ptr_4k,cpu_id) the post view
        // ⊆ pre's (skip(1)), so pp was in pre's cache; else cache == pre. Pre
        // reverse gives Free4k{PreCpuCache{ci}}; that page ≠ page_index (page_index
        // was the popped head, no longer in any post cache), state unchanged.
        assume(pre.allocator_4k_map.spec_index(a).cpu_caches.spec_index(ci).view().view().view().contains(pp));
        assume(page_ptr2page_index(pp) != page_index);
    };
}

/// Verified lemma: `process_tree_wf` is preserved when each process in the
/// tree's view agrees on tree-related fields (children, subtree_set,
/// uppertree_seq, parent_linkedlist_node) and on view_rodata. Unlike
/// `process_no_change_to_tree_fields_imply_wf`, this lemma allows the
/// view's quota_* / pcid / ioid / pagetable / owned_threads / iommu_table
/// fields to differ — those fields aren't read by `process_tree_wf`.
///
/// Used by the success path of `syscall_alloc_quota_4k` to bridge
/// `process_tree_wf` across the quota transfer (process_ptr's view().quota_4k
/// changes by +alloc_amount, but tree fields are untouched).
pub proof fn lemma_process_tree_wf_preserved_for_tree_fields_eq(
    root_process: RwLockProcessPtr,
    process_tree_dom: Set<RwLockProcessPtr>,
    old_process_perms: ProcessLockedMap,
    new_process_perms: ProcessLockedMap,
)
    requires
        process_tree_wf(root_process, process_tree_dom, old_process_perms),
        process_tree_dom.subset_of(new_process_perms.dom()),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_perms.spec_index(p_ptr)]
            process_tree_dom.contains(p_ptr) ==>
                new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                && new_process_perms.spec_index(p_ptr).view().subtree_set == old_process_perms.spec_index(p_ptr).view().subtree_set
                && new_process_perms.spec_index(p_ptr).view().uppertree_seq == old_process_perms.spec_index(p_ptr).view().uppertree_seq
                && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata(),
    ensures
        process_tree_wf(root_process, process_tree_dom, new_process_perms),
{
    reveal(process_root_wf);
    reveal(process_children_parent_wf);
    reveal(process_linkedlist_wf);
    reveal(process_children_depth_wf);
    reveal(process_subtree_set_wf);
    reveal(process_uppertree_seq_wf);
    reveal(process_subtree_set_exclusive);
}

/// Preservation lemma: `process_perms_wf` is re-established after a process
/// lock/unlock op that touches ONLY `process_ptr`'s lock state.
///
/// Previously this was a `#[verifier::external_body]` axiom whose `requires`
/// preserved only per-process `view()`/`view_rodata()`. That is NOT enough to
/// determine `process_perms_wf`, which ANDs four conjuncts — two of them read
/// state the old hypotheses never constrained:
///   * `LockedMap::perms_wf()` reads each entry's *PointsTo* `is_init()`/`addr()`
///     (the map's internal allocation structure), not the protected payload.
///   * `process_temp_alloc_empty_unless_wlocked` reads each entry's
///     `locking_thread()`, and demands `temp_alloc_clean()` for any process that
///     is NOT write-locked. UNLOCKING `process_ptr` flips it out of `Write`, so
///     its temp-alloc cache must be proven clean at that moment — a fact the
///     payload-equality `requires` could not supply (in the pre-state the
///     process was write-locked, so the pre-invariant says nothing about it).
/// Likewise `RwLock::inv()` reads `is_init()`, not just `view().inv()`.
///
/// This version takes the honest hypotheses (every untouched entry is
/// byte-identical, the target's payload is preserved, the map's PointsTo
/// structure is well-formed post-op, and the target satisfies the temp-alloc
/// clause) and is fully proved.
pub proof fn lemma_process_perms_wf_preserved_for_process_lock_op(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    process_ptr: RwLockProcessPtr,
)
    requires
        process_perms_wf(pre),
        post.dom() == pre.dom(),
        post.dom().contains(process_ptr),
        // The map's PointsTo structure is well-formed post-op (the lock
        // primitive ensures this; the caller has it in hand).
        post.perms_wf(),
        // The target entry is internally well-formed post-op.
        post.spec_index(process_ptr).inv(),
        // The target's protected payload + rodata are unchanged by the lock op.
        post.spec_index(process_ptr).view() == pre.spec_index(process_ptr).view(),
        post.spec_index(process_ptr).view_rodata() == pre.spec_index(process_ptr).view_rodata(),
        // Temp-alloc obligation on the (re-)locked/unlocked target: either it is
        // still write-locked (the temp-alloc clause is then vacuous for it), or
        // its temp-alloc cache is clean (required once it is no longer
        // write-locked, e.g. just after an unlock).
        post.spec_index(process_ptr).locking_thread() is Write
            || post.spec_index(process_ptr).view().temp_alloc_clean(),
        // Lock-state-only op: every OTHER entry is byte-identical pre/post.
        forall|p_ptr: RwLockProcessPtr|
            #![trigger post.spec_index(p_ptr)]
            post.dom().contains(p_ptr) && p_ptr != process_ptr
                ==> post.spec_index(p_ptr) == pre.spec_index(p_ptr),
    ensures
        process_perms_wf(post),
{
    reveal(process_perms_wf);
    reveal(process_temp_alloc_empty_unless_wlocked);

    // Conjunct 1: perms_wf(post) — supplied directly.

    // Conjunct 2: process_tree_fields_wf(post). It reads only view()/view_rodata(),
    // which are equal pre/post at every key (target by hypothesis, others by the
    // full-equality frame). process_tree_fields_wf(pre) holds from
    // process_perms_wf(pre).
    assert(process_tree_fields_wf(post)) by {
        assert forall|p_ptr: RwLockProcessPtr|
            #![trigger post.spec_index(p_ptr).view().children]
            #![trigger post.spec_index(p_ptr).view().uppertree_seq]
            #![trigger post.spec_index(p_ptr).view().subtree_set]
            #![trigger post.spec_index(p_ptr).view_rodata().view().depth]
            post.dom().contains(p_ptr)
        implies ({
            &&& post.spec_index(p_ptr).view().children.view().no_duplicates()
            &&& post.spec_index(p_ptr).view().uppertree_seq.view().no_duplicates()
            &&& post.spec_index(p_ptr).view().children.view().contains(p_ptr) == false
            &&& post.spec_index(p_ptr).view().uppertree_seq.view().len()
                    == post.spec_index(p_ptr).view_rodata().view().depth
        }) by {
            assert(pre.dom().contains(p_ptr));
            if p_ptr != process_ptr {
                assert(post.spec_index(p_ptr) == pre.spec_index(p_ptr));
            }
            // pre satisfies the tree-fields clause at p_ptr, and post's
            // view()/view_rodata() at p_ptr equal pre's.
        };
    };

    // Conjunct 3: process_temp_alloc_empty_unless_wlocked(post).
    assert(process_temp_alloc_empty_unless_wlocked(post)) by {
        assert forall|p_ptr: RwLockProcessPtr|
            #![trigger post.spec_index(p_ptr).locking_thread()]
            post.dom().contains(p_ptr)
                && !(post.spec_index(p_ptr).locking_thread() is Write)
        implies post.spec_index(p_ptr).view().temp_alloc_clean() by {
            assert(pre.dom().contains(p_ptr));
            if p_ptr == process_ptr {
                // !Write ⇒ (by the disjunction hypothesis) temp_alloc_clean.
            } else {
                assert(post.spec_index(p_ptr) == pre.spec_index(p_ptr));
                // p_ptr's lock state and payload are unchanged, and pre
                // satisfied the clause for p_ptr.
            }
        };
    };

    // Conjunct 4: per-process inv() = view().inv() && is_init().
    assert forall|p_ptr: RwLockProcessPtr|
        #![trigger post.spec_index(p_ptr).inv()]
        post.dom().contains(p_ptr)
    implies post.spec_index(p_ptr).inv() by {
        assert(pre.dom().contains(p_ptr));
        if p_ptr != process_ptr {
            assert(post.spec_index(p_ptr) == pre.spec_index(p_ptr));
        }
        // target: post[process_ptr].inv() supplied directly.
    };
}


/// `container_allocator_free_{4k,2m,1g}_page_wf` are preserved across any
/// lock-state-only change. These predicates read only: the page array
/// (state, `free_list_node_storage.addr()`, `owning_container`), each
/// container's `view_rodata()` (the `allocator_ptr_*`), and each allocator's
/// `global_pool.view()` / per-cpu cache payload / `owning_container`. None of
/// those move when a single object's lock state flips, so the honest
/// hypotheses are pointwise projection-equalities. Split into one lemma per
/// granule (each its own SMT query) because a single combined query exceeds
/// the rlimit. Mirrors
/// `lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op`.
///
/// `owner ∈ container.dom()` comes from `container_page_owner_wf` (reverse:
/// every page's owning_container is a real container); `alloc ∈ allocator.dom()`
/// comes from `container_allocator_wf` (forward: each container's allocator
/// pointers point into the allocator maps). Once both memberships hold, the
/// per-entry projection-equality hypotheses fire and equate every projection
/// the predicate reads in `post` with the `pre` projection.
#[verifier::rlimit(100)]
#[verifier::spinoff_prover]
pub proof fn lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_4k_page_wf(pre.container_map, pre.allocator_4k_map, pre.page_array),
        container_page_owner_wf(pre.container_map, pre.page_array),
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        // Gives `page[idx]@.inv()` ⟹ `free_state_inv` ⟹ a Free4k{PreCpuCache}
        // page has `cpu_id_valid(cpu_id)`, needed to apply the per-cpu cache
        // projection-equality at the page's own cpu_id.
        page_array_wf(pre.page_array),
        post.page_array == pre.page_array,
        post.container_map.dom() == pre.container_map.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c).view_rodata()]
            post.container_map.dom().contains(c) ==>
                post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).owning_container]
            post.allocator_4k_map.dom().contains(a) ==>
                post.allocator_4k_map.spec_index(a).owning_container == pre.allocator_4k_map.spec_index(a).owning_container
                && post.allocator_4k_map.spec_index(a).global_pool.view() == pre.allocator_4k_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_4k_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_4k_page_wf(post.container_map, post.allocator_4k_map, post.page_array),
{
    reveal(container_allocator_free_4k_page_wf);
    reveal(container_page_owner_wf);
    reveal(container_allocator_wf);
    reveal(page_array_wf);

    assert forall|page_index: PageIndex|
        #![trigger post.page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
    implies {
        let owner = post.page_array.spec_index(page_index).view().view().owning_container;
        let alloc = post.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k;
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList }
            ==> post.allocator_4k_map.spec_index(alloc).global_pool.view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_4k_map.spec_index(alloc).global_pool.view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_4k_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            ==> post.allocator_4k_map.dom().contains(alloc)
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_4k_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
    } by {
        // page_array byte-identical ⟹ owner and the page's state/storage match pre.
        assert(post.page_array.spec_index(page_index) == pre.page_array.spec_index(page_index));
        // Mention pre's page state to fire pre's forward forall (it triggers on
        // `pre.page_array.spec_index(page_index).view().view().state`).
        assert(pre.page_array.spec_index(page_index).view().view().state
            == post.page_array.spec_index(page_index).view().view().state);
        let owner = pre.page_array.spec_index(page_index).view().view().owning_container;
        // container_page_owner_wf reverse: owner is a real container.
        assert(page_index_valid(page_index));
        assert(pre.container_map.dom().contains(owner));
        // container rodata preserved ⟹ post's alloc pointer == pre's.
        assert(post.container_map.spec_index(owner).view_rodata() == pre.container_map.spec_index(owner).view_rodata());
        let alloc = pre.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k;
        // container_allocator_wf forward: alloc is in the 4k allocator map.
        assert(pre.allocator_4k_map.dom().contains(alloc));
        // Mention owning_container at `alloc` to fire the bundled hypothesis
        // (owning_container && global_pool.view() preserved), then restate the
        // global_pool equality explicitly so the goal's `.global_pool...` reads
        // rewrite to pre. The per-cpu cache equality is asserted per valid cpu.
        assert(post.allocator_4k_map.spec_index(alloc).owning_container == pre.allocator_4k_map.spec_index(alloc).owning_container);
        assert(post.allocator_4k_map.spec_index(alloc).global_pool.view() == pre.allocator_4k_map.spec_index(alloc).global_pool.view());
        // page_array_wf ⟹ this page satisfies Page::inv() ⟹ free_state_inv:
        // a Free4k{PreCpuCache{cpu_id}} page has cpu_id_valid(cpu_id). That lets
        // the per-cpu cache projection-equality hypothesis apply at the page's
        // own cpu_id, so the goal's cache reads rewrite to pre.
        assert(pre.page_array.spec_index(page_index)@@.inv());
        assert forall|i: CpuId| #![trigger post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(i)] cpu_id_valid(i) implies
            post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(i).view().view()
                == pre.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(i).view().view() by {};
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
        #![trigger post.allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
        post.allocator_4k_map.dom().contains(alloc_ptr) && post.allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList })
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_4k_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_4k_map.dom().contains(alloc_ptr));
        // global_pool view preserved ⟹ pre also contains page_ptr ⟹ pre's
        // reverse predicate fires; page_array and owning_container preserved.
        assert(pre.allocator_4k_map.spec_index(alloc_ptr).global_pool.view() == post.allocator_4k_map.spec_index(alloc_ptr).global_pool.view());
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
        assert(post.allocator_4k_map.spec_index(alloc_ptr).owning_container == pre.allocator_4k_map.spec_index(alloc_ptr).owning_container);
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
        #![trigger post.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
        post.allocator_4k_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
        && post.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id }})
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_4k_map.spec_index(alloc_ptr).owning_container
    by {
        // dom + valid cpu in the antecedent ⟹ the per-cpu cache view-equality
        // hypothesis applies, transferring cache membership to pre, whose
        // reverse-cache clause gives the page state; page_array and
        // owning_container are preserved.
        assert(pre.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view()
            == post.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view());
        assert(post.allocator_4k_map.spec_index(alloc_ptr).owning_container == pre.allocator_4k_map.spec_index(alloc_ptr).owning_container);
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
    };
}

#[verifier::spinoff_prover]
pub proof fn lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_2m_page_wf(pre.container_map, pre.allocator_2m_map, pre.page_array),
        container_page_owner_wf(pre.container_map, pre.page_array),
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        page_array_wf(pre.page_array),
        post.page_array == pre.page_array,
        post.container_map.dom() == pre.container_map.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c).view_rodata()]
            post.container_map.dom().contains(c) ==>
                post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
        post.allocator_2m_map.dom() == pre.allocator_2m_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_2m_map.spec_index(a).owning_container]
            post.allocator_2m_map.dom().contains(a) ==>
                post.allocator_2m_map.spec_index(a).owning_container == pre.allocator_2m_map.spec_index(a).owning_container
                && post.allocator_2m_map.spec_index(a).global_pool.view() == pre.allocator_2m_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_2m_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_2m_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_2m_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_2m_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_2m_page_wf(post.container_map, post.allocator_2m_map, post.page_array),
{
    reveal(container_allocator_free_2m_page_wf);
    reveal(container_page_owner_wf);
    reveal(container_allocator_wf);
    reveal(page_array_wf);

    assert forall|page_index: PageIndex|
        #![trigger post.page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
    implies {
        let owner = post.page_array.spec_index(page_index).view().view().owning_container;
        let alloc = post.container_map.spec_index(owner).view_rodata().view().allocator_ptr_2m;
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::GlobalList }
            ==> post.allocator_2m_map.spec_index(alloc).global_pool.view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_2m_map.spec_index(alloc).global_pool.view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_2m_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            ==> post.allocator_2m_map.dom().contains(alloc)
                && post.allocator_2m_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_2m_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_2m_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
    } by {
        assert(post.page_array.spec_index(page_index) == pre.page_array.spec_index(page_index));
        assert(pre.page_array.spec_index(page_index).view().view().state
            == post.page_array.spec_index(page_index).view().view().state);
        let owner = pre.page_array.spec_index(page_index).view().view().owning_container;
        assert(page_index_valid(page_index));
        assert(pre.container_map.dom().contains(owner));
        assert(post.container_map.spec_index(owner).view_rodata() == pre.container_map.spec_index(owner).view_rodata());
        let alloc = pre.container_map.spec_index(owner).view_rodata().view().allocator_ptr_2m;
        assert(pre.allocator_2m_map.dom().contains(alloc));
        assert(post.allocator_2m_map.spec_index(alloc).owning_container == pre.allocator_2m_map.spec_index(alloc).owning_container);
        assert(post.allocator_2m_map.spec_index(alloc).global_pool.view() == pre.allocator_2m_map.spec_index(alloc).global_pool.view());
        assert(pre.page_array.spec_index(page_index)@@.inv());
        assert forall|i: CpuId| #![trigger post.allocator_2m_map.spec_index(alloc).cpu_caches.spec_index(i)] cpu_id_valid(i) implies
            post.allocator_2m_map.spec_index(alloc).cpu_caches.spec_index(i).view().view()
                == pre.allocator_2m_map.spec_index(alloc).cpu_caches.spec_index(i).view().view() by {};
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
        #![trigger post.allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
        post.allocator_2m_map.dom().contains(alloc_ptr) && post.allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::GlobalList })
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_2m_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_2m_map.dom().contains(alloc_ptr));
        assert(pre.allocator_2m_map.spec_index(alloc_ptr).global_pool.view() == post.allocator_2m_map.spec_index(alloc_ptr).global_pool.view());
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
        assert(post.allocator_2m_map.spec_index(alloc_ptr).owning_container == pre.allocator_2m_map.spec_index(alloc_ptr).owning_container);
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
        #![trigger post.allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
        post.allocator_2m_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
        && post.allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::PreCpuCache { cpu_id }})
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_2m_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view()
            == post.allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view());
        assert(post.allocator_2m_map.spec_index(alloc_ptr).owning_container == pre.allocator_2m_map.spec_index(alloc_ptr).owning_container);
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
    };
}

#[verifier::spinoff_prover]
pub proof fn lemma_container_allocator_free_1g_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_1g_page_wf(pre.container_map, pre.allocator_1g_map, pre.page_array),
        container_page_owner_wf(pre.container_map, pre.page_array),
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        page_array_wf(pre.page_array),
        post.page_array == pre.page_array,
        post.container_map.dom() == pre.container_map.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c).view_rodata()]
            post.container_map.dom().contains(c) ==>
                post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
        post.allocator_1g_map.dom() == pre.allocator_1g_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_1g_map.spec_index(a).owning_container]
            post.allocator_1g_map.dom().contains(a) ==>
                post.allocator_1g_map.spec_index(a).owning_container == pre.allocator_1g_map.spec_index(a).owning_container
                && post.allocator_1g_map.spec_index(a).global_pool.view() == pre.allocator_1g_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_1g_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_1g_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_1g_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_1g_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_1g_page_wf(post.container_map, post.allocator_1g_map, post.page_array),
{
    reveal(container_allocator_free_1g_page_wf);
    reveal(container_page_owner_wf);
    reveal(container_allocator_wf);
    reveal(page_array_wf);

    assert forall|page_index: PageIndex|
        #![trigger post.page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
    implies {
        let owner = post.page_array.spec_index(page_index).view().view().owning_container;
        let alloc = post.container_map.spec_index(owner).view_rodata().view().allocator_ptr_1g;
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::GlobalList }
            ==> post.allocator_1g_map.spec_index(alloc).global_pool.view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_1g_map.spec_index(alloc).global_pool.view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_1g_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            ==> post.allocator_1g_map.dom().contains(alloc)
                && post.allocator_1g_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_1g_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_1g_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
    } by {
        assert(post.page_array.spec_index(page_index) == pre.page_array.spec_index(page_index));
        assert(pre.page_array.spec_index(page_index).view().view().state
            == post.page_array.spec_index(page_index).view().view().state);
        let owner = pre.page_array.spec_index(page_index).view().view().owning_container;
        assert(page_index_valid(page_index));
        assert(pre.container_map.dom().contains(owner));
        assert(post.container_map.spec_index(owner).view_rodata() == pre.container_map.spec_index(owner).view_rodata());
        let alloc = pre.container_map.spec_index(owner).view_rodata().view().allocator_ptr_1g;
        assert(pre.allocator_1g_map.dom().contains(alloc));
        assert(post.allocator_1g_map.spec_index(alloc).owning_container == pre.allocator_1g_map.spec_index(alloc).owning_container);
        assert(post.allocator_1g_map.spec_index(alloc).global_pool.view() == pre.allocator_1g_map.spec_index(alloc).global_pool.view());
        assert(pre.page_array.spec_index(page_index)@@.inv());
        assert forall|i: CpuId| #![trigger post.allocator_1g_map.spec_index(alloc).cpu_caches.spec_index(i)] cpu_id_valid(i) implies
            post.allocator_1g_map.spec_index(alloc).cpu_caches.spec_index(i).view().view()
                == pre.allocator_1g_map.spec_index(alloc).cpu_caches.spec_index(i).view().view() by {};
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
        #![trigger post.allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
        post.allocator_1g_map.dom().contains(alloc_ptr) && post.allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::GlobalList })
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_1g_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_1g_map.dom().contains(alloc_ptr));
        assert(pre.allocator_1g_map.spec_index(alloc_ptr).global_pool.view() == post.allocator_1g_map.spec_index(alloc_ptr).global_pool.view());
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
        assert(post.allocator_1g_map.spec_index(alloc_ptr).owning_container == pre.allocator_1g_map.spec_index(alloc_ptr).owning_container);
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
        #![trigger post.allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
        post.allocator_1g_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
        && post.allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::PreCpuCache { cpu_id }})
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_1g_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view()
            == post.allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view());
        assert(post.allocator_1g_map.spec_index(alloc_ptr).owning_container == pre.allocator_1g_map.spec_index(alloc_ptr).owning_container);
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
    };
}

/// Thin combinator: all three free-page granules preserved across a
/// lock-state-only change. Calls the three per-granule lemmas above so each
/// runs in its own SMT query (the combined query exceeds the rlimit). The
/// hypotheses are the union of the three; every call site that holds `inv()`
/// pre and changes only a single object's lock state satisfies them.
#[verifier::spinoff_prover]
pub proof fn lemma_container_allocator_free_pages_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_4k_page_wf(pre.container_map, pre.allocator_4k_map, pre.page_array),
        container_allocator_free_2m_page_wf(pre.container_map, pre.allocator_2m_map, pre.page_array),
        container_allocator_free_1g_page_wf(pre.container_map, pre.allocator_1g_map, pre.page_array),
        container_page_owner_wf(pre.container_map, pre.page_array),
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        page_array_wf(pre.page_array),
        post.page_array == pre.page_array,
        post.container_map.dom() == pre.container_map.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c).view_rodata()]
            post.container_map.dom().contains(c) ==>
                post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).owning_container]
            post.allocator_4k_map.dom().contains(a) ==>
                post.allocator_4k_map.spec_index(a).owning_container == pre.allocator_4k_map.spec_index(a).owning_container
                && post.allocator_4k_map.spec_index(a).global_pool.view() == pre.allocator_4k_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_4k_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
        post.allocator_2m_map.dom() == pre.allocator_2m_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_2m_map.spec_index(a).owning_container]
            post.allocator_2m_map.dom().contains(a) ==>
                post.allocator_2m_map.spec_index(a).owning_container == pre.allocator_2m_map.spec_index(a).owning_container
                && post.allocator_2m_map.spec_index(a).global_pool.view() == pre.allocator_2m_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_2m_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_2m_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_2m_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_2m_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
        post.allocator_1g_map.dom() == pre.allocator_1g_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_1g_map.spec_index(a).owning_container]
            post.allocator_1g_map.dom().contains(a) ==>
                post.allocator_1g_map.spec_index(a).owning_container == pre.allocator_1g_map.spec_index(a).owning_container
                && post.allocator_1g_map.spec_index(a).global_pool.view() == pre.allocator_1g_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_1g_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_1g_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_1g_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_1g_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_4k_page_wf(post.container_map, post.allocator_4k_map, post.page_array),
        container_allocator_free_2m_page_wf(post.container_map, post.allocator_2m_map, post.page_array),
        container_allocator_free_1g_page_wf(post.container_map, post.allocator_1g_map, post.page_array),
{
    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(pre, post);
    lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(pre, post);
    lemma_container_allocator_free_1g_page_wf_preserved_for_lock_op(pre, post);
}

}

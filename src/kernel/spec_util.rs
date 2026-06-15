use vstd::prelude::*;
use crate::*;
use super::*;
verus! {

// ============================================================
//   Per-type "objects unlocked" pieces
// ============================================================
//
// `all_objects_unlocked` is split into one opaque predicate per object
// kind. Keeping each piece opaque means the (large) `all_objects_unlocked`
// precondition only seeds the proof context with opaque calls, not ~18
// quantifiers — callers reveal just the pieces they actually touch.

#[verifier::opaque]
pub open spec fn cpu_objects_unlocked(cpu_array: LockedArray<Cpu, (), (), (), NUM_CPUS, CPU_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|cpu_i: CpuId|
        #![trigger cpu_array.spec_index(cpu_i).view().locked_by(lctx)]
        cpu_id_valid(cpu_i)
        ==>
        cpu_array.spec_index(cpu_i).view().locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn page_objects_unlocked(page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|p_i: PageIndex|
        #![trigger page_array.spec_index(p_i).view().locked_by(lctx)]
        page_index_valid(p_i)
        ==>
        page_array.spec_index(p_i).view().locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn container_objects_unlocked(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr)
        ==>
        container_map.spec_index(c_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn process_objects_unlocked(process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.dom().contains(p_ptr)]
        process_map.dom().contains(p_ptr)
        ==>
        process_map.spec_index(p_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn thread_objects_unlocked(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locked_by(lctx)]
        thread_map.dom().contains(t_ptr)
        ==>
        thread_map.spec_index(t_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn endpoint_objects_unlocked(endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|e_ptr: RwLockEndpointPtr|
        #![trigger endpoint_map.spec_index(e_ptr).locked_by(lctx)]
        endpoint_map.dom().contains(e_ptr)
        ==>
        endpoint_map.spec_index(e_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn pagetable_objects_unlocked(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pagetable_map.spec_index(pt_ptr).locked_by(lctx)]
        pagetable_map.dom().contains(pt_ptr)
        ==>
        pagetable_map.spec_index(pt_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn scheduler_objects_unlocked(scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|s_ptr: RwLockSchedulerPtr|
        #![trigger scheduler_map.spec_index(s_ptr).locked_by(lctx)]
        scheduler_map.dom().contains(s_ptr)
        ==>
        scheduler_map.spec_index(s_ptr).locked_by(lctx) == false
}

/// Reusable across the 4k / 2m / 1g allocator maps: quota, global poll, and
/// every cpu cache of every allocator is unlocked.
#[verifier::opaque]
pub open spec fn allocator_objects_unlocked(alloc_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>, lctx: &LocalContext) -> bool {
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr|
        #![trigger alloc_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
        alloc_map.dom().contains(alloc_ptr)
        ==>
        alloc_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr|
        #![trigger alloc_map.spec_index(alloc_ptr).quota.locked_by(lctx)]
        alloc_map.dom().contains(alloc_ptr)
        ==>
        alloc_map.spec_index(alloc_ptr).quota.locked_by(lctx) == false
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
        #![trigger alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
        alloc_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
        ==>
        alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false
}

impl KernelK{
    /// Everything is unlocked EXCEPT the cpu at `cpu_id`, the container at
    /// `container_ptr`, and the 4k allocator quota at `alloc_ptr_4k`. Used as
    /// a precondition for the exit-path helper so it can derive
    /// `all_objects_unlocked` after the 3 wunlocks.
    pub open spec fn all_objects_unlocked_except_3(
        &self,
        lctx: &LocalContext,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
    ) -> bool {
        // Pages: all unlocked
        &&& page_objects_unlocked(self.page_array, lctx)
        // CPU: all except cpu_id
        &&& (forall|cpu_i: CpuId|
            #![trigger self.cpu_array.spec_index(cpu_i).view().locked_by(lctx)]
            cpu_id_valid(cpu_i) && cpu_i != cpu_id
            ==>
            self.cpu_array.spec_index(cpu_i).view().locked_by(lctx) == false)
        // Containers: all except container_ptr
        &&& (forall|c_ptr: RwLockContainerPtr|
            #![trigger self.container_map.dom().contains(c_ptr)]
            self.container_map.dom().contains(c_ptr) && c_ptr != container_ptr
            ==>
            self.container_map.spec_index(c_ptr).locked_by(lctx) == false)
        // Processes: all unlocked
        &&& process_objects_unlocked(self.process_map, lctx)
        // Threads: all unlocked
        &&& thread_objects_unlocked(self.thread_map, lctx)
        // Endpoints: all unlocked
        &&& endpoint_objects_unlocked(self.endpoint_map, lctx)
        // Pagetables: all unlocked
        &&& pagetable_objects_unlocked(self.pagetable_map, lctx)
        // Schedulers: all unlocked
        &&& scheduler_objects_unlocked(self.scheduler_map, lctx)
        // 4k allocators: quota unlocked for all except alloc_ptr_4k; global_poll + cpu_caches all unlocked
        &&& (forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).quota.locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr) && alloc_ptr != alloc_ptr_4k
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).quota.locked_by(lctx) == false)
        &&& (forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr)
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false)
        &&& (forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false)
        // 2m allocators: all unlocked
        &&& allocator_objects_unlocked(self.allocator_2m_map, lctx)
        // 1g allocators: all unlocked
        &&& allocator_objects_unlocked(self.allocator_1g_map, lctx)
    }

    pub open spec fn get_process_pagetable(&self, process_ptr:RwLockProcessPtr) -> PageTable<PT_TYPE>
        recommends
            self.process_map.dom().contains(process_ptr)
    {
        self.pagetable_map.spec_index(self.process_map.spec_index(process_ptr).view().pagetable).view()
    }
    pub open spec fn get_container_quota_4k(&self, container_ptr:RwLockContainerPtr) -> usize
        recommends
            self.container_map.dom().contains(container_ptr)
    {
        self.allocator_4k_map.spec_index(self.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value
    }

    /// Open conjunction of the per-type opaque pieces. Reveal only the piece
    /// you need (e.g. `cpu_objects_unlocked` before a cpu `wlock`).
    pub open spec fn all_objects_unlocked(&self, lctx: &LocalContext) -> bool{
        &&& cpu_objects_unlocked(self.cpu_array, lctx)
        &&& page_objects_unlocked(self.page_array, lctx)
        &&& container_objects_unlocked(self.container_map, lctx)
        &&& process_objects_unlocked(self.process_map, lctx)
        &&& thread_objects_unlocked(self.thread_map, lctx)
        &&& endpoint_objects_unlocked(self.endpoint_map, lctx)
        &&& pagetable_objects_unlocked(self.pagetable_map, lctx)
        &&& scheduler_objects_unlocked(self.scheduler_map, lctx)
        &&& allocator_objects_unlocked(self.allocator_4k_map, lctx)
        &&& allocator_objects_unlocked(self.allocator_2m_map, lctx)
        &&& allocator_objects_unlocked(self.allocator_1g_map, lctx)
    }
}

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

/// Trusted axiom (TCB): the sum-fold of `process.view().quota_4k` over a
/// set is preserved when each process's quota_4k is preserved across
/// `pre`/`post` process maps. Soundness rationale:
///  - Finite case: induct on the set. Empty case: `0 == 0`. Insert step:
///    `lemma_fold_insert` gives `(s.insert(a)).fold = f(s.fold, a)`; the
///    inductive hypothesis on `s` plus the per-element quota equality
///    closes it.
///  - Non-finite case: `Set::fold` returns the init `0` for both, so the
///    equality holds trivially.
#[verifier::external_body]
pub proof fn lemma_process_quota_4k_fold_eq_under_view_eq(
    s: Set<RwLockProcessPtr>,
    pre: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
    post: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger pre.spec_index(p).view().quota_4k]
            #![trigger post.spec_index(p).view().quota_4k]
            s.contains(p) ==>
                post.spec_index(p).view().quota_4k == pre.spec_index(p).view().quota_4k,
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.spec_index(p_ptr).view().quota_4k)
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + pre.spec_index(p_ptr).view().quota_4k),
{
}

/// Trusted axiom (TCB): like above for `quota_2m`.
#[verifier::external_body]
pub proof fn lemma_process_quota_2m_fold_eq_under_view_eq(
    s: Set<RwLockProcessPtr>,
    pre: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
    post: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger pre.spec_index(p).view().quota_2m]
            #![trigger post.spec_index(p).view().quota_2m]
            s.contains(p) ==>
                post.spec_index(p).view().quota_2m == pre.spec_index(p).view().quota_2m,
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.spec_index(p_ptr).view().quota_2m)
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + pre.spec_index(p_ptr).view().quota_2m),
{
}

/// Trusted axiom (TCB): like above for `quota_1g`.
#[verifier::external_body]
pub proof fn lemma_process_quota_1g_fold_eq_under_view_eq(
    s: Set<RwLockProcessPtr>,
    pre: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
    post: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
)
    requires
        forall|p: RwLockProcessPtr|
            #![trigger pre.spec_index(p).view().quota_1g]
            #![trigger post.spec_index(p).view().quota_1g]
            s.contains(p) ==>
                post.spec_index(p).view().quota_1g == pre.spec_index(p).view().quota_1g,
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.spec_index(p_ptr).view().quota_1g)
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + pre.spec_index(p_ptr).view().quota_1g),
{
}

/// Trusted axiom (TCB): when exactly one process's `quota_4k` changes
/// across `pre`/`post`, the sum-fold of `quota_4k` over a set
/// containing that process changes by exactly the per-element delta.
/// Soundness rationale: induct on `s.remove(mod_p)` (a smaller set on
/// which pre and post are quota_4k-equal — apply the eq lemma above to
/// fold over `s.remove(mod_p)`), then re-insert `mod_p` using
/// `lemma_fold_insert`. Same shape as the user's
/// `fold_change_mem_4k_lemma` reference template, including the implicit
/// assumption that `owned_processes` is finite in any reachable kernel
/// state.
#[verifier::external_body]
pub proof fn lemma_process_quota_4k_fold_change_one(
    s: Set<RwLockProcessPtr>,
    pre: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
    post: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
    mod_p: RwLockProcessPtr,
)
    requires
        s.contains(mod_p),
        forall|p: RwLockProcessPtr|
            #![trigger pre.spec_index(p).view().quota_4k]
            #![trigger post.spec_index(p).view().quota_4k]
            s.contains(p) && p != mod_p ==>
                post.spec_index(p).view().quota_4k == pre.spec_index(p).view().quota_4k,
    ensures
        s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.spec_index(p_ptr).view().quota_4k)
            == s.fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + pre.spec_index(p_ptr).view().quota_4k)
                - pre.spec_index(mod_p).view().quota_4k as int
                + post.spec_index(mod_p).view().quota_4k as int,
{
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
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.process_map.spec_index(p_ptr).view().quota_4k)
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_container_quota_cache_4k.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_container_quota_cache_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
        assert(s.subset_of(post.process_map.dom()));
        // Process fold equality: from the trusted lemma + per-process view eq.
        lemma_process_quota_4k_fold_eq_under_view_eq(s, pre.process_map, post.process_map);
        // Pre-state spec at c_ptr (instantiate the forall by referencing the trigger).
        assert(pre.container_map.dom().contains(c_ptr));
        assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr);
        // Per-allocator quota.view() and total_free_pages preservation at this allocator.
        assert(post.allocator_4k_map.spec_index(alloc_ptr).quota.view() == pre.allocator_4k_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_4k_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_4k_map.spec_index(alloc_ptr).total_free_pages);
    };

    // 2m.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.process_map.spec_index(p_ptr).view().quota_2m)
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_container_quota_cache_2m.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_container_quota_cache_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m;
        assert(s.subset_of(post.process_map.dom()));
        lemma_process_quota_2m_fold_eq_under_view_eq(s, pre.process_map, post.process_map);
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
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.process_map.spec_index(p_ptr).view().quota_1g)
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_container_quota_cache_1g.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_container_quota_cache_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g;
        assert(s.subset_of(post.process_map.dom()));
        lemma_process_quota_1g_fold_eq_under_view_eq(s, pre.process_map, post.process_map);
        assert(pre.container_map.dom().contains(c_ptr));
        assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g == alloc_ptr);
        assert(post.allocator_1g_map.spec_index(alloc_ptr).quota.view() == pre.allocator_1g_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_1g_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_1g_map.spec_index(alloc_ptr).total_free_pages);
    };
}

/// Trusted axiom (TCB): for a release path that ALSO unlocks the running
/// process (in addition to cpu/container/quota), the user-view projection
/// `kernel_k_to_kernel_u` is preserved iff per-process view + view_rodata
/// equality holds (in addition to the usual cpu_array facts).
///
/// Why a TCB axiom instead of extending `lemma_release_preserves_user_view`:
/// the projection's `killed: process_map[p].being_killed()` field is the
/// problem. `wunlock_ensures` currently does NOT explicitly preserve
/// `being_killed()` — it only preserves view, view_rodata, and the kernel/
/// user ghost state. At runtime the wunlock impl doesn't touch `killer_info`
/// (so being_killed IS preserved), but the spec doesn't reflect this.
///
/// Soundness rationale (audit-able):
///  - cpu_array: unchanged_except + cpu_id view equality → projected
///    `cpu_array` is extensionally equal pre/post.
///  - process_map.dom() unchanged. Per p in dom: view, view_rodata equal
///    pre/post (caller-provided).
///  - being_killed() preserved per p: wunlock impl doesn't write
///    `killer_info`; `unchanged_except` covers off-key.
///  - get_process_pagetable(p) preserved: depends on
///    `process_map[p].view().pagetable` (preserved per-process) and
///    `pagetable_map` (byte-equal pre/post).
/// Therefore each component of `kernel_k_to_kernel_u` evaluates identically.
/// Note: container_map equality is NOT required (the projection doesn't
/// read container_map).
#[verifier::external_body]
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
                && post.process_map.spec_index(p).view_rodata() == pre.process_map.spec_index(p).view_rodata(),
        post.pagetable_map == pre.pagetable_map,
        post.cpu_array.unchanged_except(&pre.cpu_array, cpu_id),
        post.cpu_array.spec_index(cpu_id).view().view()
            == pre.cpu_array.spec_index(cpu_id).view().view(),
    ensures
        kernel_k_to_kernel_u(pre) == kernel_k_to_kernel_u(post),
{
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
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.process_map.spec_index(p_ptr).view().quota_4k)
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_container_quota_cache_4k.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_container_quota_cache_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
        assert(pre.container_map.dom().contains(c_ptr));
        if c_ptr == container_ptr {
            // process_ptr ∈ s; alloc_ptr == alloc_ptr_4k. Process fold gains
            // +alloc_amount; allocator term loses -alloc_amount. Balanced.
            assert(s.contains(process_ptr));
            assert(alloc_ptr == alloc_ptr_4k);
            lemma_process_quota_4k_fold_change_one(s, pre.process_map, post.process_map, process_ptr);
        } else {
            // process_ptr ∉ s (each process owned by exactly one container);
            // alloc_ptr != alloc_ptr_4k (each container has unique allocator).
            // Both folds and the allocator term are preserved.
            assert(!s.contains(process_ptr)) by {
                // container_process_wf 2nd conjunct: c.owned_processes contains p ⇒
                // p.owning_container == c. If process_ptr ∈ s = c_ptr.owned_processes,
                // then process_ptr.owning_container == c_ptr. But also from container_ptr
                // owning process_ptr, process_ptr.owning_container == container_ptr.
                // Contradicts c_ptr != container_ptr.
            };
            assert(alloc_ptr != alloc_ptr_4k) by {
                // container_allocator_wf forward direction: allocator's owning_container
                // is the container that points to it. If alloc_ptr == alloc_ptr_4k, then
                // the owning_container of alloc_ptr_4k is BOTH c_ptr and container_ptr.
                // Contradicts c_ptr != container_ptr.
            };
            lemma_process_quota_4k_fold_eq_under_view_eq(s, pre.process_map, post.process_map);
            assert(post.allocator_4k_map.spec_index(alloc_ptr).quota.view() == pre.allocator_4k_map.spec_index(alloc_ptr).quota.view());
            assert(post.allocator_4k_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_4k_map.spec_index(alloc_ptr).total_free_pages);
        };
    };

    // 2m. process.quota_2m and allocator_2m are fully preserved per-element.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.process_map.spec_index(p_ptr).view().quota_2m)
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_container_quota_cache_2m.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_container_quota_cache_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m;
        assert(pre.container_map.dom().contains(c_ptr));
        // Per-process quota_2m equal: post[process_ptr].quota_2m == pre[...].quota_2m
        // (precondition); for p != process_ptr, post[p].view() == pre[p].view().
        lemma_process_quota_2m_fold_eq_under_view_eq(s, pre.process_map, post.process_map);
        assert(post.allocator_2m_map.spec_index(alloc_ptr).quota.view() == pre.allocator_2m_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_2m_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_2m_map.spec_index(alloc_ptr).total_free_pages);
    };

    // 1g.
    assert forall|c_ptr: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
        post.container_map.dom().contains(c_ptr)
    implies
        post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + post.process_map.spec_index(p_ptr).view().quota_1g)
            + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().direct_container_quota_cache_1g.view())
            + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| sum + post.thread_map.spec_index(t_ptr).view().indirect_container_quota_cache_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
            + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
    by {
        let s = post.container_map.spec_index(c_ptr).view().owned_processes.view();
        let alloc_ptr = post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g;
        assert(pre.container_map.dom().contains(c_ptr));
        lemma_process_quota_1g_fold_eq_under_view_eq(s, pre.process_map, post.process_map);
        assert(post.allocator_1g_map.spec_index(alloc_ptr).quota.view() == pre.allocator_1g_map.spec_index(alloc_ptr).quota.view());
        assert(post.allocator_1g_map.spec_index(alloc_ptr).total_free_pages == pre.allocator_1g_map.spec_index(alloc_ptr).total_free_pages);
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
    old_process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
    new_process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
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
    reveal(process_childern_parent_wf);
    reveal(processs_linkedlist_wf);
    reveal(process_childern_depth_wf);
    reveal(process_subtree_set_wf);
    reveal(process_uppertree_seq_wf);
    reveal(process_subtree_set_exclusive);
}

}

//! Lock-order deadlock freedom over the kernel's own held-lock records.
//!
//! A `LockWaitSnapshot` is one physical instant: every cpu's `LocalContext` (`src/locks/local_context.rs:41`), the object
//! and `LockId` each spinning cpu waits for, and which cpus a spinning cpu is physically waiting on. The hypotheses are
//! the facts the kernel's lock contracts give (each spec cites them), plus `holder_records_cover_wanted_ids`, which no
//! contract states. The conclusions: the waits-for relation has no cycle, and every nonempty set of spinning cpus has a
//! member that waits on no member of the set.
use vstd::prelude::*;
use crate::*;

verus! {
/// One instant of the machine as far as lock waiting goes. `held[c]` is cpu `c`'s `LocalContext`. `wanted[c]`, present
/// exactly for the cpus spinning inside a lock primitive, is the object it spins on and the id its acquisition contract
/// ordered against (`old(lctx).lock_id_acyclic(id)`). `blocked_by(a, b)` says spinning cpu `a` cannot take its lock
/// because of cpu `b`.
pub ghost struct LockWaitSnapshot {
    pub held: Map<CpuId, LocalContext>,
    pub wanted: Map<CpuId, (KernelObjId, LockId)>,
    pub blocked_by: spec_fn(CpuId, CpuId) -> bool,
}

/// `c` spins inside a lock primitive.
pub open spec fn waiting(s: LockWaitSnapshot, c: CpuId) -> bool { s.wanted.dom().contains(c) }

/// The object `c` spins on.
pub open spec fn wanted_obj(s: LockWaitSnapshot, c: CpuId) -> KernelObjId { s.wanted[c].0 }

/// The id `c`'s acquisition was ordered against.
pub open spec fn wanted_id(s: LockWaitSnapshot, c: CpuId) -> LockId { s.wanted[c].1 }

/// `b`'s context records `obj` (read or write).
pub open spec fn records_obj(s: LockWaitSnapshot, b: CpuId, obj: KernelObjId) -> bool {
    s.held.dom().contains(b) && s.held[b].typed_lock_entry(obj) is Some
}

/// The id `b`'s context records for `obj`.
pub open spec fn recorded_id(s: LockWaitSnapshot, b: CpuId, obj: KernelObjId) -> LockId { s.held[b].typed_lock_entry(obj)->Some_0.lock_id }

/// `b` holds the lock `a` spins on.
pub open spec fn holds_wanted_lock(s: LockWaitSnapshot, a: CpuId, b: CpuId) -> bool { records_obj(s, b, wanted_obj(s, a)) }

/// `b` is a writer of the same per-cpu reader lock that has passed slot 0 (or set the pending mark) and spins on the same
/// lock with the same id, and every cpu `b` waits on holds that lock.
pub open spec fn queued_writer_ahead(s: LockWaitSnapshot, a: CpuId, b: CpuId) -> bool {
    &&& waiting(s, b)
    &&& s.wanted[b] == s.wanted[a]
    &&& forall|c: CpuId| #[trigger] (s.blocked_by)(b, c) ==> holds_wanted_lock(s, b, c)
}

/// Hypothesis 1. A spinning cpu's wanted id is above every id its own context records. Every waiting primitive requires
/// `old(lctx).lock_id_acyclic(id)` (`src/locks/local_context.rs:227`) for the id it records: `src/locks/locked_points_to.rs`
/// `wlock` :40, `rlock` :86, `has_kill_state_rlock` :397, `wlock_array_cell` :592, `wlock_object_minor` :650 (via
/// `TokenLock::wlock`, `src/locks/token_lock.rs:92`), `src/allocator/page_allocator_lock_t.rs` `wlock_quota` :12,
/// `wlock_cache`, `wlock_global_pool`, `src/proc/scheduler_lock_t.rs` `wlock_shard`, `src/cpu/cpu_offline_flags_lock_t.rs`
/// `wlock_flag`, and the window locker `src/pagetable_concurrent/pagetable_concurrent_lock.rs:21`. The killable forms
/// require it only for an unmarked object (`locked_points_to.rs` :164, :198, :269, :322, :453, :490); a marked object makes
/// them return at once (`src/locks/lock_inner_t.rs:85-95`, :155-160, :215-222), so a marked object never has a waiter.
pub open spec fn waiters_respect_lock_order(s: LockWaitSnapshot) -> bool {
    forall|c: CpuId| #[trigger] waiting(s, c) ==> s.held.dom().contains(c) && s.held[c].lock_id_acyclic(wanted_id(s, c))
}

/// Hypothesis 2. A cpu spins only because of a holder of its lock, or of a writer queued ahead of it on the same per-cpu
/// reader lock. `SpinWord` (`src/locks/lock_inner_t.rs:53`) spins only while the write bit is set, and only the holder
/// sets it; `PerCpuReaderSlots` (:185) lets a writer hold slots 0..i and the pending mark while it spins on slot i
/// (:200-232), which blocks readers and later writers although that writer does not hold the lock yet; such a writer
/// waits only for read holders, since only one writer gets past slot 0. A held lock is recorded in its holder's context
/// (`typed_lock_maps_aligned`, `src/kernel/kernel_k_define_spec.rs:453`).
pub open spec fn blocked_only_by_holders_or_queued_writers(s: LockWaitSnapshot) -> bool {
    forall|a: CpuId, b: CpuId| #[trigger] (s.blocked_by)(a, b) ==> waiting(s, a) && (holds_wanted_lock(s, a, b) || queued_writer_ahead(s, a, b))
}

/// Hypothesis 3, stated by no kernel contract. The id a blocking holder records for the lock is at or above the id the
/// spinning cpu ordered against. The kernel contracts are sequential: a waiter's `old(lctx).lock_id_acyclic(id)` is about
/// the object's id in its own view, and the step boundary TCB (`kernel_step_boundary_raw`,
/// `src/kernel/kernel_k_define_spec.rs:288`) makes that view the state at acquisition. Equality with the holder's record
/// follows when the id did not move while the waiter spins: ids move only under the object's write lock in the Release
/// phase (`update_lock_id`, `src/locks/local_context.rs:318`) or by a kill mark, and a spinning holder is in its Acquire
/// phase (`wlock_requires`, `src/locks/lock_cell.rs:285`). A dynamic container acquisition requesting owner `r` spins
/// only on a holder that recorded `h >= r` (`src/locks/lock_inner_t.rs:164`), hence at-or-above rather than equal.
pub open spec fn holder_records_cover_wanted_ids(s: LockWaitSnapshot) -> bool {
    forall|a: CpuId, b: CpuId| #[trigger] (s.blocked_by)(a, b) && holds_wanted_lock(s, a, b) ==> recorded_id(s, b, wanted_obj(s, a)).spec_ge(wanted_id(s, a))
}

/// All three hypotheses.
pub open spec fn lock_order_hypotheses(s: LockWaitSnapshot) -> bool {
    &&& waiters_respect_lock_order(s)
    &&& blocked_only_by_holders_or_queued_writers(s)
    &&& holder_records_cover_wanted_ids(s)
}

/// `cycle` is a nonempty cycle of the waits-for relation.
pub open spec fn is_wait_cycle(s: LockWaitSnapshot, cycle: Seq<CpuId>) -> bool {
    &&& cycle.len() > 0
    &&& forall|i: int| 0 <= i < cycle.len() ==> #[trigger] (s.blocked_by)(cycle[i], cycle[(i + 1) % (cycle.len() as int)])
}

/// No minor is below itself.
pub proof fn lock_minor_lt_self_implies_false(m: LockMinorId)
    ensures !lock_minor_lt(m, m),
    decreases m.len(),
{
    if m.len() > 1 { lock_minor_lt_self_implies_false(m.skip(1)); }
}

/// No lock id is above itself.
pub proof fn lock_id_gt_self_implies_false(a: LockId)
    ensures !a.spec_gt(a),
{ lock_minor_lt_self_implies_false(a.minor); }

/// `a > b >= c` implies `a > c`.
pub proof fn lock_id_gt_ge_implies_gt(a: LockId, b: LockId, c: LockId)
    requires a.spec_gt(b), b.spec_ge(c),
    ensures a.spec_gt(c),
{ if b != c { lock_id_gt_transitive(a, b, c); } }

/// A context's `lock_id_acyclic(id)` puts `id` above the id of every object it records.
pub proof fn lock_id_acyclic_implies_above_recorded(lctx: LocalContext, id: LockId, obj: KernelObjId)
    requires lctx.lock_id_acyclic(id), lctx.typed_lock_entry(obj) is Some,
    ensures id.spec_gt(lctx.typed_lock_entry(obj)->Some_0.lock_id),
{ reveal(LocalContext::lock_id_acyclic); }

/// Under the hypotheses, a spinning cpu that waits on a spinning holder wants a strictly higher id than that holder.
pub proof fn lock_order_hypotheses_and_holder_edge_implies_wanted_id_increases(s: LockWaitSnapshot, a: CpuId, b: CpuId)
    requires lock_order_hypotheses(s), (s.blocked_by)(a, b), holds_wanted_lock(s, a, b), waiting(s, b),
    ensures wanted_id(s, b).spec_gt(wanted_id(s, a)),
{
    lock_id_acyclic_implies_above_recorded(s.held[b], wanted_id(s, b), wanted_obj(s, a));
    lock_id_gt_ge_implies_gt(wanted_id(s, b), recorded_id(s, b, wanted_obj(s, a)), wanted_id(s, a));
}

/// Every nonempty set of spinning cpus has a member whose wanted id no member's wanted id exceeds.
pub proof fn waiting_set_implies_maximal_wanted_id(s: LockWaitSnapshot, cpus: Set<CpuId>) -> (m: CpuId)
    requires cpus.len() > 0,
    ensures cpus.contains(m), forall|c: CpuId| #[trigger] cpus.contains(c) ==> !wanted_id(s, c).spec_gt(wanted_id(s, m)),
    decreases cpus.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    let x = cpus.choose();
    let rest = cpus.remove(x);
    if rest.len() == 0 {
        assert forall|c: CpuId| #[trigger] cpus.contains(c) implies !wanted_id(s, c).spec_gt(wanted_id(s, x)) by {
            if c != x { assert(rest.contains(c)); }
            lock_id_gt_self_implies_false(wanted_id(s, x));
        };
        x
    } else {
        let m = waiting_set_implies_maximal_wanted_id(s, rest);
        if wanted_id(s, x).spec_gt(wanted_id(s, m)) {
            assert forall|c: CpuId| #[trigger] cpus.contains(c) implies !wanted_id(s, c).spec_gt(wanted_id(s, x)) by {
                if c == x { lock_id_gt_self_implies_false(wanted_id(s, x)); }
                else if wanted_id(s, c).spec_gt(wanted_id(s, x)) {
                    assert(rest.contains(c));
                    lock_id_gt_transitive(wanted_id(s, c), wanted_id(s, x), wanted_id(s, m));
                }
            };
            x
        } else {
            assert forall|c: CpuId| #[trigger] cpus.contains(c) implies !wanted_id(s, c).spec_gt(wanted_id(s, m)) by {
                if c != x { assert(rest.contains(c)); }
            };
            m
        }
    }
}

/// Some lock holder can always run: among any nonempty set of spinning cpus, one waits on no member of the set, so the
/// lock it wants is free, or held only by cpus outside the set.
pub proof fn lock_order_hypotheses_implies_unblocked_waiter(s: LockWaitSnapshot, cpus: Set<CpuId>) -> (a: CpuId)
    requires
        lock_order_hypotheses(s),
        cpus.len() > 0,
        forall|c: CpuId| #[trigger] cpus.contains(c) ==> waiting(s, c),
    ensures
        cpus.contains(a),
        forall|b: CpuId| #[trigger] cpus.contains(b) ==> !(s.blocked_by)(a, b),
{
    let m = waiting_set_implies_maximal_wanted_id(s, cpus);
    if exists|b: CpuId| #[trigger] cpus.contains(b) && (s.blocked_by)(m, b) && !holds_wanted_lock(s, m, b) {
        // A writer queued ahead of `m` has `m`'s wanted id and waits only on holders, which would want a higher id.
        let q = choose|b: CpuId| #[trigger] cpus.contains(b) && (s.blocked_by)(m, b) && !holds_wanted_lock(s, m, b);
        assert forall|b: CpuId| #[trigger] cpus.contains(b) implies !(s.blocked_by)(q, b) by {
            if (s.blocked_by)(q, b) { lock_order_hypotheses_and_holder_edge_implies_wanted_id_increases(s, q, b); }
        };
        q
    } else {
        assert forall|b: CpuId| #[trigger] cpus.contains(b) implies !(s.blocked_by)(m, b) by {
            if (s.blocked_by)(m, b) { lock_order_hypotheses_and_holder_edge_implies_wanted_id_increases(s, m, b); }
        };
        m
    }
}

/// The waits-for relation has no cycle.
pub proof fn lock_order_hypotheses_implies_no_wait_cycle(s: LockWaitSnapshot, cycle: Seq<CpuId>)
    requires lock_order_hypotheses(s),
    ensures !is_wait_cycle(s, cycle),
{
    broadcast use vstd::set::group_set_lemmas;
    if is_wait_cycle(s, cycle) {
        let cpus = cycle.to_set();
        cycle.to_set_ensures();
        assert(cpus.contains(cycle[0]));
        assert forall|c: CpuId| #[trigger] cpus.contains(c) implies waiting(s, c) by {
            let i = choose|i: int| 0 <= i < cycle.len() && cycle[i] == c;
            assert((s.blocked_by)(cycle[i], cycle[(i + 1) % (cycle.len() as int)]));
        };
        let a = lock_order_hypotheses_implies_unblocked_waiter(s, cpus);
        let i = choose|i: int| 0 <= i < cycle.len() && cycle[i] == a;
        assert((s.blocked_by)(cycle[i], cycle[(i + 1) % (cycle.len() as int)]));
        assert(0 <= (i + 1) % (cycle.len() as int) < cycle.len()) by (nonlinear_arith) requires 0 <= i < cycle.len();
        assert(cpus.contains(cycle[(i + 1) % (cycle.len() as int)]));
    }
}

/// The hypotheses are satisfiable with spinning cpus and a waits-for edge: cpus 0 and 1 hold nothing and spin on the
/// same page lock, and cpu 1 waits on cpu 0 queued ahead of it.
pub proof fn lock_order_hypotheses_satisfiable()
{
    broadcast use vstd::set::group_set_lemmas;
    let tracked c0 = LocalContext::new_bootstrap(0);
    let tracked c1 = LocalContext::new_bootstrap(1);
    let obj = KernelObjId::Page(0);
    let id = LockId { container: LockOwnerId::None, process: LockOwnerId::None, major: FREE_PAGE_LOCK_MAJOR, minor: seq![0usize] };
    let s = LockWaitSnapshot {
        held: Map::empty().insert(0usize, c0).insert(1usize, c1),
        wanted: Map::empty().insert(0usize, (obj, id)).insert(1usize, (obj, id)),
        blocked_by: |a: CpuId, b: CpuId| a == 1 && b == 0,
    };
    assert(s.held.dom().contains(0usize) && s.held.dom().contains(1usize));
    assert(s.held[0usize].lock_id_acyclic(id) && s.held[1usize].lock_id_acyclic(id)) by { reveal(LocalContext::lock_id_acyclic); };
    assert(waiters_respect_lock_order(s));
    assert(queued_writer_ahead(s, 1usize, 0usize));
    assert(blocked_only_by_holders_or_queued_writers(s));
    assert(lock_order_hypotheses(s));
    assert(waiting(s, 0usize) && waiting(s, 1usize) && (s.blocked_by)(1usize, 0usize));
}
}

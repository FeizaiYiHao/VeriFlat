//! Part B, under explicit fairness hypotheses: a thread that is not blocked eventually runs, or is killed or gone
//! (`fair_world_implies_unblocked_thread_eventually_runs`).
//!
//! The hypotheses, each a property of the behaviour:
//! (1) `timer_ticks_infinitely_often`: timer interrupts arrive infinitely often on every online cpu and each runs the
//!     cpu's tick-driven scheduling entries, the scheduler and the orphan pull with a cursor that takes every value; a lock
//!     the entry waits for is always obtained, so an entry whose call would act (its `*_syscall_result` would switch or pull
//!     on an online cpu) takes its step. In U: from every index on, each cpu eventually takes a Schedule step or reaches a
//!     state in which the scheduler would not switch, and for every cursor eventually takes that orphan pull or reaches a
//!     state in which it would pull nothing.
//! (2) `pull_ping_pong_ends`: the head-of-queue thread is not pulled back and forth between idle cpus forever: from some
//!     index on, no rebalance pull moves `t`.
//! (3) `killed_threads_leave_queues` and `killed_running_lost`: kills complete; a killed thread does not stay in a run queue
//!     forever, and a cpu whose running thread or process is killed eventually loses it.
//! (4) `container_eventually_served_forever`: `t`'s container eventually has an online cpu it owns that stays online and
//!     owned from then on.
//! (5) `shard_service_lost_finitely`: the cpu of the shard `t` waits on goes Off or leaves `t`'s container only finitely
//!     often while `t` waits on that shard. This one is not among the hypotheses the design names; without it the
//!     statement is false in U (see the report: a shard cpu that comes online and goes Off again between its own ticks,
//!     while the orphan pulls of the other cpus always fall into its online phases).
//! The start state satisfies the run-queue invariant and carries no `kill_container` mark (no cpu and no cpu set marked);
//! `kill_container` is not a world syscall, and no world step sets or clears these marks.
use vstd::prelude::*;
use crate::*;
use crate::temporal::*;
use crate::run_queue::*;
use crate::run_steps::*;
use crate::run_measure::*;
use crate::world::*;
use veriflat_syscall_schedule::{rebalance_pull::rebalance_pull_spec::*, syscall_schedule::syscall_schedule_spec::*};

verus! {
/// The scheduler on cpu `c` would switch now: the cpu is online and its `schedule` call would return `Switched` (it is not
/// marked, its running process and thread, if any, are live, and its shard has a live head).
pub open spec fn schedule_wanted(u: KernelU, c: CpuId) -> bool {
    index_valid(NUM_CPUS, c) && !(u.cpu_array[c as int].state is Off) && schedule_syscall_result(u, c) is Switched
}

/// The orphan pull of cpu `c` from cursor `x` would pull now: its `rebalance_orphan_pull` call would return `Pulled`.
pub open spec fn orphan_pull_wanted(u: KernelU, c: CpuId, x: CpuId) -> bool { index_valid(NUM_CPUS, c) && orphan_pull_syscall_result(u, c, x) is Pulled }

/// At `k` cpu `c` takes a Schedule step, or its scheduler would not switch.
pub open spec fn schedule_tick_at(b: Execution<Snap>, c: CpuId, k: nat) -> bool { b(k).cpu == c && b(k).label is Schedule || !schedule_wanted(b(k).u, c) }

/// At `k` cpu `c` takes the orphan pull from cursor `x`, or that orphan pull would pull nothing.
pub open spec fn orphan_tick_at(b: Execution<Snap>, c: CpuId, x: CpuId, k: nat) -> bool {
    b(k).cpu == c && b(k).label == (StepLabel::OrphanPull { cursor: x }) || !orphan_pull_wanted(b(k).u, c, x)
}

pub open spec fn schedule_tick_after(b: Execution<Snap>, c: CpuId, i: nat) -> bool { exists|k: nat| i <= k && #[trigger] schedule_tick_at(b, c, k) }

pub open spec fn orphan_tick_after(b: Execution<Snap>, c: CpuId, x: CpuId, i: nat) -> bool { exists|k: nat| i <= k && #[trigger] orphan_tick_at(b, c, x, k) }

/// Hypothesis (1), TIMER: on every cpu, from every index on, the scheduler eventually switches or would not switch, and
/// for every cursor the orphan pull eventually pulls or would pull nothing.
pub open spec fn timer_ticks_infinitely_often(b: Execution<Snap>) -> bool {
    &&& forall|c: CpuId, i: nat| #![trigger schedule_tick_after(b, c, i)] index_valid(NUM_CPUS, c) ==> schedule_tick_after(b, c, i)
    &&& forall|c: CpuId, x: CpuId, i: nat| #![trigger orphan_tick_after(b, c, x, i)] index_valid(NUM_CPUS, c) && index_valid(NUM_CPUS, x) ==> orphan_tick_after(b, c, x, i)
}

/// The step `s` is a rebalance pull that moves `t`: `t` heads the shard the pulling cpu takes from.
pub open spec fn rebalance_pulls(s: Snap, t: RwLockThreadPtr) -> bool {
    let queues = s.u.container_map[s.u.cpu_array[s.cpu as int].owning_container].scheduler;
    s.label is RebalancePull && queues[first_nonempty_shard(queues, 0, s.cpu)->Some_0 as int][0] == t
}

/// No rebalance pull moves `t` from `i0` on.
pub open spec fn no_rebalance_pull_from(b: Execution<Snap>, t: RwLockThreadPtr, i0: nat) -> bool { forall|k: nat| #![trigger b(k)] i0 <= k ==> !rebalance_pulls(b(k), t) }

/// Hypothesis (2): from some index on, no rebalance pull moves `t`.
pub open spec fn pull_ping_pong_ends(b: Execution<Snap>, t: RwLockThreadPtr) -> bool { exists|i0: nat| #[trigger] no_rebalance_pull_from(b, t, i0) }

/// At some index from `i` on, `x` is not in shard `s` of `c`.
pub open spec fn leaves_shard_after(b: Execution<Snap>, c: RwLockContainerPtr, s: CpuId, x: RwLockThreadPtr, i: nat) -> bool {
    exists|k: nat| i <= k && !(#[trigger] b(k).u.container_map[c].scheduler[s as int].contains(x))
}

/// Hypothesis (3a): a killed thread in a run queue eventually leaves it.
pub open spec fn killed_threads_leave_queues(b: Execution<Snap>) -> bool {
    forall|c: RwLockContainerPtr, s: CpuId, x: RwLockThreadPtr, i: nat| #![trigger leaves_shard_after(b, c, s, x, i)]
        index_valid(NUM_CPUS, s) && b(i).u.container_map.dom().contains(c) && b(i).u.container_map[c].scheduler[s as int].contains(x) && b(i).u.thread_map[x].killed
        ==> leaves_shard_after(b, c, s, x, i)
}

/// The running process of cpu `c`, or its running thread, is killed (the case in which `schedule` does not switch).
pub open spec fn running_killed(u: KernelU, c: CpuId) -> bool {
    let cpu = u.cpu_array[c as int];
    cpu.current_process is Some && (u.process_map[cpu.current_process->Some_0].killed || u.thread_map[cpu.current_thread->Some_0].killed)
}

/// At some index from `i` on, cpu `c` no longer runs the thread and process it runs at `i`.
pub open spec fn running_lost_after(b: Execution<Snap>, c: CpuId, i: nat) -> bool {
    exists|k: nat| i <= k && (#[trigger] b(k).u.cpu_array[c as int].current_thread != b(i).u.cpu_array[c as int].current_thread
        || b(k).u.cpu_array[c as int].current_process != b(i).u.cpu_array[c as int].current_process)
}

/// Hypothesis (3b): a cpu whose running thread or process is killed eventually loses it.
pub open spec fn killed_running_lost(b: Execution<Snap>) -> bool {
    forall|c: CpuId, i: nat| #![trigger running_lost_after(b, c, i)] index_valid(NUM_CPUS, c) && running_killed(b(i).u, c) ==> running_lost_after(b, c, i)
}

/// Cpu `a` serves `ctn` (is owned by it and not Off) at every index from `i0` on.
pub open spec fn serves_from(b: Execution<Snap>, ctn: RwLockContainerPtr, a: CpuId, i0: nat) -> bool {
    index_valid(NUM_CPUS, a) && forall|k: nat| #![trigger b(k)] i0 <= k ==> cpu_serves_container(b(k).u, ctn, a)
}

/// Hypothesis (4): container `ctn` eventually has a cpu that serves it from then on.
pub open spec fn container_eventually_served_forever(b: Execution<Snap>, ctn: RwLockContainerPtr) -> bool { exists|a: CpuId, i0: nat| #[trigger] serves_from(b, ctn, a, i0) }

/// From `i0` on, while `t` waits on one shard, a cpu that serves `t`'s container on that shard keeps serving it.
pub open spec fn shard_service_kept_from(b: Execution<Snap>, t: RwLockThreadPtr, i0: nat) -> bool {
    forall|k: nat| #![trigger b(k)]
        i0 <= k && waiting(b(k).u, t) && waiting(b(k + 1).u, t) && shard_of(b(k + 1).u, t) == shard_of(b(k).u, t)
            && cpu_serves_container(b(k).u, ctn_of(b(k).u, t), shard_of(b(k).u, t))
        ==> cpu_serves_container(b(k + 1).u, ctn_of(b(k).u, t), shard_of(b(k).u, t))
}

/// Hypothesis (5): the cpu of the shard `t` waits on stops serving `t`'s container only finitely often while `t` waits on
/// that shard.
pub open spec fn shard_service_lost_finitely(b: Execution<Snap>, t: RwLockThreadPtr) -> bool { exists|i0: nat| #[trigger] shard_service_kept_from(b, t, i0) }

/// No cpu and no cpu set carries a `kill_container` mark.
pub open spec fn no_kill_container_marks(u: KernelU) -> bool {
    &&& forall|c: CpuId| #![trigger u.cpu_array[c as int]] index_valid(NUM_CPUS, c) ==> !u.cpu_array[c as int].killed
    &&& forall|ctn: RwLockContainerPtr| #![trigger u.container_map[ctn]] u.container_map.dom().contains(ctn) ==> !u.container_map[ctn].cpu_set_killed
}

/// `t` runs, or is killed or gone.
pub open spec fn runs_or_gone(t: RwLockThreadPtr) -> StatePred<Snap> { |s: Snap| running(s.u, t) || gone(s.u, t) }

/// Both the run-queue invariant and the absence of marks at the start hold at every index.
proof fn world_behavior_implies_start_facts_kept(b: Execution<Snap>, k: nat)
    requires world_behavior(b), queue_inv(b(0).u), no_kill_container_marks(b(0).u),
    ensures queue_inv(b(k).u), no_kill_container_marks(b(k).u),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        world_behavior_implies_start_facts_kept(b, j);
        assert(world_step(b(j), b(j + 1)));
        world_step_implies_run_step(b(j).u, b(k).u, b(j).label, b(j).cpu, arbitrary());
        let u = b(j).u;
        let u2 = b(k).u;
        assert forall|c: CpuId| #![trigger u2.cpu_array[c as int]] index_valid(NUM_CPUS, c) implies !u2.cpu_array[c as int].killed by { assert(!u.cpu_array[c as int].killed); };
        assert forall|ctn: RwLockContainerPtr| #![trigger u2.container_map[ctn]] u2.container_map.dom().contains(ctn) implies !u2.container_map[ctn].cpu_set_killed by {
            assert(u.container_map.dom().contains(ctn));
            assert(!u.container_map[ctn].cpu_set_killed);
        };
    }
}

/// The standing facts of the proof by contradiction: from `m` on, `t` waits in container `c` with the run-queue invariant and
/// without marks, no rebalance pull moves `t`, a shard of `t` that is served stays served while `t` stays on it, and cpu `a`
/// serves `c`.
pub open spec fn stuck_ctx(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat) -> bool {
    &&& world_behavior(b) && index_valid(NUM_CPUS, a)
    &&& timer_ticks_infinitely_often(b) && killed_threads_leave_queues(b) && killed_running_lost(b)
    &&& forall|k: nat| #![trigger b(k)] m <= k ==> waiting(b(k).u, t) && ctn_of(b(k).u, t) == c && queue_inv(b(k).u) && no_kill_container_marks(b(k).u)
        && !rebalance_pulls(b(k), t) && cpu_serves_container(b(k).u, c, a)
    &&& forall|k: nat| #![trigger b(k)] m <= k && shard_of(b(k + 1).u, t) == shard_of(b(k).u, t) && cpu_serves_container(b(k).u, c, shard_of(b(k).u, t))
        ==> cpu_serves_container(b(k + 1).u, c, shard_of(b(k).u, t))
}

/// `t` stays on shard `s` at every index of `k0..=k`.
pub open spec fn on_shard(b: Execution<Snap>, t: RwLockThreadPtr, s: CpuId, k0: nat, k: nat) -> bool { forall|j: nat| #![trigger b(j)] k0 <= j <= k ==> shard_of(b(j).u, t) == s }

/// Two queues in which `t` first occurs at the same position with the same threads in front have the same head.
proof fn same_front_implies_same_head(q1: Seq<RwLockThreadPtr>, q2: Seq<RwLockThreadPtr>, t: RwLockThreadPtr)
    requires q1.contains(t), q2.contains(t), seq_pos(q2, t) == seq_pos(q1, t), q2.take(seq_pos(q1, t) as int) == q1.take(seq_pos(q1, t) as int),
    ensures q2.len() > 0, q2[0] == q1[0],
{
    contains_implies_seq_pos_facts(q1, t);
    contains_implies_seq_pos_facts(q2, t);
    let p = seq_pos(q1, t) as int;
    if p > 0 { assert(q2.take(p)[0] == q1.take(p)[0]); }
}

/// While `t` stays on its shard, its position does not grow, and does not move unless a thread in front leaves.
proof fn stuck_on_shard_implies_pos_kept(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat, k0: nat, k: nat)
    requires stuck_ctx(b, t, c, a, m), m <= k0 <= k, on_shard(b, t, shard_of(b(k0).u, t), k0, k),
    ensures
        pos(b(k).u, t) <= pos(b(k0).u, t),
        pos(b(k).u, t) == pos(b(k0).u, t) ==> queue_of(b(k).u, t).len() > 0 && queue_of(b(k).u, t)[0] == queue_of(b(k0).u, t)[0],
{
    let u0 = b(k0).u;
    let u = b(k).u;
    assert(waits_on_one_shard(b, t, k0, k)) by {
        assert forall|j: nat| #![trigger b(j)] k0 <= j <= k implies waiting(b(j).u, t) && shard_of(b(j).u, t) == shard_of(b(k0).u, t) by { assert(m <= j); };
    };
    assert(queue_inv(u0) && queue_inv(u) && waiting(u0, t) && waiting(u, t));
    waiting_stretch_implies_head_pops_bounded(b, t, k0, k);
    queue_inv_implies_queued(u, t);
    queue_inv_implies_queued(u0, t);
    if pos(u, t) == pos(u0, t) { same_front_implies_same_head(queue_of(u0, t), queue_of(u, t), t); }
}

/// While `t` stays on its shard, a cpu serving that shard keeps serving it.
proof fn stuck_on_shard_implies_served_kept(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat, k0: nat, k: nat)
    requires stuck_ctx(b, t, c, a, m), m <= k0 <= k, on_shard(b, t, shard_of(b(k0).u, t), k0, k), cpu_serves_container(b(k0).u, c, shard_of(b(k0).u, t)),
    ensures cpu_serves_container(b(k).u, c, shard_of(b(k0).u, t)),
    decreases k - k0,
{
    if k > k0 {
        let j = (k - 1) as nat;
        assert(on_shard(b, t, shard_of(b(k0).u, t), k0, j)) by { assert forall|i: nat| #![trigger b(i)] k0 <= i <= j implies shard_of(b(i).u, t) == shard_of(b(k0).u, t) by { assert(b(i) == b(i)); }; };
        stuck_on_shard_implies_served_kept(b, t, c, a, m, k0, j);
        assert(b(j) == b(j) && b(j + 1) == b(k));
    }
}

/// Without a Schedule of cpu `x` at `k..k2`, the cpu keeps its running thread and process or has dropped both.
proof fn no_schedule_implies_running_kept_or_dropped(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat, x: CpuId, k: nat, k2: nat)
    requires
        stuck_ctx(b, t, c, a, m), m <= k <= k2, index_valid(NUM_CPUS, x),
        forall|j: nat| #![trigger b(j)] k <= j < k2 ==> !(b(j).label is Schedule && b(j).cpu == x),
    ensures
        b(k2).u.cpu_array[x as int].current_thread == b(k).u.cpu_array[x as int].current_thread && b(k2).u.cpu_array[x as int].current_process == b(k).u.cpu_array[x as int].current_process
            || b(k2).u.cpu_array[x as int].current_thread is None && b(k2).u.cpu_array[x as int].current_process is None,
    decreases k2 - k,
{
    if k2 > k {
        let j = (k2 - 1) as nat;
        no_schedule_implies_running_kept_or_dropped(b, t, c, a, m, x, k, j);
        assert(b(j) == b(j) && b(j + 1) == b(k2));
        world_behavior_implies_waiting_step(b, t, j);
        assert(b(k2).u.cpu_array[x as int] == b(k2).u.cpu_array[x as int]);
    }
}

/// An orphan shard other than the cpu's own is the victim of an orphan pull whose cursor names it.
proof fn orphan_shard_implies_victim(u: KernelU, c: RwLockContainerPtr, s: CpuId, own: CpuId)
    requires index_valid(NUM_CPUS, s), s != own, !cpu_serves_container(u, c, s),
    ensures orphan_victim(u, c, s, own) == Some(s),
{ reveal_with_fuel(first_orphan_shard, 2); }

/// While `t` waits forever on one shard, its position drops: the shard's head pops, by a Schedule of a serving cpu or by
/// an orphan pull of cpu `a`.
proof fn stuck_on_shard_implies_pos_drops(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat, k0: nat) -> (k1: nat)
    requires stuck_ctx(b, t, c, a, m), m <= k0, forall|k: nat| #![trigger b(k)] k0 <= k ==> shard_of(b(k).u, t) == shard_of(b(k0).u, t),
    ensures k0 < k1, pos(b(k1).u, t) < pos(b(k0).u, t),
{
    let s0 = shard_of(b(k0).u, t);
    let p = pos(b(k0).u, t);
    if exists|k: nat| k0 <= k && #[trigger] pos(b(k).u, t) < p {
        let k = choose|k: nat| k0 <= k && #[trigger] pos(b(k).u, t) < p;
        return k;
    }
    assert(b(k0) == b(k0));
    let h0 = queue_of(b(k0).u, t)[0];
    // Every later index keeps `t` on `s0` at position `p`, with `h0` at the head.
    assert forall|k: nat| #![trigger b(k)] k0 <= k implies on_shard(b, t, s0, k0, k) by {
        assert forall|j: nat| #![trigger b(j)] k0 <= j <= k implies shard_of(b(j).u, t) == s0 by { assert(b(j) == b(j)); };
    };
    assert forall|k: nat| #![trigger b(k)] k0 <= k implies pos(b(k).u, t) == p && queue_of(b(k).u, t).len() > 0 && queue_of(b(k).u, t)[0] == h0
        && queued(b(k).u, t) && shard_of(b(k).u, t) == s0 by {
        assert(on_shard(b, t, s0, k0, k));
        stuck_on_shard_implies_pos_kept(b, t, c, a, m, k0, k);
        assert(!(pos(b(k).u, t) < p));
        queue_inv_implies_queued(b(k).u, t);
    };
    // No step pops the head of `s0`.
    assert forall|k: nat| #![trigger b(k)] k0 <= k implies !pops_at(b, k, c, s0) by {
        if pops_at(b, k, c, s0) {
            world_behavior_implies_waiting_step(b, t, k);
            assert(b(k + 1) == b(k + 1));
            assert(pos(b(k + 1).u, t) == p);
        }
    };
    // The head is never killed.
    assert forall|k: nat| #![trigger b(k)] k0 <= k implies !b(k).u.thread_map[h0].killed by {
        if b(k).u.thread_map[h0].killed {
            assert(queue_of(b(k).u, t)[0] == h0 && queue_of(b(k).u, t).contains(h0));
            assert(leaves_shard_after(b, c, s0, h0, k));
            let k2 = choose|k2: nat| k <= k2 && !(#[trigger] b(k2).u.container_map[c].scheduler[s0 as int].contains(h0));
            assert(b(k2) == b(k2));
            assert(queue_of(b(k2).u, t)[0] == h0 && queue_of(b(k2).u, t).len() > 0);
            assert(queue_of(b(k2).u, t).contains(h0));
        }
    };
    if exists|k: nat| k0 <= k && #[trigger] cpu_serves_container(b(k).u, c, s0) {
        // Served: the scheduler of `s0` would switch unless its running thread or process is killed, but it never pops the head.
        let ks = choose|k: nat| k0 <= k && #[trigger] cpu_serves_container(b(k).u, c, s0);
        assert(b(ks) == b(ks));
        assert forall|k: nat| #![trigger b(k)] ks <= k implies cpu_serves_container(b(k).u, c, s0) && !(b(k).label is Schedule && b(k).cpu == s0) by {
            assert(on_shard(b, t, s0, ks, k)) by { assert forall|j: nat| #![trigger b(j)] ks <= j <= k implies shard_of(b(j).u, t) == s0 by { assert(b(j) == b(j)); }; };
            stuck_on_shard_implies_served_kept(b, t, c, a, m, ks, k);
            if b(k).label is Schedule && b(k).cpu == s0 { assert(pops_at(b, k, c, s0)); }
        };
        assert forall|k: nat| #![trigger b(k)] ks <= k && !running_killed(b(k).u, s0) implies schedule_wanted(b(k).u, s0) by {
            assert(!b(k).u.cpu_array[s0 as int].killed);
            assert(shard_queue(b(k).u, c, s0) == queue_of(b(k).u, t));
        };
        assert(index_valid(NUM_CPUS, s0));
        assert(schedule_tick_after(b, s0, ks));
        let k1 = choose|k1: nat| ks <= k1 && #[trigger] schedule_tick_at(b, s0, k1);
        assert(b(k1) == b(k1));
        assert(running_killed(b(k1).u, s0));
        assert(running_lost_after(b, s0, k1));
        let k2 = choose|k2: nat| k1 <= k2 && (#[trigger] b(k2).u.cpu_array[s0 as int].current_thread != b(k1).u.cpu_array[s0 as int].current_thread
            || b(k2).u.cpu_array[s0 as int].current_process != b(k1).u.cpu_array[s0 as int].current_process);
        assert forall|j: nat| #![trigger b(j)] k1 <= j < k2 implies !(b(j).label is Schedule && b(j).cpu == s0) by { assert(b(j) == b(j)); };
        no_schedule_implies_running_kept_or_dropped(b, t, c, a, m, s0, k1, k2);
        assert(schedule_tick_after(b, s0, k2));
        let k3 = choose|k3: nat| k2 <= k3 && #[trigger] schedule_tick_at(b, s0, k3);
        assert(b(k3) == b(k3) && b(k2) == b(k2));
        assert forall|j: nat| #![trigger b(j)] k2 <= j < k3 implies !(b(j).label is Schedule && b(j).cpu == s0) by { assert(b(j) == b(j)); };
        no_schedule_implies_running_kept_or_dropped(b, t, c, a, m, s0, k2, k3);
        assert(!running_killed(b(k3).u, s0));
        assert(false);
    } else {
        // Orphan forever: cpu `a` would pull the head of `s0` with cursor `s0`, but it never pops the head.
        assert(b(k0) == b(k0));
        assert(cpu_serves_container(b(k0).u, c, a) && !cpu_serves_container(b(k0).u, c, s0));
        assert(index_valid(NUM_CPUS, s0) && s0 != a);
        assert(orphan_tick_after(b, a, s0, k0));
        let k1 = choose|k1: nat| k0 <= k1 && #[trigger] orphan_tick_at(b, a, s0, k1);
        assert(b(k1) == b(k1));
        let u = b(k1).u;
        assert(!cpu_serves_container(u, c, s0));
        orphan_shard_implies_victim(u, c, s0, a);
        assert(shard_queue(u, c, s0) == queue_of(u, t));
        assert(!u.cpu_array[a as int].killed && !u.container_map[c].cpu_set_killed);
        if b(k1).cpu == a && b(k1).label == (StepLabel::OrphanPull { cursor: s0 }) { assert(pops_at(b, k1, c, s0)); }
        assert(orphan_pull_wanted(u, a, s0));
        assert(false);
    }
    arbitrary()
}

/// `t` cannot wait forever on one shard: its position would drop forever.
proof fn stuck_on_shard_forever_impossible(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat, k0: nat)
    requires stuck_ctx(b, t, c, a, m), m <= k0, forall|k: nat| #![trigger b(k)] k0 <= k ==> shard_of(b(k).u, t) == shard_of(b(k0).u, t),
    ensures false,
    decreases pos(b(k0).u, t),
{
    let k1 = stuck_on_shard_implies_pos_drops(b, t, c, a, m, k0);
    assert(b(k1) == b(k1));
    stuck_on_shard_forever_impossible(b, t, c, a, m, k1);
}

/// The first index after `k0` at which `t` is off shard `s`, given one.
proof fn first_shard_change(b: Execution<Snap>, t: RwLockThreadPtr, s: CpuId, k0: nat, k: nat) -> (j: nat)
    requires k0 <= k, shard_of(b(k0).u, t) == s, shard_of(b(k).u, t) != s,
    ensures k0 < j <= k, shard_of(b(j).u, t) != s, on_shard(b, t, s, k0, (j - 1) as nat),
    decreases k - k0,
{
    if shard_of(b(k0 + 1).u, t) != s {
        assert(on_shard(b, t, s, k0, k0)) by { assert forall|i: nat| #![trigger b(i)] k0 <= i <= k0 implies shard_of(b(i).u, t) == s by { assert(i == k0); }; };
        k0 + 1
    } else {
        let j = first_shard_change(b, t, s, k0 + 1, k);
        assert(on_shard(b, t, s, k0, (j - 1) as nat)) by {
            assert forall|i: nat| #![trigger b(i)] k0 <= i <= (j - 1) as nat implies shard_of(b(i).u, t) == s by { if i > k0 { assert(b(i) == b(i)); } };
        };
        j
    }
}

/// A step that moves the stuck `t` off its shard is an orphan pull from a shard its cpu does not serve, onto a shard whose
/// cpu serves `t`'s container after the step.
proof fn stuck_move_is_orphan_pull(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat, k: nat)
    requires stuck_ctx(b, t, c, a, m), m <= k, shard_of(b(k + 1).u, t) != shard_of(b(k).u, t),
    ensures !cpu_serves_container(b(k).u, c, shard_of(b(k).u, t)), cpu_serves_container(b(k + 1).u, c, shard_of(b(k + 1).u, t)),
{
    assert(b(k) == b(k) && b(k + 1) == b(k + 1));
    world_behavior_implies_waiting_step(b, t, k);
    if b(k).label is RebalancePull {
        queue_inv_implies_queued(b(k).u, t);
        contains_implies_seq_pos_facts(queue_of(b(k).u, t), t);
        assert(rebalance_pulls(b(k), t));
    }
}

/// `t` cannot wait forever from `m`: it would stay on some shard forever, or leave a served shard by an orphan pull.
proof fn stuck_forever_impossible(b: Execution<Snap>, t: RwLockThreadPtr, c: RwLockContainerPtr, a: CpuId, m: nat)
    requires stuck_ctx(b, t, c, a, m),
    ensures false,
{
    let s0 = shard_of(b(m).u, t);
    if !exists|k: nat| m <= k && #[trigger] shard_of(b(k).u, t) != s0 { stuck_on_shard_forever_impossible(b, t, c, a, m, m); }
    let k = choose|k: nat| m <= k && #[trigger] shard_of(b(k).u, t) != s0;
    let j1 = first_shard_change(b, t, s0, m, k);
    stuck_move_is_orphan_pull(b, t, c, a, m, (j1 - 1) as nat);
    let s1 = shard_of(b(j1).u, t);
    assert(cpu_serves_container(b(j1).u, c, s1));
    if !exists|k: nat| j1 <= k && #[trigger] shard_of(b(k).u, t) != s1 { stuck_on_shard_forever_impossible(b, t, c, a, m, j1); }
    let k2 = choose|k2: nat| j1 <= k2 && #[trigger] shard_of(b(k2).u, t) != s1;
    let j2 = first_shard_change(b, t, s1, j1, k2);
    stuck_on_shard_implies_served_kept(b, t, c, a, m, j1, (j2 - 1) as nat);
    stuck_move_is_orphan_pull(b, t, c, a, m, (j2 - 1) as nat);
    assert(b((j2 - 1) as nat) == b((j2 - 1) as nat));
}

/// While `t` waits from `i` to `k`, it stays in its container.
proof fn waiting_implies_ctn_kept(b: Execution<Snap>, t: RwLockThreadPtr, i: nat, k: nat)
    requires world_behavior(b), queue_inv(b(0).u), no_kill_container_marks(b(0).u), i <= k, forall|j: nat| #![trigger b(j)] i <= j <= k ==> waiting(b(j).u, t),
    ensures ctn_of(b(k).u, t) == ctn_of(b(i).u, t),
    decreases k - i,
{
    if k > i {
        let j = (k - 1) as nat;
        waiting_implies_ctn_kept(b, t, i, j);
        world_behavior_implies_start_facts_kept(b, j);
        assert(b(j) == b(j) && b(j + 1) == b(k));
        world_behavior_implies_waiting_step(b, t, j);
    }
}

/// The first index after `i` at which `t` does not wait, given one.
proof fn first_not_waiting(b: Execution<Snap>, t: RwLockThreadPtr, i: nat, k: nat) -> (j: nat)
    requires i <= k, waiting(b(i).u, t), !waiting(b(k).u, t),
    ensures i < j <= k, waiting(b((j - 1) as nat).u, t), !waiting(b(j).u, t),
    decreases k - i,
{ if !waiting(b(i + 1).u, t) { i + 1 } else { first_not_waiting(b, t, i + 1, k) } }

/// Part B: in a world behaviour from a state with the run-queue invariant and no `kill_container` mark, under hypotheses
/// (1) to (5), a thread that is not blocked at `i` eventually runs, or is killed or gone.
pub proof fn fair_world_implies_unblocked_thread_eventually_runs(b: Execution<Snap>, t: RwLockThreadPtr, i: nat)
    requires
        world_behavior(b), queue_inv(b(0).u), no_kill_container_marks(b(0).u), unblocked(b(i).u, t),
        timer_ticks_infinitely_often(b), pull_ping_pong_ends(b, t), killed_threads_leave_queues(b), killed_running_lost(b),
        container_eventually_served_forever(b, b(i).u.thread_map[t].owning_container), shard_service_lost_finitely(b, t),
    ensures eventually(lift_state(runs_or_gone(t)))(b, i),
{
    if runs_or_gone(t)(b(i)) { assert(lift_state(runs_or_gone(t))(b, i)); return; }
    assert(waiting(b(i).u, t));
    if exists|k: nat| i <= k && !(#[trigger] waiting(b(k).u, t)) {
        let k = choose|k: nat| i <= k && !(#[trigger] waiting(b(k).u, t));
        let j = first_not_waiting(b, t, i, k);
        world_behavior_implies_start_facts_kept(b, (j - 1) as nat);
        world_behavior_implies_waiting_step(b, t, (j - 1) as nat);
        assert(b(j) == b(((j - 1) as nat) + 1));
        assert(lift_state(runs_or_gone(t))(b, j));
        return;
    }
    let c = ctn_of(b(i).u, t);
    let i1 = choose|i0: nat| #[trigger] no_rebalance_pull_from(b, t, i0);
    let i2 = choose|i0: nat| #[trigger] shard_service_kept_from(b, t, i0);
    let (a, i3) = choose|a: CpuId, i0: nat| #[trigger] serves_from(b, c, a, i0);
    let m = i + i1 + i2 + i3;
    assert forall|k: nat| #![trigger b(k)] m <= k implies waiting(b(k).u, t) && ctn_of(b(k).u, t) == c && queue_inv(b(k).u) && no_kill_container_marks(b(k).u)
        && !rebalance_pulls(b(k), t) && cpu_serves_container(b(k).u, c, a) by {
        assert forall|j: nat| #![trigger b(j)] i <= j <= k implies waiting(b(j).u, t) by { assert(!!waiting(b(j).u, t)); };
        waiting_implies_ctn_kept(b, t, i, k);
        world_behavior_implies_start_facts_kept(b, k);
    };
    assert forall|k: nat| #![trigger b(k)] m <= k && shard_of(b(k + 1).u, t) == shard_of(b(k).u, t) && cpu_serves_container(b(k).u, c, shard_of(b(k).u, t))
        implies cpu_serves_container(b(k + 1).u, c, shard_of(b(k).u, t)) by {
        assert(b(k + 1) == b(k + 1));
        assert(waiting(b(k).u, t) && waiting(b(k + 1).u, t) && ctn_of(b(k).u, t) == c);
    };
    assert(stuck_ctx(b, t, c, a, m));
    stuck_forever_impossible(b, t, c, a, m);
}
} // verus!

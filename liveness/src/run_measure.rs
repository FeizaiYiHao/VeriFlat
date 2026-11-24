//! Part A, without fairness: the run queues are FIFO. Over a stretch of a world behaviour in which `t` waits on one shard,
//! every step that pops the head of that shard (a Schedule of the shard's cpu while that cpu belongs to `t`'s container,
//! or a pull or orphan pull from that shard) lowers `t`'s position by one and nothing raises it
//! (`waiting_stretch_implies_head_pops_bounded`, and its Schedule-only form
//! `waiting_stretch_implies_served_schedules_bounded`); a Schedule of the shard's cpu with `t` at the head runs `t`
//! (`served_schedule_at_head_implies_running`); `t` leaves waiting only to run or to be killed or gone
//! (`waiting_thread_leaves_only_running_or_gone`); and `t` changes shard only from the head, by a pull or orphan pull, onto
//! a shard whose cpu serves its container (`waiting_thread_changes_shard_only_by_pull`). On a shard whose cpu does not serve
//! the container no Schedule pops the head (`orphan_shard_implies_no_served_schedule`), so there the head pops are pulls.
//! The measure of a waiting thread is therefore its position in its current shard, in two phases: on an orphan shard it
//! falls with each pull from that shard until an orphan pull takes `t` from the head to the tail of the puller's served
//! shard, at a position at most that shard's old length; on a served shard it falls with each Schedule of the shard's cpu
//! (and each pull from it) until that cpu runs `t`, or an idle cpu's pull takes `t` from the head to the head of its own
//! empty shard.
use vstd::prelude::*;
use crate::*;
use crate::run_queue::*;
use crate::run_steps::*;
use crate::world::*;
use veriflat_syscall_schedule::syscall_schedule::syscall_schedule_spec::*;

verus! {
/// The step at `k` pops the head of shard `s` of container `c`.
pub open spec fn pops_at(b: Execution<Snap>, k: nat, c: RwLockContainerPtr, s: CpuId) -> bool { pops_head(b(k).u, b(k).label, b(k).cpu, c, s) }

/// The step at `k` is a Schedule of cpu `s` while `s` is owned by container `c`: it serves shard `s` of `c`.
pub open spec fn served_at(b: Execution<Snap>, k: nat, c: RwLockContainerPtr, s: CpuId) -> bool {
    b(k).label is Schedule && b(k).cpu == s && b(k).u.cpu_array[s as int].owning_container == c
}

/// The number of steps at `i..j` that pop the head of shard `s` of `c`.
pub open spec fn head_pops(b: Execution<Snap>, c: RwLockContainerPtr, s: CpuId, i: nat, j: nat) -> nat
    decreases j - i,
{
    if j <= i { 0 } else { head_pops(b, c, s, i, (j - 1) as nat) + if pops_at(b, (j - 1) as nat, c, s) { 1nat } else { 0nat } }
}

/// The number of steps at `i..j` that serve shard `s` of `c`.
pub open spec fn served_count(b: Execution<Snap>, c: RwLockContainerPtr, s: CpuId, i: nat, j: nat) -> nat
    decreases j - i,
{
    if j <= i { 0 } else { served_count(b, c, s, i, (j - 1) as nat) + if served_at(b, (j - 1) as nat, c, s) { 1nat } else { 0nat } }
}

/// The Schedule steps at `i..j` that serve the shard `t` waits in at `i`.
pub open spec fn served_schedules(b: Execution<Snap>, t: RwLockThreadPtr, i: nat, j: nat) -> nat { served_count(b, ctn_of(b(i).u, t), shard_of(b(i).u, t), i, j) }

/// `t` waits at every index of `i..=j`, always on the shard it waits on at `i`.
pub open spec fn waits_on_one_shard(b: Execution<Snap>, t: RwLockThreadPtr, i: nat, j: nat) -> bool {
    forall|k: nat| #![trigger b(k)] i <= k <= j ==> waiting(b(k).u, t) && shard_of(b(k).u, t) == shard_of(b(i).u, t)
}

/// The run-queue invariant at `i` holds at every later index of a world behaviour.
pub proof fn world_behavior_implies_queue_inv_kept(b: Execution<Snap>, i: nat, k: nat)
    requires world_behavior(b), i <= k, queue_inv(b(i).u),
    ensures queue_inv(b(k).u),
    decreases k - i,
{
    if k > i {
        let j = (k - 1) as nat;
        world_behavior_implies_queue_inv_kept(b, i, j);
        assert(world_step(b(j), b(j + 1)));
        world_step_implies_run_step(b(j).u, b(k).u, b(j).label, b(j).cpu, arbitrary());
    }
}

/// One world step of a behaviour does to a waiting thread what `waiting_step` says.
pub proof fn world_behavior_implies_waiting_step(b: Execution<Snap>, t: RwLockThreadPtr, k: nat)
    requires world_behavior(b), queue_inv(b(k).u), waiting(b(k).u, t),
    ensures waiting_step(b(k).u, b(k + 1).u, b(k).label, b(k).cpu, t), queue_inv(b(k + 1).u), cpu_frame(b(k).u, b(k + 1).u, b(k).label, b(k).cpu),
{
    assert(world_step(b(k), b(k + 1)));
    world_step_implies_run_step(b(k).u, b(k + 1).u, b(k).label, b(k).cpu, t);
}

/// Part A, the measure: over a stretch in which `t` waits on one shard, the head pops of that shard plus `t`'s final
/// position are at most its first position; if the position did not fall, the same threads stand in front of `t`.
pub proof fn waiting_stretch_implies_head_pops_bounded(b: Execution<Snap>, t: RwLockThreadPtr, i: nat, j: nat)
    requires world_behavior(b), queue_inv(b(i).u), i <= j, waits_on_one_shard(b, t, i, j),
    ensures
        ctn_of(b(j).u, t) == ctn_of(b(i).u, t),
        head_pops(b, ctn_of(b(i).u, t), shard_of(b(i).u, t), i, j) + pos(b(j).u, t) <= pos(b(i).u, t),
        pos(b(j).u, t) == pos(b(i).u, t) ==> queue_of(b(j).u, t).take(pos(b(i).u, t) as int) == queue_of(b(i).u, t).take(pos(b(i).u, t) as int),
    decreases j - i,
{
    if j > i {
        let k = (j - 1) as nat;
        assert(waits_on_one_shard(b, t, i, k)) by { assert forall|m: nat| #![trigger b(m)] i <= m <= k implies waiting(b(m).u, t) && shard_of(b(m).u, t) == shard_of(b(i).u, t) by { assert(b(m) == b(m)); }; };
        waiting_stretch_implies_head_pops_bounded(b, t, i, k);
        assert(b(k) == b(k) && b(j) == b(j));
        world_behavior_implies_queue_inv_kept(b, i, k);
        world_behavior_implies_waiting_step(b, t, k);
        assert(k + 1 == j);
    }
}

/// A Schedule that serves a shard pops its head.
proof fn served_at_implies_pops_at(b: Execution<Snap>, k: nat, c: RwLockContainerPtr, s: CpuId)
    requires served_at(b, k, c, s),
    ensures pops_at(b, k, c, s),
{}

pub proof fn served_count_implies_at_most_head_pops(b: Execution<Snap>, c: RwLockContainerPtr, s: CpuId, i: nat, j: nat)
    ensures served_count(b, c, s, i, j) <= head_pops(b, c, s, i, j),
    decreases j - i,
{
    if j > i {
        served_count_implies_at_most_head_pops(b, c, s, i, (j - 1) as nat);
        if served_at(b, (j - 1) as nat, c, s) { served_at_implies_pops_at(b, (j - 1) as nat, c, s); }
    }
}

/// Part A in the form of the design: over a stretch in which `t` waits on one shard, the Schedule steps serving that shard
/// plus `t`'s final position are at most its first position.
pub proof fn waiting_stretch_implies_served_schedules_bounded(b: Execution<Snap>, t: RwLockThreadPtr, i: nat, j: nat)
    requires world_behavior(b), queue_inv(b(0).u), i <= j, waits_on_one_shard(b, t, i, j),
    ensures served_schedules(b, t, i, j) + pos(b(j).u, t) <= pos(b(i).u, t),
{
    world_behavior_implies_queue_inv_kept(b, 0, i);
    waiting_stretch_implies_head_pops_bounded(b, t, i, j);
    served_count_implies_at_most_head_pops(b, ctn_of(b(i).u, t), shard_of(b(i).u, t), i, j);
}

/// Part A, the head: a Schedule serving the shard of a waiting `t` that stands at its head runs `t` on that shard's cpu.
pub proof fn served_schedule_at_head_implies_running(b: Execution<Snap>, t: RwLockThreadPtr, k: nat)
    requires world_behavior(b), queue_inv(b(0).u), waiting(b(k).u, t), pos(b(k).u, t) == 0, served_at(b, k, ctn_of(b(k).u, t), shard_of(b(k).u, t)),
    ensures running(b(k + 1).u, t), b(k + 1).u.thread_map[t].state == (ThreadState::RUNNING { cpu_id: shard_of(b(k).u, t) }),
{
    world_behavior_implies_queue_inv_kept(b, 0, k);
    world_behavior_implies_waiting_step(b, t, k);
}

/// Part A, leaving: a waiting thread stops waiting only to run, or killed, or gone.
pub proof fn waiting_thread_leaves_only_running_or_gone(b: Execution<Snap>, t: RwLockThreadPtr, k: nat)
    requires world_behavior(b), queue_inv(b(0).u), waiting(b(k).u, t), !waiting(b(k + 1).u, t),
    ensures running(b(k + 1).u, t) || gone(b(k + 1).u, t),
{
    world_behavior_implies_queue_inv_kept(b, 0, k);
    world_behavior_implies_waiting_step(b, t, k);
}

/// Part A, moving: a thread that waits before and after a step on different shards was at the head of its shard, and the
/// step is a pull (to the head of an idle cpu's empty shard) or an orphan pull (from a shard whose cpu does not serve the
/// container) of a cpu `d` that serves the container, which puts `t` on shard `d` at a position no greater than that
/// shard's old length; the container is kept.
pub proof fn waiting_thread_changes_shard_only_by_pull(b: Execution<Snap>, t: RwLockThreadPtr, k: nat)
    requires world_behavior(b), queue_inv(b(0).u), waiting(b(k).u, t), waiting(b(k + 1).u, t), shard_of(b(k + 1).u, t) != shard_of(b(k).u, t),
    ensures pulled_step(b(k).u, b(k + 1).u, b(k).label, b(k).cpu, t), ctn_of(b(k + 1).u, t) == ctn_of(b(k).u, t),
{
    world_behavior_implies_queue_inv_kept(b, 0, k);
    world_behavior_implies_waiting_step(b, t, k);
}

/// On a shard whose cpu does not serve the container no Schedule serves the shard: a Schedule needs a cpu that is not Off.
pub proof fn orphan_shard_implies_no_served_schedule(b: Execution<Snap>, k: nat, c: RwLockContainerPtr, s: CpuId)
    requires world_behavior(b), !cpu_serves_container(b(k).u, c, s),
    ensures !served_at(b, k, c, s),
{
    assert(world_step(b(k), b(k + 1)));
    if served_at(b, k, c, s) { reveal(schedule_step_pre); }
}
} // verus!

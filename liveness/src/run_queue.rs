//! Run queues: where a waiting thread stands, and what one world step does to it.
//!
//! A thread `t` waits when it is in the thread map, not killed, and SCHEDULED. It waits in shard `shard_of(u, t)` (the cpu
//! id its state names) of its container's scheduler, and its position `pos(u, t)` is the index of its first occurrence in
//! that shard. `queue_inv` says every waiting thread is in its shard; U's ownership facts do not say so (the kernel's
//! `container_thread_scheduler_wf` does), so the theorems take it at their start and every world step keeps it.
//! `waiting_step` is what one world step does to a waiting thread: it keeps waiting in its container, or it runs, or it
//! is killed or gone; on the same shard its position never grows, and does not move at all unless something in front of
//! it leaves; a step that pops the head of its shard lowers it; a Schedule of the shard's own cpu with `t` at the head
//! runs `t`; and `t` changes shard only from the head, by a pull, onto a shard whose cpu serves its container.
use vstd::prelude::*;
use crate::*;

verus! {
/// `t` waits in a run queue: it exists, is not killed, and is SCHEDULED.
pub open spec fn waiting(u: KernelU, t: RwLockThreadPtr) -> bool { u.thread_map.dom().contains(t) && !u.thread_map[t].killed && u.thread_map[t].state is SCHEDULED }

/// `t` runs on a cpu.
pub open spec fn running(u: KernelU, t: RwLockThreadPtr) -> bool { u.thread_map.dom().contains(t) && u.thread_map[t].state is RUNNING }

/// `t` is killed or no longer exists.
pub open spec fn gone(u: KernelU, t: RwLockThreadPtr) -> bool { !u.thread_map.dom().contains(t) || u.thread_map[t].killed }

/// `t` is not blocked: it exists and is SCHEDULED or RUNNING (blocked = waiting on an endpoint or for a reply, or in IPC
/// transit).
pub open spec fn unblocked(u: KernelU, t: RwLockThreadPtr) -> bool { u.thread_map.dom().contains(t) && (u.thread_map[t].state is SCHEDULED || u.thread_map[t].state is RUNNING) }

/// The shard a SCHEDULED `t` waits in: the cpu id its state names.
pub open spec fn shard_of(u: KernelU, t: RwLockThreadPtr) -> CpuId { u.thread_map[t].state->SCHEDULED_cpu_id }

pub open spec fn ctn_of(u: KernelU, t: RwLockThreadPtr) -> RwLockContainerPtr { u.thread_map[t].owning_container }

/// Shard `s` of container `c`'s scheduler.
pub open spec fn shard_queue(u: KernelU, c: RwLockContainerPtr, s: CpuId) -> Seq<RwLockThreadPtr> { u.container_map[c].scheduler[s as int] }

/// The run queue `t` waits in.
pub open spec fn queue_of(u: KernelU, t: RwLockThreadPtr) -> Seq<RwLockThreadPtr> { shard_queue(u, ctn_of(u, t), shard_of(u, t)) }

/// The index of the first occurrence of `t` in `q`, or `q.len()` when `t` does not occur.
pub open spec fn seq_pos(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr) -> nat {
    match q.index_of_first(t) { Some(i) => i as nat, None => q.len() }
}

/// The position of `t` in its run queue: how many threads stand in front of it.
pub open spec fn pos(u: KernelU, t: RwLockThreadPtr) -> nat { seq_pos(queue_of(u, t), t) }

/// `t` stands in its shard, which is a valid shard of an existing container.
pub open spec fn queued(u: KernelU, t: RwLockThreadPtr) -> bool {
    index_valid(NUM_CPUS, shard_of(u, t)) && u.container_map.dom().contains(ctn_of(u, t)) && queue_of(u, t).contains(t)
}

/// Every scheduler has one shard per cpu, every thread's last cpu is a valid cpu id (the wake shard of a cross-container
/// rendezvous), and every waiting thread stands in its shard.
#[verifier::opaque]
pub open spec fn queue_inv(u: KernelU) -> bool {
    &&& forall|c: RwLockContainerPtr| #![trigger u.container_map[c]] u.container_map.dom().contains(c) ==> u.container_map[c].scheduler.len() == NUM_CPUS
    &&& forall|x: RwLockThreadPtr| #![trigger u.thread_map[x]] u.thread_map.dom().contains(x) ==> index_valid(NUM_CPUS, u.thread_map[x].last_cpu)
    &&& forall|x: RwLockThreadPtr| #![trigger waiting(u, x)] waiting(u, x) ==> queued(u, x)
}

pub proof fn queue_inv_implies_queued(u: KernelU, t: RwLockThreadPtr)
    requires queue_inv(u), waiting(u, t),
    ensures queued(u, t), u.container_map[ctn_of(u, t)].scheduler.len() == NUM_CPUS,
{ reveal(queue_inv); }

/// The step at `d` with label `l` removes the head of shard `s` of container `c`: a Schedule of cpu `s` while `s` is owned by
/// `c`, or a pull or orphan pull of a cpu of `c` whose victim is `s`.
pub open spec fn pops_head(u: KernelU, l: StepLabel, d: CpuId, c: RwLockContainerPtr, s: CpuId) -> bool {
    u.cpu_array[d as int].owning_container == c && match l {
        StepLabel::Schedule { .. } => d == s,
        StepLabel::RebalancePull => first_nonempty_shard(u.container_map[c].scheduler, 0, d) == Some(s),
        StepLabel::OrphanPull { cursor } => orphan_victim(u, c, cursor, d) == Some(s),
        _ => false,
    }
}

/// A step that keeps `t` on its shard: its position never grows, stays only with the same threads in front, and drops when
/// the step pops the head.
pub open spec fn stays_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, t: RwLockThreadPtr) -> bool {
    &&& pos(u2, t) <= pos(u, t)
    &&& pos(u2, t) == pos(u, t) ==> queue_of(u2, t).take(pos(u, t) as int) == queue_of(u, t).take(pos(u, t) as int)
    &&& pops_head(u, l, d, ctn_of(u, t), shard_of(u, t)) ==> pos(u2, t) < pos(u, t)
}

/// A step that moves `t` to another shard: a pull or orphan pull of cpu `d` takes `t` from the head of its shard to shard `d`,
/// whose cpu serves `t`'s container, at a position no greater than that shard's old length; a pull lands it at the head
/// (the puller's shard was empty), and an orphan pull takes it only from a shard whose cpu does not serve the container.
pub open spec fn pulled_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, t: RwLockThreadPtr) -> bool {
    let c = ctn_of(u, t);
    &&& pos(u, t) == 0
    &&& pops_head(u, l, d, c, shard_of(u, t))
    &&& shard_of(u2, t) == d
    &&& cpu_serves_container(u, c, d) && cpu_serves_container(u2, c, d)
    &&& pos(u2, t) <= shard_queue(u, c, d).len()
    &&& l is RebalancePull ==> pos(u2, t) == 0
    &&& l is RebalancePull || l is OrphanPull && !cpu_serves_container(u, c, shard_of(u, t))
}

/// What a world step of cpu `d` with label `l` does to the waiting thread `t`.
pub open spec fn waiting_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, t: RwLockThreadPtr) -> bool {
    &&& !waiting(u2, t) ==> running(u2, t) || gone(u2, t)
    &&& waiting(u2, t) ==> ctn_of(u2, t) == ctn_of(u, t)
    &&& waiting(u2, t) && shard_of(u2, t) == shard_of(u, t) ==> stays_step(u, u2, l, d, t)
    &&& waiting(u2, t) && shard_of(u2, t) != shard_of(u, t) ==> pulled_step(u, u2, l, d, t)
    &&& l is Schedule && pops_head(u, l, d, ctn_of(u, t), shard_of(u, t)) && pos(u, t) == 0
        ==> u2.thread_map.dom().contains(t) && u2.thread_map[t].state == (ThreadState::RUNNING { cpu_id: d })
}

/// The scheduling frame of a step that touches no run queue: every scheduler is kept, every thread's last cpu is kept or
/// valid, and a thread waits after the step exactly as it waited before, unless it is now killed or gone.
pub open spec fn sched_frame(u: KernelU, u2: KernelU) -> bool {
    &&& u2.container_map.dom() =~= u.container_map.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c) ==> u2.container_map[c].scheduler == u.container_map[c].scheduler
    &&& forall|x: RwLockThreadPtr| #![trigger u2.thread_map[x]] u2.thread_map.dom().contains(x)
        ==> u.thread_map.dom().contains(x) && u2.thread_map[x].last_cpu == u.thread_map[x].last_cpu || index_valid(NUM_CPUS, u2.thread_map[x].last_cpu)
    &&& forall|x: RwLockThreadPtr| #![trigger waiting(u2, x)] waiting(u2, x)
        ==> waiting(u, x) && u2.thread_map[x].state == u.thread_map[x].state && u2.thread_map[x].owning_container == u.thread_map[x].owning_container
    &&& forall|x: RwLockThreadPtr| #![trigger waiting(u, x)] waiting(u, x) ==> waiting(u2, x) || gone(u2, x)
}

/// The cpu frame of every world step: no container appears or disappears, no cpu changes its kill mark, no container its
/// cpu-set kill mark, and a cpu keeps its running thread and process or drops both, except by a Schedule of that cpu.
pub open spec fn cpu_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId) -> bool {
    &&& forall|c: CpuId| #![trigger u2.cpu_array[c as int]] index_valid(NUM_CPUS, c) ==> u2.cpu_array[c as int].killed == u.cpu_array[c as int].killed
        && (u2.cpu_array[c as int].current_thread is Some || u2.cpu_array[c as int].current_process is Some ==> l is Schedule && c == d
            || u2.cpu_array[c as int].current_thread == u.cpu_array[c as int].current_thread && u2.cpu_array[c as int].current_process == u.cpu_array[c as int].current_process)
    &&& u2.container_map.dom() =~= u.container_map.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c) ==> u2.container_map[c].cpu_set_killed == u.container_map[c].cpu_set_killed
}

/// `t` first occurs in `q` at `p`.
pub proof fn first_at_implies_seq_pos(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr, p: int)
    requires 0 <= p < q.len(), q[p] == t, forall|j: int| 0 <= j < p ==> q[j] != t,
    ensures seq_pos(q, t) == p, q.contains(t),
{
    q.index_of_first_ensures(t);
    assert(q.contains(t));
    let i = q.index_of_first(t)->Some_0;
    if i < p { assert(q[i] != t); } else if i > p { assert(q[p] != t); }
}

/// The first occurrence of a contained `t`.
pub proof fn contains_implies_seq_pos_facts(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr)
    requires q.contains(t),
    ensures seq_pos(q, t) < q.len(), q[seq_pos(q, t) as int] == t, forall|j: int| 0 <= j < seq_pos(q, t) ==> q[j] != t,
{ q.index_of_first_ensures(t); }

/// A push at the tail keeps the position and what stands in front.
pub proof fn push_implies_seq_pos_kept(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr, x: RwLockThreadPtr)
    requires q.contains(t),
    ensures q.push(x).contains(t), seq_pos(q.push(x), t) == seq_pos(q, t), q.push(x).take(seq_pos(q, t) as int) == q.take(seq_pos(q, t) as int),
{
    contains_implies_seq_pos_facts(q, t);
    let p = seq_pos(q, t) as int;
    assert(q.push(x)[p] == t);
    first_at_implies_seq_pos(q.push(x), t, p);
    assert(q.push(x).take(p) =~= q.take(p));
}

/// Popping a head other than `t` lowers its position by one.
pub proof fn skip_head_implies_seq_pos_lowered(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr)
    requires q.contains(t), q[0] != t,
    ensures q.skip(1).contains(t), seq_pos(q.skip(1), t) + 1 == seq_pos(q, t),
{
    contains_implies_seq_pos_facts(q, t);
    let p = seq_pos(q, t) as int;
    assert(q.skip(1)[p - 1] == t);
    first_at_implies_seq_pos(q.skip(1), t, p - 1);
}

/// Popping a head other than `t` and pushing `prev`, if any, lowers its position by one.
pub proof fn switch_queue_implies_seq_pos_lowered(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr, prev: Option<RwLockThreadPtr>)
    requires q.contains(t), q[0] != t,
    ensures ({
        let q2 = match prev { Some(p) => q.skip(1).push(p), None => q.skip(1) };
        q2.contains(t) && seq_pos(q2, t) + 1 == seq_pos(q, t)
    }),
{
    skip_head_implies_seq_pos_lowered(q, t);
    if prev is Some { push_implies_seq_pos_kept(q.skip(1), t, prev->Some_0); }
}

/// Removing another thread keeps `t`, lowers its position, or keeps it with the same threads in front.
pub proof fn remove_value_implies_seq_pos_kept_or_lowered(q: Seq<RwLockThreadPtr>, t: RwLockThreadPtr, v: RwLockThreadPtr)
    requires q.contains(t), v != t,
    ensures
        q.remove_value(v).contains(t), seq_pos(q.remove_value(v), t) <= seq_pos(q, t),
        seq_pos(q.remove_value(v), t) == seq_pos(q, t) ==> q.remove_value(v).take(seq_pos(q, t) as int) == q.take(seq_pos(q, t) as int),
{
    contains_implies_seq_pos_facts(q, t);
    q.index_of_first_ensures(v);
    let p = seq_pos(q, t) as int;
    match q.index_of_first(v) {
        Some(i) => {
            let r = q.remove(i);
            assert(q.remove_value(v) == r);
            assert(i != p);
            if i < p {
                assert(r[p - 1] == q[p]);
                assert forall|j: int| 0 <= j < p - 1 implies r[j] != t by { if j < i { assert(r[j] == q[j]); } else { assert(r[j] == q[j + 1]); } };
                first_at_implies_seq_pos(r, t, p - 1);
            } else {
                assert(r[p] == q[p]);
                assert forall|j: int| 0 <= j < p implies r[j] != t by { assert(r[j] == q[j]); };
                first_at_implies_seq_pos(r, t, p);
                assert(r.take(p) =~= q.take(p));
            }
        },
        None => {},
    }
}

/// A step with the scheduling frame keeps the run-queue invariant and leaves every waiting thread where it was.
pub proof fn sched_frame_implies_run_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, t: RwLockThreadPtr)
    requires queue_inv(u), sched_frame(u, u2), !(l is Schedule || l is RebalancePull || l is OrphanPull),
    ensures queue_inv(u2), waiting(u, t) ==> waiting_step(u, u2, l, d, t),
{
    reveal(queue_inv);
    assert forall|x: RwLockThreadPtr| #![trigger waiting(u2, x)] waiting(u2, x) implies queued(u2, x) by {
        assert(waiting(u, x) && queued(u, x));
        assert(u2.container_map[ctn_of(u, x)].scheduler == u.container_map[ctn_of(u, x)].scheduler);
    };
    assert forall|x: RwLockThreadPtr| #![trigger u2.thread_map[x]] u2.thread_map.dom().contains(x) implies index_valid(NUM_CPUS, u2.thread_map[x].last_cpu) by {
        if u.thread_map.dom().contains(x) { assert(index_valid(NUM_CPUS, u.thread_map[x].last_cpu)); }
    };
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u2.container_map.dom().contains(c) implies u2.container_map[c].scheduler.len() == NUM_CPUS by {
        assert(u.container_map.dom().contains(c));
        assert(u.container_map[c].scheduler.len() == NUM_CPUS);
    };
    if waiting(u, t) && waiting(u2, t) {
        assert(u2.container_map[ctn_of(u, t)].scheduler == u.container_map[ctn_of(u, t)].scheduler);
        assert(queue_of(u2, t) == queue_of(u, t));
    }
}
} // verus!

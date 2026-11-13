//! Round 8: every step of `kill_process` proves what its killer `d` owes the kill invariants (`kill_own_post`) and leaves
//! the tables alone or changes only the empty target's (`kill_table_post`), one lemma per step.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_kill::*;
use crate::kill_steps::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;

verus! {
/// An element of `s.push(x)` is an element of `s` or `x`.
pub proof fn push_contains_implies_contains_or_last<A>(s: Seq<A>, x: A, y: A)
    ensures s.push(x).contains(y) <==> (s.contains(y) || y == x),
{
    if s.contains(y) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
        assert(s.push(x)[i] == y);
    }
    if y == x { assert(s.push(x)[s.len() as int] == x); }
    if s.push(x).contains(y) {
        let j = choose|j: int| 0 <= j < s.push(x).len() && s.push(x)[j] == y;
        if j < s.len() { assert(s[j] == y); }
    }
}

/// A middle kill step starts from a killer inside `kill_process` that holds what its walk needs, away from its own process.
pub proof fn kill_step_pre_implies_kill_holds(u: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), kill_process_step_pre(u, d),
    ensures
        in_kill(u, d), kill_holds(u, d), kill_target(u, d) != kill_own(u, d), kill_killer(u, d) == u.cpu_array[d as int].current_thread->Some_0,
        u.thread_map.dom().contains(kill_killer(u, d)), proc_wf_at(u, kill_target(u, d)), proc_wf_at(u, kill_own(u, d)),
{
    reveal(kill_process_step_pre);
    assert(thread_wf_at(u.thread_map[kill_killer(u, d)]));
    assert(in_kill(u, d));
    kill_holds_at(u, d);
    proc_wf_at_of(u, kill_target(u, d));
    proc_wf_at_of(u, kill_own(u, d));
}

/// Inside `kill_process` the killer moves to a process kill record.
pub proof fn in_kill_implies_killer_at(u: KernelU, d: CpuId, p: RwLockProcessPtr, st: KillStage)
    requires in_kill(u, d),
    ensures kill_killer_at(u, d, p, st) == (ThreadU { syscall_progress: kill_progress(p, st), ..cur_thread(u, d) }),
{}

/// A step that keeps the killer's cpu, target, and the lock, mark, and ancestors of every process keeps the killer's holds,
/// given the facts of its new stage, and keeps every process it marked on its walk.
proof fn kill_same_target_implies_holds(u: KernelU, u2: KernelU, d: CpuId)
    requires
        kill_world_inv(u), in_kill(u, d), kill_holds(u, d), kill_target(u, d) != kill_own(u, d),
        u2.cpu_array[d as int] == u.cpu_array[d as int], in_kill(u2, d), cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state,
        kill_target(u2, d) == kill_target(u, d), kill_stage_ok(u2, d), u2.process_map.dom() == u.process_map.dom(),
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) ==> u2.process_map[p].lock_state == u.process_map[p].lock_state
            && u2.process_map[p].killed == u.process_map[p].killed && u2.process_map[p].uppertree_seq == u.process_map[p].uppertree_seq,
    ensures
        kill_holds(u2, d),
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
            u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
                ==> in_kill(u2, d) && kill_on_path(u2, d, p),
{
    let tp = kill_target(u, d);
    let pp = kill_own(u, d);
    assert(u2.process_map[pp].lock_state == u.process_map[pp].lock_state && u2.process_map[pp].killed == u.process_map[pp].killed);
    assert(u2.process_map[tp].lock_state == u.process_map[tp].lock_state && u2.process_map[tp].uppertree_seq == u.process_map[tp].uppertree_seq);
    assert forall|q: RwLockProcessPtr| #![trigger u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q)]
        u2.process_map.dom().contains(q) && u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q) && u2.process_map[q].uppertree_seq.contains(pp)
        implies u2.process_map[q].killed && u2.process_map[q].lock_state == (LockStateU::WriteLocked { writer: d }) by {
        assert(u.process_map[tp].uppertree_seq.contains(q));
        assert(u.process_map[q].uppertree_seq.contains(pp));
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
        implies in_kill(u2, d) && kill_on_path(u2, d, p) by {
        assert(u.process_map[p].killed && u.process_map[p].lock_state == u2.process_map[p].lock_state);
        if p != tp { assert(u.process_map[p].uppertree_seq.contains(pp)); }
    };
}

/// Removing thread `v` from the threads of `tp`, which listed it, and changing no other process shape keeps the process
/// tree well formed.
pub proof fn owned_removed_implies_processes_wf(u: KernelU, u2: KernelU, tp: RwLockProcessPtr, v: RwLockThreadPtr)
    requires
        kernel_u_ownership_wf(u), processes_wf(u), u.process_map.dom().contains(tp), u.process_map[tp].owned_threads.contains(v),
        u2.process_map.dom() == u.process_map.dom(),
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && p != tp ==> u2.process_map[p] == u.process_map[p],
        u2.process_map[tp].parent == u.process_map[tp].parent && u2.process_map[tp].children == u.process_map[tp].children,
        u2.process_map[tp].uppertree_seq == u.process_map[tp].uppertree_seq && u2.process_map[tp].depth == u.process_map[tp].depth,
        u2.process_map[tp].zombie == u.process_map[tp].zombie && (u2.process_map[tp].pagetable is Some) == (u.process_map[tp].pagetable is Some)
            || u2.process_map[tp].zombie && u2.process_map[tp].owned_threads.len() == 0,
        u2.process_map[tp].owned_threads == u.process_map[tp].owned_threads.remove_value(v),
        forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u.thread_map.dom().contains(t) && t != v
            ==> u2.thread_map[t].owning_proc == u.thread_map[t].owning_proc && (u2.thread_map[t].state is DANGLING ==> u.thread_map[t].state is DANGLING),
    ensures processes_wf(u2),
{
    reveal(kernel_u_process_threads_wf);
    proc_wf_at_of(u, tp);
    no_dup_remove_value_implies_removed(u.process_map[tp].owned_threads, v);
    assert(u.thread_map[v].owning_proc == tp);
    assert forall|p: RwLockProcessPtr| #![trigger proc_wf_at(u2, p)] u2.process_map.dom().contains(p) implies proc_wf_at(u2, p) by {
        proc_wf_at_of(u, p);
        let b = u2.process_map[p];
        assert forall|ch: RwLockProcessPtr| #![trigger b.children.contains(ch)] b.children.contains(ch)
            implies u2.process_map.dom().contains(ch) && u2.process_map[ch].parent == Some(p) && u2.process_map[ch].uppertree_seq == b.uppertree_seq.push(p) by {
            assert(u.process_map[p].children.contains(ch));
        };
        if b.parent is Some { assert(u.process_map[p].parent == b.parent); }
        assert forall|q: RwLockProcessPtr| #![trigger b.uppertree_seq.contains(q)] b.uppertree_seq.contains(q) && u2.process_map.dom().contains(q)
            implies u2.process_map[q].uppertree_seq.len() < b.uppertree_seq.len() by { assert(u.process_map[p].uppertree_seq.contains(q)); };
        assert forall|t: RwLockThreadPtr| #![trigger b.owned_threads.contains(t)] b.owned_threads.contains(t)
            implies !(u2.thread_map[t].state is DANGLING) && u2.thread_map[t].owning_proc == p by {
            assert(u.process_map[p].owned_threads.contains(t));
            assert(u.thread_map.dom().contains(t) && u.thread_map[t].owning_proc == p);
            if t == v { assert(p == tp); }
        };
    };
}

/// Two processes are not each other's ancestors.
proof fn ancestors_acyclic(u: KernelU, p: RwLockProcessPtr, q: RwLockProcessPtr)
    requires processes_wf(u), u.process_map.dom().contains(p), u.process_map.dom().contains(q),
    ensures !(u.process_map[p].uppertree_seq.contains(q) && u.process_map[q].uppertree_seq.contains(p)), !u.process_map[p].uppertree_seq.contains(p),
{
    proc_wf_at_of(u, p);
    proc_wf_at_of(u, q);
}

// ---------------------------------------------------------------------------------------------------------------------
// One lemma per step.

proof fn kill_enter_implies_post(u: KernelU, u2: KernelU, d: CpuId, child_index: usize)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessEnter { child_index }, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_enter_step_pre); reveal(kill_process_enter_step);
    reveal(kernel_u_cpu_ownership_wf);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let cpu = u.cpu_array[d as int];
    let pp = cpu.current_process->Some_0;
    let k = cpu.current_thread->Some_0;
    let ch = u.process_map[pp].children[child_index as int];
    proc_wf_at_of(u, pp);
    assert(u.process_map[pp].children.contains(ch));
    proc_wf_at_of(u, ch);
    push_contains_implies_contains_or_last(u.process_map[pp].uppertree_seq, pp, pp);
    ancestors_acyclic(u, pp, pp);
    assert(ch != pp) by { assert(u.process_map[ch].uppertree_seq.len() == u.process_map[pp].uppertree_seq.len() + 1); };
    assert(!in_kill(u, d));
    assert(in_kill(u2, d));
    assert(kill_target(u2, d) == ch && kill_stage(u2, d) == KillStage::Walk && kill_own(u2, d) == pp);
    assert forall|q: RwLockProcessPtr| #![trigger u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q)]
        u2.process_map.dom().contains(q) && u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q) && u2.process_map[q].uppertree_seq.contains(pp)
        implies u2.process_map[q].killed && u2.process_map[q].lock_state == (LockStateU::WriteLocked { writer: d }) by {
        push_contains_implies_contains_or_last(u.process_map[pp].uppertree_seq, pp, q);
        ancestors_acyclic(u, pp, q);
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
        implies in_kill(u2, d) && kill_on_path(u2, d, p) by {
        if p != ch && p != pp { assert(u.process_map[p].killed); }
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_wf_at(u2.thread_map[t]) by {
        if t != k { assert(thread_wf_at(u.thread_map[t])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_mark_child_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessMarkChild, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_mark_child_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let pp = kill_own(u, d);
    let t = u.process_map[tp];
    let k = kill_killer(u, d);
    let ch = t.children[0];
    assert(t.children.contains(ch));
    proc_wf_at_of(u, ch);
    ancestors_acyclic(u, ch, ch);
    push_contains_implies_contains_or_last(t.uppertree_seq, tp, pp);
    in_kill_implies_killer_at(u, d, ch, KillStage::Walk);
    assert(ch != pp && ch != tp);
    assert(in_kill(u2, d));
    assert(kill_target(u2, d) == ch && kill_stage(u2, d) == KillStage::Walk && kill_own(u2, d) == pp);
    assert forall|q: RwLockProcessPtr| #![trigger u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q)]
        u2.process_map.dom().contains(q) && u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q) && u2.process_map[q].uppertree_seq.contains(pp)
        implies u2.process_map[q].killed && u2.process_map[q].lock_state == (LockStateU::WriteLocked { writer: d }) by {
        push_contains_implies_contains_or_last(t.uppertree_seq, tp, q);
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
        implies in_kill(u2, d) && kill_on_path(u2, d, p) by {
        if p != ch {
            assert(u.process_map[p].killed && kill_on_path(u, d, p));
            push_contains_implies_contains_or_last(t.uppertree_seq, tp, p);
        }
    };
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_dangling_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessDangling, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_dangling_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let t = u.process_map[tp];
    let k = kill_killer(u, d);
    let v = t.owned_threads[0];
    assert(t.owned_threads.contains(v));
    assert(thread_wf_at(u.thread_map[v]));
    assert(v != k);
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == kill_stage(u, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != v { assert(thread_wf_at(u.thread_map[t2])); }
    };
    owned_removed_implies_processes_wf(u, u2, tp, v);
    assert(tables_kept(u, u2));
}

proof fn kill_mark_thread_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessMarkThread, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_mark_thread_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let t = u.process_map[tp];
    let k = kill_killer(u, d);
    let v = t.owned_threads[0];
    assert(t.owned_threads.contains(v));
    assert(thread_wf_at(u.thread_map[v]));
    assert(v != k);
    in_kill_implies_killer_at(u, d, tp, KillStage::Thread { thread: v });
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == (KillStage::Thread { thread: v }));
    assert(kill_victim_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != v && t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_dequeue_scheduled_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessDequeueScheduled, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_dequeue_scheduled_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let k = kill_killer(u, d);
    let v = kill_stage(u, d)->Thread_thread;
    assert(v != k);
    assert(in_kill(u2, d) && kill_target(u2, d) == kill_target(u, d) && kill_stage(u2, d) == kill_stage(u, d));
    assert(kill_victim_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        assert(thread_wf_at(u.thread_map[t2]));
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_dequeue_endpoint_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessDequeueEndpoint, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_dequeue_endpoint_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let k = kill_killer(u, d);
    let v = kill_stage(u, d)->Thread_thread;
    assert(v != k);
    assert(in_kill(u2, d) && kill_target(u2, d) == kill_target(u, d) && kill_stage(u2, d) == kill_stage(u, d));
    assert(kill_victim_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        assert(thread_wf_at(u.thread_map[t2]));
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_cpu_to_idle_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessCpuToIdle, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_cpu_to_idle_step);
    reveal(kernel_u_cpu_ownership_wf);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let k = kill_killer(u, d);
    let v = kill_stage(u, d)->Thread_thread;
    assert(v != k);
    assert(u2.cpu_array[d as int] == u.cpu_array[d as int]);
    assert(in_kill(u2, d) && kill_target(u2, d) == kill_target(u, d) && kill_stage(u2, d) == kill_stage(u, d));
    assert(kill_victim_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        assert(thread_wf_at(u.thread_map[t2]));
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_unlink_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessUnlink, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_unlink_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    let v = kill_stage(u, d)->Thread_thread;
    assert(v != k);
    in_kill_implies_killer_at(u, d, tp, KillStage::Walk);
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == KillStage::Walk);
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    owned_removed_implies_processes_wf(u, u2, tp, v);
    assert(tables_kept(u, u2));
}

proof fn kill_reassign_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessReassignFunctions, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_reassign_functions_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_kill(u2, d) && kill_target(u2, d) == kill_target(u, d) && kill_stage(u2, d) == kill_stage(u, d));
    kill_same_target_implies_holds(u, u2, d);
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_lock_table_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessLockTable, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_lock_table_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    in_kill_implies_killer_at(u, d, tp, KillStage::Reclaim { flushed: false });
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == (KillStage::Reclaim { flushed: false }));
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(table_killer(u2, d) && table_killer_proc(u2, d) == tp);
    assert(kill_target_table_step(u, u2, d, tp));
}

proof fn kill_table_hidden_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessTableHidden, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_table_hidden_step); reveal(process_table_hidden_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == kill_stage(u, d));
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(table_killer(u2, d) && table_killer_proc(u2, d) == tp);
    assert(kill_target_table_step(u, u2, d, tp));
}

proof fn kill_tlb_cleared_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessTlbCleared, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kernel_u_cpu_tlb_cleared);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(u2.process_map == u.process_map && u2.thread_map == u.thread_map && u2.cpu_array == u.cpu_array);
    kill_same_target_implies_holds(u, u2, d);
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_flushed_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessFlushed, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_flushed_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    in_kill_implies_killer_at(u, d, tp, KillStage::Reclaim { flushed: true });
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == (KillStage::Reclaim { flushed: true }));
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_iommu_leaf_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessIommuLeaf, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_iommu_leaf_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_kill(u2, d) && kill_target(u2, d) == kill_target(u, d) && kill_stage(u2, d) == kill_stage(u, d));
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_refund_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessRefund, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_refund_step);
    reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_container_quota_2m_increased); reveal(kernel_u_container_quota_1g_increased);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(u2.process_map == u.process_map && u2.thread_map == u.thread_map && u2.cpu_array == u.cpu_array);
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c) implies u2.container_map[c].lock_state == u.container_map[c].lock_state
        && u2.container_map[c].pcid_allocator_lock == u.container_map[c].pcid_allocator_lock && u2.container_map[c].free_pcids == u.container_map[c].free_pcids by {};
    kill_same_target_implies_holds(u, u2, d);
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_quota_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessQuota, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_quota_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    let st = kill_stage(u, d);
    let size = kill_process_quota_stage_after(st)->Some_0->Quota_returned;
    in_kill_implies_killer_at(u, d, tp, KillStage::Quota { returned: size });
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == (KillStage::Quota { returned: size }));
    assert(kill_stage_flushed(st));
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_unlock_table_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessUnlockTable, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_unlock_table_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    in_kill_implies_killer_at(u, d, tp, KillStage::Zombie);
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == KillStage::Zombie);
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(table_killer(u, d) && table_killer_proc(u, d) == tp && !table_killer(u2, d));
    assert(kill_target_table_step(u, u2, d, tp));
}

proof fn kill_zombify_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessZombify, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_zombify_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    in_kill_implies_killer_at(u, d, tp, KillStage::Retire);
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == KillStage::Retire);
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(!table_present(u2, tp) && !table_killer(u, d) && !table_killer(u2, d));
    assert(kill_target_table_step(u, u2, d, tp));
}

proof fn kill_zombie_retire_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessZombieRetire, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_zombie_retire_step);
    kill_step_pre_implies_kill_holds(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let tp = kill_target(u, d);
    let k = kill_killer(u, d);
    in_kill_implies_killer_at(u, d, tp, KillStage::Retire);
    assert(in_kill(u2, d) && kill_target(u2, d) == tp && kill_stage(u2, d) == KillStage::Retire);
    assert(kill_stage_ok(u2, d));
    kill_same_target_implies_holds(u, u2, d);
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn kill_retire_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessRetire, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_retire_step);
    kill_step_pre_implies_kill_holds(u, d);
    let tp = kill_target(u, d);
    let pp = kill_own(u, d);
    let t = u.process_map[tp];
    let k = kill_killer(u, d);
    let par = t.parent->Some_0;
    assert(u.process_map.dom().contains(par) && t.uppertree_seq == u.process_map[par].uppertree_seq.push(par));
    proc_wf_at_of(u, par);
    ancestors_acyclic(u, tp, tp);
    ancestors_acyclic(u, par, par);
    push_contains_implies_contains_or_last(u.process_map[par].uppertree_seq, par, pp);
    push_contains_implies_contains_or_last(u.process_map[par].uppertree_seq, par, par);
    assert(par != tp);
    assert(u.process_map[par].killed || par == pp);
    assert(u.process_map[par].lock_state == (LockStateU::WriteLocked { writer: d }));
    in_kill_implies_killer_at(u, d, par, KillStage::Walk);
    assert(in_kill(u2, d) && kill_target(u2, d) == par && kill_stage(u2, d) == KillStage::Walk && kill_own(u2, d) == pp);
    assert(u2.process_map.dom() =~= u.process_map.dom().remove(tp));
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map.dom().contains(p) implies {
        &&& u2.process_map[p].lock_state == u.process_map[p].lock_state && u2.process_map[p].killed == u.process_map[p].killed
        &&& u2.process_map[p].uppertree_seq == u.process_map[p].uppertree_seq && u2.process_map[p].depth == u.process_map[p].depth
        &&& u2.process_map[p].parent == u.process_map[p].parent && u2.process_map[p].owned_threads == u.process_map[p].owned_threads
        &&& u2.process_map[p].zombie == u.process_map[p].zombie && u2.process_map[p].pagetable == u.process_map[p].pagetable
        &&& u2.process_map[p].children == (if p == par { u.process_map[p].children.remove_value(tp) } else { u.process_map[p].children })
        &&& p != par ==> proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p])
    } by {};
    // kill_d_frame: a process another cpu holds is not the parent, so only its subtree set changes.
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d)
        implies u2.process_map.dom().contains(p) && proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p]) by {};
    // The killer's holds at the parent.
    assert forall|q: RwLockProcessPtr| #![trigger u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q)]
        u2.process_map.dom().contains(q) && u2.process_map[kill_target(u2, d)].uppertree_seq.contains(q) && u2.process_map[q].uppertree_seq.contains(pp)
        implies u2.process_map[q].killed && u2.process_map[q].lock_state == (LockStateU::WriteLocked { writer: d }) by {
        push_contains_implies_contains_or_last(u.process_map[par].uppertree_seq, par, q);
    };
    assert(kill_holds(u2, d));
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
        implies in_kill(u2, d) && kill_on_path(u2, d, p) by {
        assert(u.process_map[p].killed && kill_on_path(u, d, p));
        push_contains_implies_contains_or_last(u.process_map[par].uppertree_seq, par, p);
    };
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    // The process tree without the empty target.
    no_dup_remove_value_implies_removed(u.process_map[par].children, tp);
    assert forall|p: RwLockProcessPtr| #![trigger proc_wf_at(u2, p)] u2.process_map.dom().contains(p) implies proc_wf_at(u2, p) by {
        proc_wf_at_of(u, p);
        let a = u.process_map[p];
        let b = u2.process_map[p];
        assert forall|ch: RwLockProcessPtr| #![trigger b.children.contains(ch)] b.children.contains(ch)
            implies u2.process_map.dom().contains(ch) && u2.process_map[ch].parent == Some(p) && u2.process_map[ch].uppertree_seq == b.uppertree_seq.push(p) by {
            assert(a.children.contains(ch));
            if ch == tp { assert(p == par); }
        };
        if b.parent is Some {
            let pr = b.parent->Some_0;
            assert(pr != tp) by { if pr == tp { assert(t.children.contains(p)); } };
            if pr == par { assert(u.process_map[par].children.contains(p)); }
        }
        assert forall|q: RwLockProcessPtr| #![trigger b.uppertree_seq.contains(q)] b.uppertree_seq.contains(q) && u2.process_map.dom().contains(q)
            implies u2.process_map[q].uppertree_seq.len() < b.uppertree_seq.len() by { assert(a.uppertree_seq.contains(q)); };
        assert forall|t2: RwLockThreadPtr| #![trigger b.owned_threads.contains(t2)] b.owned_threads.contains(t2)
            implies !(u2.thread_map[t2].state is DANGLING) && u2.thread_map[t2].owning_proc == p by { assert(a.owned_threads.contains(t2)); };
    };
    assert(!table_killer(u, d) && !table_killer(u2, d));
    assert(kill_target_table_step(u, u2, d, tp));
}

proof fn kill_finish_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::KillProcessFinish, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step);
    reveal(kernel_u_cpu_ownership_wf);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    let cpu = u.cpu_array[d as int];
    let pp = cpu.current_process->Some_0;
    let k = cpu.current_thread->Some_0;
    assert(in_kill(u, d));
    kill_holds_at(u, d);
    assert(kill_target(u, d) == pp);
    proc_wf_at_of(u, pp);
    assert(!in_kill(u2, d));
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
        implies in_kill(u2, d) && kill_on_path(u2, d, p) by {
        assert(p != pp);
        assert(u.process_map[p].killed && kill_on_path(u, d, p));
        ancestors_acyclic(u, p, pp);
    };
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != k { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

/// Every step of `kill_process` in the world proves what its killer owes and keeps the tables or changes only the empty
/// target's.
pub proof fn kill_step_implies_own_post(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), kill_label(l), labeled_step(l, u, u2, d),
    ensures kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    match l {
        StepLabel::KillProcessEnter { child_index } => kill_enter_implies_post(u, u2, d, child_index),
        StepLabel::KillProcessMarkChild => kill_mark_child_implies_post(u, u2, d),
        StepLabel::KillProcessDangling => kill_dangling_implies_post(u, u2, d),
        StepLabel::KillProcessMarkThread => kill_mark_thread_implies_post(u, u2, d),
        StepLabel::KillProcessDequeueScheduled => kill_dequeue_scheduled_implies_post(u, u2, d),
        StepLabel::KillProcessDequeueEndpoint => kill_dequeue_endpoint_implies_post(u, u2, d),
        StepLabel::KillProcessCpuToIdle => kill_cpu_to_idle_implies_post(u, u2, d),
        StepLabel::KillProcessUnlink => kill_unlink_implies_post(u, u2, d),
        StepLabel::KillProcessReassignFunctions => kill_reassign_implies_post(u, u2, d),
        StepLabel::KillProcessLockTable => kill_lock_table_implies_post(u, u2, d),
        StepLabel::KillProcessTableHidden => kill_table_hidden_implies_post(u, u2, d),
        StepLabel::KillProcessTlbCleared => kill_tlb_cleared_implies_post(u, u2, d),
        StepLabel::KillProcessFlushed => kill_flushed_implies_post(u, u2, d),
        StepLabel::KillProcessIommuLeaf => kill_iommu_leaf_implies_post(u, u2, d),
        StepLabel::KillProcessRefund => kill_refund_implies_post(u, u2, d),
        StepLabel::KillProcessQuota => kill_quota_implies_post(u, u2, d),
        StepLabel::KillProcessUnlockTable => kill_unlock_table_implies_post(u, u2, d),
        StepLabel::KillProcessZombify => kill_zombify_implies_post(u, u2, d),
        StepLabel::KillProcessZombieRetire => kill_zombie_retire_implies_post(u, u2, d),
        StepLabel::KillProcessRetire => kill_retire_implies_post(u, u2, d),
        StepLabel::KillProcessFinish => kill_finish_implies_post(u, u2, d),
        _ => {},
    }
}

/// A kill step keeps every other cpu, every foreign hold, and the kill invariants.
pub proof fn kill_step_implies_kill_world_inv_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), kill_label(l), labeled_step(l, u, u2, d),
    ensures others_kept(u, u2, d), foreign_holds_kept(u, u2, d), kill_world_inv(u2), kill_own_post(u, u2, d), kill_table_post(u, u2, d),
{
    kill_step_implies_own_post(u, u2, l, d);
    kill_d_frame_implies_others_kept(u, u2, d);
    assert forall|c: CpuId| #![trigger u2.cpu_array[c as int]] in_kill(u2, c) implies kill_holds(u2, c) by {};
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) implies {
        &&& cpu_outside(u2, x) ==> !(u2.cpu_array[x as int].op is InStep)
        &&& !cpu_outside(u2, x) && u2.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u2, x).syscall_progress is None
    } by { if x == d && in_kill(u2, d) { assert(kill_holds(u2, d)); } };
}
} // verus!

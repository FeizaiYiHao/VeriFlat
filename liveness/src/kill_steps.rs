//! Round 8: every step of `kill_process` keeps the world invariants. A kill step of `d` touches only objects that are
//! unlocked or that `d` write-holds, besides cpus it sends from running to idle and the subtree sets of the ancestors of a
//! retired process (`kill_d_frame`); its own facts are proved per step.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::fill_quota::*;
use crate::family_kill::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;

verus! {
pub open spec fn held_by_other(l: LockStateU, d: CpuId) -> bool { l is WriteLocked && l->WriteLocked_writer != d }

/// No cpu maps, unmaps, or shares in the page table of `tp`.
pub open spec fn table_unworked(u: KernelU, tp: RwLockProcessPtr) -> bool {
    forall|c: CpuId| #![trigger table_op(u, c)] #![trigger table_sharer(u, c)] table_op(u, c) || table_sharer(u, c) ==> table_proc(u, c) != tp
}

/// A process but for its subtree set.
pub open spec fn proc_kview(p: ProcessU) -> ProcessU { ProcessU { subtree_set: Set::empty(), ..p } }

/// What a kill step of `d` leaves alone: no process appears, ancestors, depths, and parents stay, a marked process not held
/// by `d` stays marked and held, objects other cpus hold stay, container and endpoint locks stay, and every cpu but `d` stays
/// or is an unlocked cpu outside a kernel step.
pub open spec fn kill_d_frame(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& u2.process_map.dom().subset_of(u.process_map.dom())
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map.dom().contains(p) ==> {
        &&& u2.process_map[p].uppertree_seq == u.process_map[p].uppertree_seq && u2.process_map[p].depth == u.process_map[p].depth
        &&& u2.process_map[p].killed && u2.process_map[p].lock_state != (LockStateU::WriteLocked { writer: d })
            ==> u.process_map[p].killed && u2.process_map[p].lock_state == u.process_map[p].lock_state
    }
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d)
        ==> u2.process_map.dom().contains(p) && proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p])
    &&& forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u.thread_map.dom().contains(t) && held_by_other(u.thread_map[t].lock_state, d)
        ==> u2.thread_map.dom().contains(t) && u2.thread_map[t] == u.thread_map[t]
    &&& forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u.thread_map.dom().contains(t) && u.thread_map[t].state is RUNNING
        && (index_valid(NUM_CPUS, d) ==> Some(t) != u.cpu_array[d as int].current_thread)
        ==> u2.thread_map.dom().contains(t) && u2.thread_map[t].syscall_progress == u.thread_map[t].syscall_progress
            && (u2.thread_map[t].lock_state == u.thread_map[t].lock_state || u2.thread_map[t].lock_state is Unlocked || u2.thread_map[t].lock_state == (LockStateU::WriteLocked { writer: d }))
    &&& forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c)
        ==> (held_by_other(u.container_map[c].lock_state, d) ==> u2.container_map[c].lock_state == u.container_map[c].lock_state)
        && (held_by_other(u.container_map[c].pcid_allocator_lock, d) ==> u2.container_map[c].pcid_allocator_lock == u.container_map[c].pcid_allocator_lock
            && u2.container_map[c].free_pcids == u.container_map[c].free_pcids)
    &&& forall|e: RwLockEndpointPtr| #![trigger u2.endpoint_map[e]] u.endpoint_map.dom().contains(e) && held_by_other(u.endpoint_map[e].lock_state, d)
        ==> u2.endpoint_map.dom().contains(e) && u2.endpoint_map[e].lock_state == u.endpoint_map[e].lock_state
    &&& forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && x != d
        ==> u2.cpu_array[x as int] == u.cpu_array[x as int] || cpu_outside(u, x) && cpu_outside(u2, x) && !(u2.cpu_array[x as int].op is InStep)
    &&& u2.kernel_l4_end == u.kernel_l4_end
}

/// What a kill step of `d` proves of `d` itself: its frame, its holds and marks, the thread and process facts, and its
/// cpu's mode.
pub open spec fn kill_own_post(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& kill_d_frame(u, u2, d)
    &&& in_kill(u2, d) ==> kill_holds(u2, d)
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d })
            ==> in_kill(u2, d) && kill_on_path(u2, d, p)
    &&& threads_wf(u2)
    &&& processes_wf(u2)
    &&& cpu_outside(u2, d) ==> !(u2.cpu_array[d as int].op is InStep)
    &&& !cpu_outside(u2, d) ==> in_kill(u2, d)
    &&& op_in_step_kept(u, u2, d)
    &&& cpu_outside(u, d) || in_kill(u, d)
}

/// A kill step that changes only the tables of the empty target `tp`, which no cpu maps or unmaps in.
pub open spec fn kill_target_table_step(u: KernelU, u2: KernelU, d: CpuId, tp: RwLockProcessPtr) -> bool {
    &&& u.process_map.dom().contains(tp) && (u.process_map[tp].owned_threads.len() == 0 || table_unworked(u, tp))
    &&& u.process_map[tp].lock_state == (LockStateU::WriteLocked { writer: d })
    &&& u2.process_map.dom().subset_of(u.process_map.dom())
    &&& forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != tp && u.process_map.dom().contains(p) ==> u2.process_map.dom().contains(p) && table_view(u2, p) == table_view(u, p)
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] p != tp && u.process_map.dom().contains(p)
        ==> u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k
    &&& table_present(u2, tp) ==> {
        &&& table_present(u, tp)
        &&& table_windows(u2, tp).dom().subset_of(table_windows(u, tp).dom())
        &&& forall|w: WindowVa| #![trigger table_windows(u2, tp)[w]] table_windows(u2, tp).dom().contains(w) ==> table_windows(u2, tp)[w] == table_windows(u, tp)[w]
        &&& !(table_lock(u2, tp) is ReadLocked)
        &&& table_lock(u2, tp) is WriteLocked ==> table_killer(u2, table_lock(u2, tp)->WriteLocked_writer) && table_killer_proc(u2, table_lock(u2, tp)->WriteLocked_writer) == tp
    }
    &&& table_killer(u, d) ==> table_killer_proc(u, d) == tp
    &&& table_killer(u2, d) ==> table_killer_proc(u2, d) == tp
}

/// The tables after a kill step: kept, with `d` reclaiming the same table or none, or changed only at the empty target.
pub open spec fn kill_table_post(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    ||| tables_kept(u, u2) && table_killer(u2, d) == table_killer(u, d) && (table_killer(u, d) ==> table_killer_proc(u2, d) == table_killer_proc(u, d))
    ||| kill_target_table_step(u, u2, d, kill_target(u, d))
}

/// No duplicate is left by removing a value, which then is gone, and every other element stays.
pub proof fn no_dup_remove_value_implies_removed<A>(s: Seq<A>, v: A)
    requires s.no_duplicates(),
    ensures
        s.remove_value(v).no_duplicates(), !s.remove_value(v).contains(v),
        forall|t: A| #![trigger s.remove_value(v).contains(t)] s.remove_value(v).contains(t) ==> s.contains(t),
        forall|t: A| #![trigger s.contains(t)] s.contains(t) && t != v ==> s.remove_value(v).contains(t),
{
    s.index_of_first_ensures(v);
    match s.index_of_first(v) {
        Some(i) => {
            let r = s.remove(i);
            assert(r.len() == s.len() - 1);
            assert forall|j: int| 0 <= j < r.len() implies r[j] == (if j < i { s[j] } else { s[j + 1] }) by {};
            assert forall|j: int, k: int| 0 <= j < r.len() && 0 <= k < r.len() && j != k implies r[j] != r[k] by {
                let jj = if j < i { j } else { j + 1 };
                let kk = if k < i { k } else { k + 1 };
                assert(s[jj] != s[kk]);
            };
            assert forall|t: A| #![trigger r.contains(t)] r.contains(t) implies s.contains(t) && t != v by {
                let j = choose|j: int| 0 <= j < r.len() && r[j] == t;
                let jj = if j < i { j } else { j + 1 };
                assert(s[jj] == t);
                assert(jj != i);
            };
            assert forall|t: A| #![trigger s.contains(t)] s.contains(t) && t != v implies r.contains(t) by {
                let j = choose|j: int| 0 <= j < s.len() && s[j] == t;
                assert(j != i);
                let jj = if j < i { j } else { j - 1 };
                assert(r[jj] == t);
            };
        },
        None => {},
    }
}

/// A cpu inside `mmap_4k`, `unmap_4k`, or `new_process` runs a thread of the process it works on.
pub proof fn table_op_implies_proc_has_thread(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), table_op(u, c) || table_sharer(u, c),
    ensures u.process_map.dom().contains(table_proc(u, c)), u.process_map[table_proc(u, c)].owned_threads.len() > 0,
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    let t = u.cpu_array[c as int].current_thread->Some_0;
    assert(u.thread_map.dom().contains(t));
    assert(u.process_map[table_proc(u, c)].owned_threads.contains(t));
}

/// The kill frame of `d` keeps every other cpu, every foreign hold, and every other killer's holds and marks.
pub proof fn kill_d_frame_implies_others_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), kill_d_frame(u, u2, d),
    ensures
        others_kept(u, u2, d), foreign_holds_kept(u, u2, d),
        forall|x: CpuId| #![trigger u2.cpu_array[x as int]] x != d && in_kill(u2, x) ==> kill_holds(u2, x),
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
            u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state != (LockStateU::WriteLocked { writer: d }) ==> {
                let w = u2.process_map[p].lock_state->WriteLocked_writer;
                &&& u2.process_map[p].lock_state is WriteLocked
                &&& in_kill(u2, w)
                &&& kill_on_path(u2, w, p)
            },
        forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && x != d ==> {
            &&& cpu_outside(u2, x) ==> !(u2.cpu_array[x as int].op is InStep)
            &&& !cpu_outside(u2, x) && u2.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u2, x).syscall_progress is None
        },
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        assert(u2.cpu_array[x as int] == u.cpu_array[x as int] || cpu_outside(u, x) && cpu_outside(u2, x));
        if u2.cpu_array[x as int] == u.cpu_array[x as int] && !cpu_outside(u, x) && u.cpu_array[x as int].current_thread is Some {
            let t = u.cpu_array[x as int].current_thread->Some_0;
            assert(u.thread_map.dom().contains(t));
            assert(u.thread_map[t].state == (ThreadState::RUNNING { cpu_id: x }));
            if index_valid(NUM_CPUS, d) && u.cpu_array[d as int].current_thread == Some(t) { assert(u.cpu_array[d as int] == u.cpu_array[d as int]); }
            if cur_thread(u, x).syscall_progress is Some || cur_thread(u, x).lock_state == (LockStateU::WriteLocked { writer: x }) {
                assert(held_by_other(u.thread_map[t].lock_state, d));
            }
        }
    };
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && x != d implies {
        &&& cpu_outside(u2, x) ==> !(u2.cpu_array[x as int].op is InStep)
        &&& !cpu_outside(u2, x) && u2.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u2, x).syscall_progress is None
    } by {
        assert(cpu_kept(u, u2, x));
        assert(u.cpu_array[x as int] == u.cpu_array[x as int]);
    };
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] x != d && in_kill(u2, x) implies kill_holds(u2, x) by {
        assert(cpu_kept(u, u2, x));
        assert(in_kill(u, x));
        kill_holds_at(u, x);
        let pp = kill_own(u, x);
        let tp = kill_target(u, x);
        let st = kill_stage(u, x);
        assert(cur_thread(u2, x) == cur_thread(u, x));
        assert(kill_target(u2, x) == tp && kill_stage(u2, x) == st && kill_own(u2, x) == pp);
        assert(held_by_other(u.process_map[pp].lock_state, d) && held_by_other(u.process_map[tp].lock_state, d));
        assert(proc_kview(u2.process_map[pp]) == proc_kview(u.process_map[pp]));
        assert(proc_kview(u2.process_map[tp]) == proc_kview(u.process_map[tp]));
        assert forall|q: RwLockProcessPtr| #![trigger u2.process_map[kill_target(u2, x)].uppertree_seq.contains(q)]
            u2.process_map.dom().contains(q) && u2.process_map[kill_target(u2, x)].uppertree_seq.contains(q) && u2.process_map[q].uppertree_seq.contains(pp)
            implies u2.process_map[q].killed && u2.process_map[q].lock_state == (LockStateU::WriteLocked { writer: x }) by {
            assert(u.process_map[tp].uppertree_seq.contains(q));
            assert(u.process_map[q].uppertree_seq.contains(pp));
            assert(held_by_other(u.process_map[q].lock_state, d));
            assert(proc_kview(u2.process_map[q]) == proc_kview(u.process_map[q]));
        };
        if st is Thread {
            let v = st->Thread_thread;
            assert(held_by_other(u.thread_map[v].lock_state, d));
        }
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed]
        u2.process_map.dom().contains(p) && u2.process_map[p].killed && u2.process_map[p].lock_state != (LockStateU::WriteLocked { writer: d }) implies {
            let w = u2.process_map[p].lock_state->WriteLocked_writer;
            &&& u2.process_map[p].lock_state is WriteLocked
            &&& in_kill(u2, w)
            &&& kill_on_path(u2, w, p)
        } by {
        assert(u.process_map[p].killed);
        let w = u.process_map[p].lock_state->WriteLocked_writer;
        assert(in_kill(u, w) && w != d);
        assert(cpu_kept(u, u2, w));
        assert(cur_thread(u2, w) == cur_thread(u, w));
        kill_holds_at(u, w);
        let tw = kill_target(u, w);
        assert(held_by_other(u.process_map[tw].lock_state, d));
        assert(proc_kview(u2.process_map[tw]) == proc_kview(u.process_map[tw]));
    };
}

/// A kill step that changes only the empty target's tables keeps pagetable lock consistency, VA progress, and the fill
/// quota.
pub proof fn kill_target_table_step_implies_table_invariants_kept(u: KernelU, u2: KernelU, d: CpuId, tp: RwLockProcessPtr)
    requires
        kernel_u_ownership_wf(u), pagetable_locks_consistent(u), table_ops_vas(u), fill_quota(u), others_kept(u, u2, d), !table_op(u, d), !table_op(u2, d),
        !table_sharer(u, d), !table_sharer(u2, d), sharer_children_held(u), kill_target_table_step(u, u2, d, tp),
    ensures pagetable_locks_consistent(u2), table_ops_vas(u2), fill_quota(u2),
{
    assert forall|x: CpuId| #![trigger other_cpu_unchanged(u, u2, x)] x != d implies other_cpu_unchanged(u, u2, x) by { if index_valid(NUM_CPUS, x) { assert(cpu_kept(u, u2, x)); } };
    if u.process_map[tp].owned_threads.len() == 0 {
        assert forall|c: CpuId| #![trigger table_op(u, c)] #![trigger table_sharer(u, c)] table_op(u, c) || table_sharer(u, c) implies table_proc(u, c) != tp by {
            table_op_implies_proc_has_thread(u, c);
        };
    }
    assert(table_unworked(u, tp));
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != tp {
            assert(table_view(u2, p) == table_view(u, p));
            assert(table_locks_held_by_ops_at(u, p));
            let lk = table_lock(u, p);
            if lk is WriteLocked && lk->WriteLocked_writer != d { assert(other_cpu_unchanged(u, u2, lk->WriteLocked_writer)); }
            assert forall|x: CpuId| #![trigger table_lock(u2, p).readers().contains(x)] table_lock(u2, p).readers().contains(x)
                implies reader_ok(u2, p, x) by {
                assert(table_lock(u, p).readers().contains(x));
                assert(other_cpu_unchanged(u, u2, x));
            };
            assert forall|w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)] table_windows(u2, p).dom().contains(w) implies window_held_by_op(u2, p, w) by {
                assert(table_windows(u, p).dom().contains(w) && window_held_by_op(u, p, w));
                let x = table_windows(u, p)[w]->WriteLocked_writer;
                if table_windows(u, p)[w] is WriteLocked { assert(other_cpu_unchanged(u, u2, x)); }
            };
        } else {
            assert(table_locks_held_by_ops_at(u, tp));
            assert forall|w: WindowVa| #![trigger table_windows(u2, tp).dom().contains(w)] table_windows(u2, tp).dom().contains(w) implies window_held_by_op(u2, tp, w) by {
                assert(table_windows(u, tp).dom().contains(w) && window_held_by_op(u, tp, w));
                assert(table_windows(u2, tp)[w] == table_windows(u, tp)[w]);
                if table_windows(u, tp)[w] is WriteLocked {
                    let h = table_windows(u, tp)[w]->WriteLocked_writer;
                    if table_op(u, h) || table_sharer(u, h) && table_proc(u, h) == tp { table_op_implies_proc_has_thread(u, h); }
                }
            };
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) && table_op_vas(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c) && cpu_kept(u, u2, c));
        assert(table_op(u, c) && table_op_holds_locks(u, c) && table_op_shape(u, c) && table_op_vas(u, c));
        assert(cur_thread(u2, c) == cur_thread(u, c));
        let p = table_proc(u, c);
        table_op_implies_proc_has_thread(u, c);
        assert(table_view(u2, p) == table_view(u, p));
        assert(u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k);
        assert(op_holds_range_windows(u2, c));
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) && sharer_vas(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c) && cpu_kept(u, u2, c));
        assert(table_sharer(u, c) && sharer_holds_tables(u, c) && sharer_vas(u, c));
        assert(cur_thread(u2, c) == cur_thread(u, c));
        let p = table_proc(u, c);
        table_op_implies_proc_has_thread(u, c);
        assert(table_view(u2, p) == table_view(u, p));
        assert(u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k);
        if sharer_child(u, c) is Some {
            let ch = sharer_child(u, c)->Some_0;
            assert(table_view(u2, ch) == table_view(u, ch));
            assert(u2.process_map[ch].pagetable->Some_0.mapping_4k == u.process_map[ch].pagetable->Some_0.mapping_4k);
        }
        assert(op_holds_range_windows(u2, c));
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) && table_filling(u2, c) implies fill_quota_at(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c) && cpu_kept(u, u2, c));
        assert(table_op(u, c));
        fill_quota_implies_fill_quota_at(u, c);
        table_op_implies_proc_has_thread(u, c);
        assert(table_view(u2, table_proc(u, c)) == table_view(u, table_proc(u, c)));
    };
}

/// Processes whose shape stays keep the process tree well formed, given that no thread becomes dangling.
pub proof fn proc_shapes_same_implies_processes_wf(u: KernelU, u2: KernelU)
    requires
        kernel_u_ownership_wf(u), processes_wf(u), u2.process_map.dom() == u.process_map.dom(),
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) ==> {
            &&& u2.process_map[p].parent == u.process_map[p].parent && u2.process_map[p].children == u.process_map[p].children
            &&& u2.process_map[p].uppertree_seq == u.process_map[p].uppertree_seq && u2.process_map[p].depth == u.process_map[p].depth
            &&& u2.process_map[p].owned_threads == u.process_map[p].owned_threads
            &&& !u2.process_map[p].zombie ==> u2.process_map[p].zombie == u.process_map[p].zombie && (u2.process_map[p].pagetable is Some) == (u.process_map[p].pagetable is Some)
            &&& u2.process_map[p].zombie && !u.process_map[p].zombie ==> u2.process_map[p].owned_threads.len() == 0
        },
        forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u.thread_map.dom().contains(t) ==> u2.thread_map[t].owning_proc == u.thread_map[t].owning_proc
            && (u2.thread_map[t].state is DANGLING ==> u.thread_map[t].state is DANGLING),
    ensures processes_wf(u2),
{
    reveal(kernel_u_process_threads_wf);
    assert forall|p: RwLockProcessPtr| #![trigger proc_wf_at(u2, p)] u2.process_map.dom().contains(p) implies proc_wf_at(u2, p) by {
        proc_wf_at_of(u, p);
        let b = u2.process_map[p];
        assert forall|ch: RwLockProcessPtr| #![trigger b.children.contains(ch)] b.children.contains(ch)
            implies u2.process_map.dom().contains(ch) && u2.process_map[ch].parent == Some(p) && u2.process_map[ch].uppertree_seq == b.uppertree_seq.push(p) by {
            assert(u.process_map[p].children.contains(ch));
        };
        assert forall|q: RwLockProcessPtr| #![trigger b.uppertree_seq.contains(q)] b.uppertree_seq.contains(q) && u2.process_map.dom().contains(q)
            implies u2.process_map[q].uppertree_seq.len() < b.uppertree_seq.len() by { assert(u.process_map[p].uppertree_seq.contains(q)); };
        assert forall|t: RwLockThreadPtr| #![trigger b.owned_threads.contains(t)] b.owned_threads.contains(t)
            implies !(u2.thread_map[t].state is DANGLING) && u2.thread_map[t].owning_proc == p by {
            assert(u.process_map[p].owned_threads.contains(t));
            assert(u.thread_map.dom().contains(t) && u.thread_map[t].owning_proc == p);
        };
    };
}
} // verus!

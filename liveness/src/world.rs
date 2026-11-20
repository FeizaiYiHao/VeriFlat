//! Round 5: the closed world of every syscall covered so far, and its two properties for a cpu inside a syscall: it is
//! never blocked (`world_inv_implies_never_blocked`), and it leaves within the per-call bound of its own steps
//! (`world_inv_conformant_fair_implies_leaves_within_call_bound`). Adding a syscall family means one file with its labels,
//! inside predicate, frame lemmas, call traces, and bound, plus one line in each dispatch below.
use vstd::prelude::*;
use crate::*;
use crate::trace::*;
use crate::pagetable_locks::*;
use crate::frame::*;
use crate::family_traced::*;
use crate::family_alloc::*;
use crate::family_new_thread::*;
use crate::family_cpu::*;
use crate::family_pci::*;
use crate::family_schedule::*;
use crate::family_env::*;
use crate::fill_quota::*;
use crate::family_split_merge::*;
use crate::family_kill::*;
use crate::kill_frame::*;
use crate::kill_steps::*;
use crate::kill_own::*;
use crate::kill_enabled::*;
use crate::family_new_process::*;
use crate::family_exit::*;
use crate::exit_own::*;
use crate::family_offline::*;
use crate::family_ipc::*;
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::syscall_cpu_offline_check_spec::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;
use veriflat_syscall_new_thread::syscall_new_thread::syscall_new_thread_spec::*;

verus! {
/// The labels of the world, one family per line.
pub open spec fn world_label(l: StepLabel) -> bool {
    ||| traced_label(l) // new_endpoint, alloc_quota_4k, mmap_4k, unmap_4k
    ||| alloc_label(l) // alloc_thread_quota_4k, alloc_quota_2m, alloc_thread_quota_2m, alloc_quota_1g, alloc_thread_quota_1g
    ||| new_thread_label(l) // new_thread, new_thread_with_endpoint
    ||| cpu_label(l) // cpu_offline_request, cpu_online, cpu_offline_request_child, cpu_online_child
    ||| pci_label(l) // pci_attach_dma, pci_claim
    ||| schedule_label(l) // schedule, rebalance_pull
    ||| split_merge_label(l) // split_2m, merge_2m
    ||| env_label(l) // trap entry, return, and divert, register changes, TLB and context-cache fills
    ||| kill_label(l) // kill_process without its five killed-thread reclaim steps (`kill_label`)
    ||| new_process_label(l) // new_process, new_process_with_endpoint, new_process_with_iommu_and_endpoint
    ||| exit_label(l) // thread_exit without its five killed-thread reclaim steps (`exit_label`)
    ||| offline_label(l) // cpu_offline_check
    ||| ipc_label(l) // ordinary IPC: block and rendezvous without a PCI payload
}

/// The liveness-side restrictions on world steps, each a clause U lacks (`u_gaps.md`): `offline_hold_at_rest` (G20) and
/// `new_process_depth_room` (G21).
pub open spec fn world_allowed(u: KernelU, l: StepLabel, d: CpuId) -> bool {
    offline_hold_at_rest(u, l, d) && new_process_depth_room(u, l, d)
}

/// `s2` follows `s` by the world step `s` records, from a well-formed state.
pub open spec fn world_step(s: Snap, s2: Snap) -> bool {
    kernel_u_ownership_wf(s.u) && world_label(s.label) && world_allowed(s.u, s.label, s.cpu) && labeled_step(s.label, s.u, s2.u, s.cpu)
}

/// Every step of `b` is a world step.
pub open spec fn world_behavior(b: Execution<Snap>) -> bool { forall|i: nat| #[trigger] world_step(b(i), b(i + 1)) }

/// `c` is inside a multi-step syscall of the world; the one-step families have no inside.
pub open spec fn in_world(u: KernelU, c: CpuId) -> bool { in_traced(u, c) || in_new_thread(u, c) || in_new_process(u, c) || in_offline_check(u, c) }

/// Some step of `c` inside a world syscall is enabled.
pub open spec fn world_next_pre(u: KernelU, c: CpuId) -> bool {
    traced_next_pre(u, c) || new_thread_finish_step_pre(u, c) || new_process_next_pre(u, c) || cpu_offline_check_release_step_pre(u, c)
}

pub open spec fn world_enabled(c: CpuId) -> spec_fn(KernelU) -> bool { |u: KernelU| in_world(u, c) && world_next_pre(u, c) }

/// Every cpu inside holds the locks of its syscall, and the pagetable locks are consistent.
pub open spec fn world_base_inv(u: KernelU) -> bool {
    new_endpoint_locks_held(u) && new_thread_locks_held(u) && new_process_locks_held(u) && pagetable_locks_consistent(u) && table_ops_vas(u)
        && fill_quota(u) && locked_cpus_in_step(u)
}

/// The world invariant: the base invariant and the kill invariants.
pub open spec fn world_inv(u: KernelU) -> bool { world_base_inv(u) && kill_world_inv(u) && exit_locks_held(u) }

/// No cpu is inside a syscall, every pagetable and window is unlocked, and no process is marked, as after boot.
pub open spec fn world_quiescent(u: KernelU) -> bool {
    (forall|x: CpuId| #![trigger u.cpu_array[x as int]] cpu_outside(u, x)) && pagetables_quiescent(u) && kill_quiescent(u)
}

pub proof fn world_quiescent_implies_world_inv(u: KernelU)
    requires world_quiescent(u),
    ensures world_inv(u),
{
    assert forall|c: CpuId| #![trigger table_sharer(u, c)] !table_sharer(u, c) by { if index_valid(NUM_CPUS, c) { assert(cpu_outside(u, c)); } };
    pagetables_quiescent_implies_locks_consistent(u);
    assert forall|c: CpuId| #![trigger u.cpu_array[c as int]] in_kill(u, c) implies kill_holds(u, c) by { assert(cpu_outside(u, c)); };
    assert forall|c: CpuId| #![trigger u.cpu_array[c as int]] in_exit(u, c) implies exit_holds(u, c) by { assert(cpu_outside(u, c)); };
    assert forall|x: CpuId| #![trigger u.cpu_array[x as int]] index_valid(NUM_CPUS, x) implies {
        &&& cpu_outside(u, x) ==> !(u.cpu_array[x as int].op is InStep)
        &&& !cpu_outside(u, x) && u.cpu_array[x as int].current_thread is Some ==> cur_thread(u, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u, x).syscall_progress is None
    } by { assert(cpu_outside(u, x)); };
}

/// A world step keeps every other cpu, and `d` is outside every syscall or inside the one of the step's family after it.
pub proof fn world_step_implies_others_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), world_inv(u), world_label(l), world_allowed(u, l, d), labeled_step(l, u, u2, d),
    ensures others_kept(u, u2, d), env_label(l) && !cpu_outside(u, d) ==> tlbs_only_changed(u, u2),
{
    if traced_label(l) { traced_step_implies_others_kept(u, u2, l, d); }
    else if alloc_label(l) { alloc_step_implies_frame(u, u2, l, d); }
    else if new_thread_label(l) { new_thread_step_implies_others_kept(u, u2, l, d); }
    else if cpu_label(l) { cpu_step_implies_frame(u, u2, l, d); }
    else if pci_label(l) { pci_step_implies_frame(u, u2, l, d); }
    else if schedule_label(l) { schedule_step_implies_frame(u, u2, l, d); }
    else if split_merge_label(l) { split_merge_step_implies_frame(u, u2, l, d); }
    else if kill_label(l) { kill_step_implies_kill_world_inv_kept(u, u2, l, d); }
    else if new_process_label(l) { new_process_step_implies_others_kept(u, u2, l, d); }
    else if exit_label(l) { exit_step_implies_kill_world_inv_kept(u, u2, l, d); }
    else if offline_label(l) { offline_step_implies_frame(u, u2, l, d); }
    else if ipc_label(l) { ipc_step_implies_frame(u, u2, l, d); }
    else { env_step_implies_frame(u, u2, l, d); }
}

/// Every write-locked cpu other than `d` is kept, and `d` is outside after the step or runs inside its kernel step.
proof fn op_in_step_kept_implies_locked_cpus_in_step(u: KernelU, u2: KernelU, d: CpuId)
    requires locked_cpus_in_step(u), others_kept(u, u2, d), op_in_step_kept(u, u2, d),
    ensures locked_cpus_in_step(u2),
{
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && !cpu_outside(u2, x) implies u2.cpu_array[x as int].op is InStep by {
        if x != d { assert(cpu_kept(u, u2, x)); } else { assert(u.cpu_array[d as int] == u.cpu_array[d as int]); }
    };
}

/// A step that changes only the TLBs keeps the base invariant.
proof fn tlbs_only_changed_implies_world_inv_kept(u: KernelU, u2: KernelU)
    requires world_base_inv(u), tlbs_only_changed(u, u2),
    ensures world_base_inv(u2),
{
    assert(u2.cpu_array == u.cpu_array && u2.thread_map == u.thread_map && u2.process_map == u.process_map);
    assert(u2.container_map == u.container_map && u2.endpoint_map == u.endpoint_map);
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        assert(pagetable_locks_consistent(u));
        assert(u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some);
        assert(table_present(u, p));
        assert(table_locks_held_by_ops_at(u, p));
        assert forall|w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)] table_windows(u2, p).dom().contains(w) implies window_held_by_op(u2, p, w) by {
            assert(table_windows(u, p).dom().contains(w) && window_held_by_op(u, p, w));
        };
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) && table_op_vas(u2, c) by {
        assert(table_op(u, c));
        assert(table_op_holds_locks(u, c) && table_op_shape(u, c) && table_op_vas(u, c));
        assert(op_holds_range_windows(u2, c));
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) && table_filling(u2, c) implies fill_quota_at(u2, c) by { assert(table_op(u, c)); };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) && sharer_vas(u2, c) && new_process_holds(u2, c) by {
        assert(table_sharer(u, c));
        assert(sharer_holds_tables(u, c) && sharer_vas(u, c) && new_process_holds(u, c));
        assert(op_holds_range_windows(u2, c));
    };
}

/// A step of a one-step family keeps the base invariant.
proof fn single_step_frame_implies_world_inv_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), world_base_inv(u), single_step_frame(u, u2, d), empty_held_procs_kept(u, u2, d),
    ensures world_base_inv(u2),
{
    op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
    object_locks_same_implies_foreign_holds_kept(u, u2, d);
    frame_implies_new_endpoint_locks_held_kept(u, u2, d);
    frame_implies_new_thread_locks_held_kept(u, u2, d);
    frame_implies_new_process_locks_held_kept(u, u2, d);
    tables_kept_implies_table_invariants_kept(u, u2, d);
    tables_kept_implies_fill_quota_kept(u, u2, d);
}

/// A kill step keeps the base invariant: the killer is outside every other syscall, and the tables are kept or change only
/// at the empty target.
proof fn kill_step_implies_world_base_inv_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), world_inv(u), kill_label(l), labeled_step(l, u, u2, d),
    ensures world_base_inv(u2), kill_world_inv(u2), others_kept(u, u2, d),
{
    kill_step_implies_kill_world_inv_kept(u, u2, l, d);
    assert(!table_op(u, d) && !table_op(u2, d) && !in_new_endpoint(u2, d) && !in_new_thread(u2, d) && !table_sharer(u, d) && !table_sharer(u2, d));
    frame_implies_new_endpoint_locks_held_kept(u, u2, d);
    frame_implies_new_thread_locks_held_kept(u, u2, d);
    kill_d_frame_implies_empty_held_procs_kept(u, u2, d);
    frame_implies_new_process_locks_held_kept(u, u2, d);
    new_process_locks_held_implies_sharer_children_held(u);
    op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
    if tables_kept(u, u2) && table_killer(u2, d) == table_killer(u, d) && (table_killer(u, d) ==> table_killer_proc(u2, d) == table_killer_proc(u, d)) {
        tables_kept_implies_table_invariants_kept(u, u2, d);
        tables_kept_implies_fill_quota_kept(u, u2, d);
    } else {
        kill_target_table_step_implies_table_invariants_kept(u, u2, d, kill_target(u, d));
    }
}

/// An exit step keeps the base invariant: the exiting cpu is outside every other syscall, and the tables are kept or
/// change only at its own process.
proof fn exit_step_implies_world_base_inv_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), world_inv(u), exit_label(l), labeled_step(l, u, u2, d),
    ensures world_base_inv(u2), kill_world_inv(u2), exit_locks_held(u2), others_kept(u, u2, d),
{
    exit_step_implies_kill_world_inv_kept(u, u2, l, d);
    assert(!table_op(u, d) && !table_op(u2, d) && !in_new_endpoint(u2, d) && !in_new_thread(u2, d) && !table_sharer(u, d) && !table_sharer(u2, d));
    frame_implies_new_endpoint_locks_held_kept(u, u2, d);
    frame_implies_new_thread_locks_held_kept(u, u2, d);
    kill_d_frame_implies_empty_held_procs_kept(u, u2, d);
    frame_implies_new_process_locks_held_kept(u, u2, d);
    new_process_locks_held_implies_sharer_children_held(u);
    op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
    if tables_kept(u, u2) && table_killer(u2, d) == table_killer(u, d) && (table_killer(u, d) ==> table_killer_proc(u2, d) == table_killer_proc(u, d)) {
        tables_kept_implies_table_invariants_kept(u, u2, d);
        tables_kept_implies_fill_quota_kept(u, u2, d);
    } else {
        kill_target_table_step_implies_table_invariants_kept(u, u2, d, u.cpu_array[d as int].current_process->Some_0);
    }
}

/// Every world step keeps the world invariant.
pub proof fn world_step_implies_world_inv_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), world_inv(u), world_label(l), world_allowed(u, l, d), labeled_step(l, u, u2, d),
    ensures world_inv(u2),
{
    if kill_label(l) {
        kill_step_implies_world_base_inv_kept(u, u2, l, d);
        kill_step_implies_kill_world_inv_kept(u, u2, l, d);
        kill_d_frame_implies_held_procs_kept(u, u2, d);
        assert(!in_exit(u2, d));
        frame_implies_exit_locks_held_kept(u, u2, d);
        return;
    }
    if exit_label(l) {
        exit_step_implies_world_base_inv_kept(u, u2, l, d);
        return;
    }
    world_step_implies_others_kept(u, u2, l, d);
    if traced_label(l) {
        traced_step_implies_new_endpoint_locks_held_kept(u, u2, l, d);
        traced_step_implies_others_kept(u, u2, l, d);
        traced_step_implies_foreign_holds_kept(u, u2, l, d);
        frame_implies_new_thread_locks_held_kept(u, u2, d);
        traced_step_implies_pagetable_locks_consistent_kept(u, u2, l, d);
        traced_step_implies_table_ops_vas_kept(u, u2, l, d);
        traced_step_implies_fill_quota_kept(u, u2, l, d);
        op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
        traced_step_implies_kill_frame(u, u2, l, d);
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        frame_implies_new_process_locks_held_kept(u, u2, d);
        kill_frame_implies_held_procs_kept(u, u2, d);
        assert(!in_exit(u2, d));
        frame_implies_exit_locks_held_kept(u, u2, d);
    } else if env_label(l) {
        env_step_implies_frame(u, u2, l, d);
        env_step_implies_kill_frame(u, u2, l, d);
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        if cpu_outside(u, d) { single_step_frame_implies_world_inv_kept(u, u2, d); } else { tlbs_only_changed_implies_world_inv_kept(u, u2); }
        kill_frame_implies_held_procs_kept(u, u2, d);
        if !cpu_outside(u, d) {
            assert(u2.cpu_array == u.cpu_array && u2.thread_map == u.thread_map && u2.process_map == u.process_map);
            assert(u2.container_map == u.container_map && u2.endpoint_map == u.endpoint_map);
            if in_exit(u, d) { exit_holds_at(u, d); }
        }
        object_locks_same_implies_foreign_holds_kept(u, u2, d);
        frame_implies_exit_locks_held_kept(u, u2, d);
    } else if offline_label(l) {
        offline_step_implies_frame(u, u2, l, d);
        op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
        object_locks_same_implies_foreign_holds_kept(u, u2, d);
        assert(!in_new_endpoint(u2, d) && !in_new_thread(u2, d) && !in_new_process(u2, d) && !in_exit(u2, d) && !table_op(u, d) && !table_op(u2, d));
        assert(!table_sharer(u, d) && !table_sharer(u2, d) && !table_killer(u, d) && !table_killer(u2, d));
        frame_implies_new_endpoint_locks_held_kept(u, u2, d);
        frame_implies_new_thread_locks_held_kept(u, u2, d);
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        frame_implies_new_process_locks_held_kept(u, u2, d);
        tables_kept_implies_table_invariants_kept(u, u2, d);
        tables_kept_implies_fill_quota_kept(u, u2, d);
        kill_frame_implies_held_procs_kept(u, u2, d);
        frame_implies_exit_locks_held_kept(u, u2, d);
    } else if new_process_label(l) {
        new_process_step_implies_others_kept(u, u2, l, d);
        op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
        new_process_step_implies_frame(u, u2, l, d);
        frame_implies_new_endpoint_locks_held_kept(u, u2, d);
        frame_implies_new_thread_locks_held_kept(u, u2, d);
        new_process_step_implies_kill_frame(u, u2, l, d);
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        frame_implies_new_process_locks_held_kept(u, u2, d);
        new_process_step_implies_table_invariants_kept(u, u2, l, d);
        kill_frame_implies_held_procs_kept(u, u2, d);
        assert(!in_exit(u2, d));
        frame_implies_exit_locks_held_kept(u, u2, d);
    } else if new_thread_label(l) {
        new_thread_step_implies_others_kept(u, u2, l, d);
        op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
        new_thread_step_implies_frame(u, u2, l, d);
        frame_implies_new_endpoint_locks_held_kept(u, u2, d);
        frame_implies_new_thread_locks_held_kept(u, u2, d);
        tables_kept_implies_table_invariants_kept(u, u2, d);
        tables_kept_implies_fill_quota_kept(u, u2, d);
        new_thread_step_implies_kill_frame(u, u2, l, d);
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        frame_implies_new_process_locks_held_kept(u, u2, d);
        kill_frame_implies_held_procs_kept(u, u2, d);
        assert(!in_exit(u2, d));
        frame_implies_exit_locks_held_kept(u, u2, d);
    } else if split_merge_label(l) {
        split_merge_step_implies_frame(u, u2, l, d);
        op_in_step_kept_implies_locked_cpus_in_step(u, u2, d);
        object_locks_same_implies_foreign_holds_kept(u, u2, d);
        frame_implies_new_endpoint_locks_held_kept(u, u2, d);
        frame_implies_new_thread_locks_held_kept(u, u2, d);
        tables_kept_implies_table_invariants_kept(u, u2, d);
        tables_kept_implies_fill_quota_kept(u, u2, d);
        split_merge_step_implies_kill_frame(u, u2, l, d);
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        frame_implies_new_process_locks_held_kept(u, u2, d);
        kill_frame_implies_held_procs_kept(u, u2, d);
        assert(!in_exit(u2, d));
        frame_implies_exit_locks_held_kept(u, u2, d);
    } else {
        if alloc_label(l) { alloc_step_implies_frame(u, u2, l, d); alloc_step_implies_kill_frame(u, u2, l, d); }
        else if cpu_label(l) { cpu_step_implies_frame(u, u2, l, d); cpu_step_implies_kill_frame(u, u2, l, d); }
        else if pci_label(l) { pci_step_implies_frame(u, u2, l, d); pci_step_implies_kill_frame(u, u2, l, d); }
        else if ipc_label(l) { ipc_step_implies_frame(u, u2, l, d); }
        else { schedule_step_implies_frame(u, u2, l, d); schedule_step_implies_kill_frame(u, u2, l, d); }
        kill_frame_implies_empty_held_procs_kept(u, u2, d);
        single_step_frame_implies_world_inv_kept(u, u2, d);
        object_locks_same_implies_foreign_holds_kept(u, u2, d);
        kill_frame_implies_held_procs_kept(u, u2, d);
        assert(!in_exit(u2, d));
        frame_implies_exit_locks_held_kept(u, u2, d);
    }
    kill_frame_implies_kill_world_inv_kept(u, u2, d);
}

/// The world invariant at `i` holds at every later index of a world behaviour.
pub proof fn world_behavior_implies_world_inv_kept(b: Execution<Snap>, i: nat, k: nat)
    requires world_behavior(b), i <= k, world_inv(b(i).u),
    ensures world_inv(b(k).u),
    decreases k - i,
{
    if k > i {
        let j = (k - 1) as nat;
        world_behavior_implies_world_inv_kept(b, i, j);
        assert(world_step(b(j), b(j + 1)));
        world_step_implies_world_inv_kept(b(j).u, b(k).u, b(j).label, b(j).cpu);
    }
}

/// Property (a), never blocked: under the world invariant a cpu inside a world syscall has an enabled next step.
pub proof fn world_inv_implies_never_blocked(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), world_inv(u), in_world(u, c),
    ensures world_next_pre(u, c),
{
    if in_offline_check(u, c) { in_offline_check_implies_release_enabled(u, c); }
    else if in_new_endpoint(u, c) { new_endpoint_locks_held_implies_finish_enabled(u, c); }
    else if in_unmap_4k(u, c) { table_invariants_implies_unmap_4k_never_blocked(u, c); }
    else if in_mmap_4k(u, c) { table_invariants_implies_mmap_4k_never_blocked(u, c); }
    else if in_new_thread(u, c) { new_thread_locks_held_implies_finish_enabled(u, c); }
    else { new_process_invariants_implies_next_pre(u, c); }
}

/// Property (a) over a behaviour from a quiescent start.
pub proof fn world_quiescent_behavior_implies_never_blocked(b: Execution<Snap>, k: nat, c: CpuId)
    requires world_behavior(b), world_quiescent(b(0).u), in_world(b(k).u, c),
    ensures world_next_pre(b(k).u, c),
{
    world_quiescent_implies_world_inv(b(0).u);
    world_behavior_implies_world_inv_kept(b, 0, k);
    assert(world_step(b(k), b(k + 1)));
    world_inv_implies_never_blocked(b(k).u, c);
}

/// Property (a) for `kill_process` over a behaviour from a quiescent start: a cpu inside a kill whose wanted locks are free
/// has an enabled kill step.
pub proof fn world_quiescent_behavior_implies_kill_never_blocked(b: Execution<Snap>, k: nat, c: CpuId)
    requires world_behavior(b), world_quiescent(b(0).u), in_kill(b(k).u, c), kill_wanted_free(b(k).u, c),
    ensures kill_enabled(b(k).u, c),
{
    world_quiescent_implies_world_inv(b(0).u);
    world_behavior_implies_world_inv_kept(b, 0, k);
    assert(world_step(b(k), b(k + 1)));
    kill_world_inv_wanted_free_implies_kill_enabled(b(k).u, c);
}

/// Property (a) for `thread_exit` over a behaviour from a quiescent start: an exiting cpu whose wanted objects are free,
/// and whose next endpoint, if any, can be dropped or released, has an enabled exit step.
pub proof fn world_quiescent_behavior_implies_exit_never_blocked(b: Execution<Snap>, k: nat, c: CpuId)
    requires world_behavior(b), world_quiescent(b(0).u), in_exit(b(k).u, c), exit_wanted_free(b(k).u, c), exit_endpoint_room(b(k).u, c),
    ensures exit_enabled(b(k).u, c),
{
    world_quiescent_implies_world_inv(b(0).u);
    world_behavior_implies_world_inv_kept(b, 0, k);
    assert(world_step(b(k), b(k + 1)));
    exit_holds_at(b(k).u, c);
    exit_holds_wanted_free_implies_enabled(b(k).u, c);
}

/// One world syscall invocation with its arguments, by family.
pub ghost enum WorldCall {
    Traced(PilotCall), Alloc(AllocCall), NewThread(NewThreadCall), Cpu(CpuCall), Pci(PciCall), Schedule(ScheduleCall), SplitMerge(SplitMergeCall), NewProcess(NewProcessCall),
    Offline(OfflineCall), Ipc(IpcCall),
}

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it.
pub open spec fn world_call_trace_ok(call: WorldCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    match call {
        WorldCall::Traced(x) => call_trace_ok(x, t, c),
        WorldCall::Alloc(x) => alloc_call_trace_ok(x, t, c),
        WorldCall::NewThread(x) => new_thread_call_trace_ok(x, t, c),
        WorldCall::Cpu(x) => cpu_call_trace_ok(x, t, c),
        WorldCall::Pci(x) => pci_call_trace_ok(x, t, c),
        WorldCall::Schedule(x) => schedule_call_trace_ok(x, t, c),
        WorldCall::SplitMerge(x) => split_merge_call_trace_ok(x, t, c),
        WorldCall::NewProcess(x) => new_process_call_trace_ok(x, t, c),
        WorldCall::Offline(x) => offline_call_trace_ok(x, t, c),
        WorldCall::Ipc(x) => ipc_call_trace_ok(x, t, c),
    }
}

/// The most own steps one invocation of `call` records.
pub open spec fn world_call_bound(call: WorldCall) -> nat {
    match call {
        WorldCall::Traced(x) => call_bound(x),
        WorldCall::Alloc(x) => alloc_call_bound(x),
        WorldCall::NewThread(x) => new_thread_call_bound(x),
        WorldCall::Cpu(x) => cpu_call_bound(x),
        WorldCall::Pci(x) => pci_call_bound(x),
        WorldCall::Schedule(x) => schedule_call_bound(x),
        WorldCall::SplitMerge(x) => split_merge_call_bound(x),
        WorldCall::NewProcess(x) => new_process_call_bound(x),
        WorldCall::Offline(x) => offline_call_bound(x),
        WorldCall::Ipc(x) => ipc_call_bound(x),
    }
}

pub proof fn world_call_trace_ok_implies_len_bounded(call: WorldCall, t: Seq<KernelStep>, c: CpuId)
    requires world_call_trace_ok(call, t, c),
    ensures t.len() <= world_call_bound(call),
{
    match call {
        WorldCall::Traced(x) => call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::Alloc(x) => alloc_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::NewThread(x) => new_thread_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::Cpu(x) => cpu_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::Pci(x) => pci_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::Schedule(x) => schedule_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::SplitMerge(x) => split_merge_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::NewProcess(x) => new_process_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::Offline(x) => offline_call_trace_ok_implies_len_bounded(x, t, c),
        WorldCall::Ipc(x) => ipc_call_trace_ok_implies_len_bounded(x, t, c),
    }
}

/// `p` is a prefix of a complete trace of `call` on `c`.
pub open spec fn world_call_prefix_ok(call: WorldCall, p: Seq<KernelStep>, c: CpuId) -> bool {
    exists|t: Seq<KernelStep>| #[trigger] world_call_trace_ok(call, t, c) && p.len() <= t.len() && p == t.subrange(0, p.len() as int)
}

/// What a step of another cpu must leave alone for `c` inside a world syscall: its cpu entry, and its running thread when
/// that records progress or `c` write-holds it; a cpu inside the offline check holds no thread, which other cpus may lock.
pub open spec fn world_slice(u: KernelU, c: CpuId) -> (CpuU, Option<ThreadU>) {
    (u.cpu_array[c as int], if u.cpu_array[c as int].current_thread is Some && (cur_thread(u, c).syscall_progress is Some || cur_thread(u, c).lock_state == (LockStateU::WriteLocked { writer: c })) { Some(cur_thread(u, c)) } else { None })
}

/// Index `k` is a syscall step of `c`: `c` takes it and it is no environment event.
pub open spec fn call_step(b: Execution<Snap>, c: CpuId, k: nat) -> bool { b(k).cpu == c && !env_label(b(k).label) }

/// The syscall steps of `c` at the indices `i..j` as a trace.
pub open spec fn call_trace(b: Execution<Snap>, c: CpuId, i: nat, j: nat) -> Seq<KernelStep>
    decreases j - i,
{
    if j <= i { Seq::empty() }
    else {
        let k = (j - 1) as nat;
        call_trace(b, c, i, k) + if call_step(b, c, k) { seq![KernelStep { old_u: b(k).u, new_u: b(j).u }] } else { Seq::empty() }
    }
}

/// The number of syscall steps of `c` at the indices `i..j`.
pub open spec fn call_steps(b: Execution<Snap>, c: CpuId, i: nat, j: nat) -> nat
    decreases j - i,
{
    if j <= i { 0 } else { call_steps(b, c, i, (j - 1) as nat) + if call_step(b, c, (j - 1) as nat) { 1nat } else { 0nat } }
}

pub proof fn call_trace_len_implies_call_steps(b: Execution<Snap>, c: CpuId, i: nat, j: nat)
    ensures call_trace(b, c, i, j).len() == call_steps(b, c, i, j),
    decreases j - i,
{ if j > i { call_trace_len_implies_call_steps(b, c, i, (j - 1) as nat); } }

pub proof fn no_call_step_implies_call_steps_zero(b: Execution<Snap>, c: CpuId, i: nat, j: nat)
    requires forall|k: nat| #![trigger b(k)] i <= k < j ==> !call_step(b, c, k),
    ensures call_steps(b, c, i, j) == 0,
    decreases j - i,
{ if j > i { no_call_step_implies_call_steps_zero(b, c, i, (j - 1) as nat); } }

pub proof fn call_steps_split_implies_sum(b: Execution<Snap>, c: CpuId, i: nat, j: nat, k: nat)
    requires i <= j <= k,
    ensures call_steps(b, c, i, k) == call_steps(b, c, i, j) + call_steps(b, c, j, k),
    decreases k - j,
{ if k > j { call_steps_split_implies_sum(b, c, i, j, (k - 1) as nat); } }

/// Labels that are syscall steps.
pub open spec fn call_label() -> spec_fn(StepLabel) -> bool { |l: StepLabel| !env_label(l) }

/// The syscall steps of `c` from its entry step at `e`, while it stays inside a world syscall, are a prefix of one complete
/// trace of `call`; environment events that `c` takes meanwhile, TLB fills, are not part of the call.
pub open spec fn world_invocation_conformant(b: Execution<Snap>, c: CpuId, call: WorldCall, e: nat) -> bool {
    forall|j: nat| #![trigger call_trace(b, c, e, j)]
        e < j && (forall|k: nat| #![trigger b(k)] e < k < j ==> in_world(b(k).u, c)) ==> world_call_prefix_ok(call, call_trace(b, c, e, j), c)
}

/// Some step of `c` is enabled at every index from `i` at which `c` is inside a world syscall.
pub open spec fn world_never_blocked_from(b: Execution<Snap>, c: CpuId, i: nat) -> bool {
    forall|k: nat| #![trigger b(k)] i <= k && in_world(b(k).u, c) ==> world_next_pre(b(k).u, c)
}

/// A world step that is not a syscall step of `c`, a step of another cpu or an environment event, keeps the cpu entry and
/// running thread of `c` inside a world syscall.
pub proof fn world_noncall_step_implies_cpu_slice_unchanged(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, c: CpuId)
    requires kernel_u_ownership_wf(u), world_inv(u), world_label(l), world_allowed(u, l, d), labeled_step(l, u, u2, d), in_world(u, c), d != c || env_label(l),
    ensures world_slice(u2, c) == world_slice(u, c),
{
    world_step_implies_others_kept(u, u2, l, d);
    if d != c { assert(cpu_kept(u, u2, c)); } else { assert(u2.cpu_array == u.cpu_array && u2.thread_map == u.thread_map); }
}

/// While `c` stays inside after entering `call` at `e`, it has taken at most `world_call_bound(call)` syscall steps since `e`.
pub proof fn world_invocation_conformant_implies_call_steps_bounded(b: Execution<Snap>, c: CpuId, call: WorldCall, e: nat, j: nat)
    requires world_invocation_conformant(b, c, call, e), e < j, forall|k: nat| #![trigger b(k)] e < k < j ==> in_world(b(k).u, c),
    ensures call_steps(b, c, e, j) <= world_call_bound(call),
{
    assert(world_call_prefix_ok(call, call_trace(b, c, e, j), c));
    let t = choose|t: Seq<KernelStep>| #[trigger] world_call_trace_ok(call, t, c) && call_trace(b, c, e, j).len() <= t.len()
        && call_trace(b, c, e, j) == t.subrange(0, call_trace(b, c, e, j).len() as int);
    world_call_trace_ok_implies_len_bounded(call, t, c);
    call_trace_len_implies_call_steps(b, c, e, j);
}

/// From `t`, while `c` has taken no syscall step since `i` and its slice is the one at `i`, weak fairness finds the first
/// syscall step of `c` at or after `t`.
proof fn world_fair_enabled_slice_implies_first_call_step(b: Execution<Snap>, c: CpuId, fair: spec_fn(nat) -> nat, i: nat, t: nat) -> (s: nat)
    requires
        world_behavior(b), in_world(b(i).u, c), i <= t <= fair(i), weakly_fair_witness(b, c, world_enabled(c), call_label(), fair),
        forall|k: nat| #![trigger b(k)] i <= k ==> world_inv(b(k).u),
        forall|k: nat| #![trigger b(k)] i <= k && world_slice(b(k).u, c) == world_slice(b(i).u, c) ==> world_next_pre(b(k).u, c),
        forall|k: nat| #![trigger b(k)] i <= k < t ==> !call_step(b, c, k) && world_slice(b(k).u, c) == world_slice(b(i).u, c),
        world_slice(b(t).u, c) == world_slice(b(i).u, c),
    ensures
        t <= s <= fair(i), call_step(b, c, s), world_slice(b(s).u, c) == world_slice(b(i).u, c), in_world(b(s).u, c),
        forall|k: nat| #![trigger b(k)] i <= k < s ==> !call_step(b, c, k) && world_slice(b(k).u, c) == world_slice(b(i).u, c),
    decreases fair(i) - t,
{
    assert(in_world(b(t).u, c));
    if call_step(b, c, t) { t }
    else {
        assert(fair(i) == fair(i));
        assert(t < fair(i)) by { if t == fair(i) { assert(world_next_pre(b(t).u, c)); } };
        assert(world_step(b(t), b(t + 1)) && world_inv(b(t).u));
        world_noncall_step_implies_cpu_slice_unchanged(b(t).u, b(t + 1).u, b(t).label, b(t).cpu, c);
        world_fair_enabled_slice_implies_first_call_step(b, c, fair, i, t + 1)
    }
}

/// Property (b), bounded own steps: a cpu `c` that entered `call` at `e`, conforms to the call's trace specification, is
/// inside from `e + 1` to `i`, is never blocked from `i`, and is weakly fair for syscall steps, leaves at the returned `s`
/// within `world_call_bound(call)` syscall steps since `e`, staying inside from `i` to `s`.
pub proof fn world_conformant_never_blocked_fair_implies_leaves_within_call_bound(b: Execution<Snap>, c: CpuId, call: WorldCall, e: nat,
    fair: spec_fn(nat) -> nat, i: nat) -> (s: nat)
    requires
        world_behavior(b), world_inv(b(i).u), world_invocation_conformant(b, c, call, e), e < i,
        forall|k: nat| #![trigger b(k)] e < k <= i ==> in_world(b(k).u, c), world_never_blocked_from(b, c, i),
        weakly_fair_witness(b, c, world_enabled(c), call_label(), fair),
    ensures
        i <= s, call_step(b, c, s), !in_world(b(s + 1).u, c), call_steps(b, c, e, s + 1) <= world_call_bound(call),
        forall|k: nat| #![trigger b(k)] i <= k <= s ==> in_world(b(k).u, c),
    decreases world_call_bound(call) - call_steps(b, c, e, i),
{
    world_invocation_conformant_implies_call_steps_bounded(b, c, call, e, i);
    assert forall|k: nat| #![trigger b(k)] i <= k implies world_inv(b(k).u) by { world_behavior_implies_world_inv_kept(b, i, k); };
    assert forall|k: nat| #![trigger b(k)] i <= k && world_slice(b(k).u, c) == world_slice(b(i).u, c) implies world_next_pre(b(k).u, c) by { assert(in_world(b(k).u, c)); };
    let s0 = world_fair_enabled_slice_implies_first_call_step(b, c, fair, i, i);
    assert forall|k: nat| #![trigger b(k)] e < k < s0 + 1 implies in_world(b(k).u, c) by { if k > i { assert(world_slice(b(k).u, c) == world_slice(b(i).u, c)); } };
    world_invocation_conformant_implies_call_steps_bounded(b, c, call, e, s0 + 1);
    no_call_step_implies_call_steps_zero(b, c, i, s0);
    call_steps_split_implies_sum(b, c, e, i, s0);
    if !in_world(b(s0 + 1).u, c) {
        assert forall|k: nat| #![trigger b(k)] i <= k <= s0 implies in_world(b(k).u, c) by { assert(world_slice(b(k).u, c) == world_slice(b(i).u, c)); };
        s0
    } else {
        assert forall|k: nat| #![trigger b(k)] e < k <= s0 + 1 implies in_world(b(k).u, c) by { if k > i && k <= s0 { assert(world_slice(b(k).u, c) == world_slice(b(i).u, c)); } };
        assert(world_inv(b(s0 + 1).u));
        let s = world_conformant_never_blocked_fair_implies_leaves_within_call_bound(b, c, call, e, fair, s0 + 1);
        assert forall|k: nat| #![trigger b(k)] i <= k <= s implies in_world(b(k).u, c) by { if k <= s0 { assert(world_slice(b(k).u, c) == world_slice(b(i).u, c)); } };
        s
    }
}

/// Properties (a) and (b) together from a quiescent start: a cpu `c` weakly fair for syscall steps that entered `call` at
/// `e`, conforms to the call's trace specification, and is inside from `e + 1` to `i`, leaves within
/// `world_call_bound(call)` syscall steps since `e`.
pub proof fn world_quiescent_conformant_fair_implies_leaves_within_call_bound(b: Execution<Snap>, c: CpuId, call: WorldCall, e: nat,
    fair: spec_fn(nat) -> nat, i: nat) -> (s: nat)
    requires
        world_behavior(b), world_quiescent(b(0).u), world_invocation_conformant(b, c, call, e), e < i,
        forall|k: nat| #![trigger b(k)] e < k <= i ==> in_world(b(k).u, c),
        weakly_fair_witness(b, c, world_enabled(c), call_label(), fair),
    ensures i <= s, call_step(b, c, s), !in_world(b(s + 1).u, c), call_steps(b, c, e, s + 1) <= world_call_bound(call),
{
    assert forall|k: nat| #![trigger b(k)] i <= k && in_world(b(k).u, c) implies world_next_pre(b(k).u, c) by {
        world_quiescent_behavior_implies_never_blocked(b, k, c);
    };
    world_quiescent_implies_world_inv(b(0).u);
    world_behavior_implies_world_inv_kept(b, 0, i);
    world_conformant_never_blocked_fair_implies_leaves_within_call_bound(b, c, call, e, fair, i)
}
} // verus!

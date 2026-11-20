//! Round 10: every `thread_exit` step in the world keeps the world invariants. An exit step of `d` touches only objects that
//! are unlocked or that `d` write-holds (`kill_d_frame`), and its own facts are proved per step.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_kill::*;
use crate::kill_steps::*;
use crate::kill_own::*;
use crate::family_exit::*;
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;

verus! {
/// The tables after an exit step: kept, or changed only at the exiting cpu's own process.
pub open spec fn exit_table_post(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    ||| tables_kept(u, u2) && table_killer(u2, d) == table_killer(u, d) && (table_killer(u, d) ==> table_killer_proc(u2, d) == table_killer_proc(u, d))
    ||| kill_target_table_step(u, u2, d, u.cpu_array[d as int].current_process->Some_0)
}

/// What an exit step of `d` proves of `d` itself: its frame, its holds, that it holds no marked process, the thread and
/// process facts, and its cpu's mode.
pub open spec fn exit_own_post(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& kill_d_frame(u, u2, d)
    &&& in_exit(u2, d) ==> exit_holds(u2, d)
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed] u2.process_map.dom().contains(p) && u2.process_map[p].killed
        ==> u2.process_map[p].lock_state != (LockStateU::WriteLocked { writer: d })
    &&& threads_wf(u2)
    &&& processes_wf(u2)
    &&& cpu_outside(u2, d) ==> !(u2.cpu_array[d as int].op is InStep)
    &&& !cpu_outside(u2, d) ==> in_exit(u2, d)
    &&& op_in_step_kept(u, u2, d)
    &&& cpu_outside(u, d) || in_exit(u, d)
    &&& exit_table_post(u, u2, d)
}

/// A middle exit step starts from a cpu inside `thread_exit` that holds what its stage needs and holds no marked process.
proof fn exit_middle_pre(u: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), in_exit(u, d),
    ensures
        exit_holds(u, d), !table_op(u, d), !table_sharer(u, d), u.thread_map.dom().contains(u.cpu_array[d as int].current_thread->Some_0),
        u.container_map.dom().contains(u.cpu_array[d as int].owning_container),
        u.process_map[cur_thread(u, d).owning_proc].owned_threads.contains(u.cpu_array[d as int].current_thread->Some_0),
        thread_wf_at(cur_thread(u, d)),
        forall|p: RwLockProcessPtr| #![trigger u.process_map[p].killed] u.process_map.dom().contains(p) && u.process_map[p].killed
            ==> u.process_map[p].lock_state != (LockStateU::WriteLocked { writer: d }),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    exit_holds_at(u, d);
    assert(u.cpu_array[d as int] == u.cpu_array[d as int]);
    assert(!in_kill(u, d));
}

/// The killed-process fact of `u` for a cpu outside every kill.
proof fn not_killer_implies_no_killed_held(u: KernelU, d: CpuId)
    requires kill_world_inv(u), !in_kill(u, d),
    ensures
        forall|p: RwLockProcessPtr| #![trigger u.process_map[p].killed] u.process_map.dom().contains(p) && u.process_map[p].killed
            ==> u.process_map[p].lock_state != (LockStateU::WriteLocked { writer: d }),
{}

proof fn exit_enter_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), labeled_step(StepLabel::ThreadExitEnter, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); reveal(kernel_u_cpu_ownership_wf);
    let cpu = u.cpu_array[d as int];
    let td = cpu.current_thread->Some_0;
    let t = u.thread_map[td];
    let pd = cpu.current_process->Some_0;
    assert(u.cpu_array[d as int] == u.cpu_array[d as int]);
    assert(cpu_outside(u, d) && !in_kill(u, d));
    not_killer_implies_no_killed_held(u, d);
    if t.caller is Some { assert(t.caller->Some_0 != td); }
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_exit(u2, d) && cur_thread(u2, d).caller is None && cur_thread(u2, d).owning_proc == pd);
    assert(exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_drop_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitDrop, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_drop_step_pre); reveal(thread_exit_drop_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    let t = u.thread_map[td];
    let next = t.syscall_progress->Some_0->ThreadExit_next;
    let index = (u2.thread_map[td].syscall_progress->Some_0->ThreadExit_next - 1) as EndpointIdx;
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_exit(u2, d) && cur_thread(u2, d) == u2.thread_map[td]);
    assert(u2.thread_map[td].endpoint_descriptors == t.endpoint_descriptors.update(index as int, None));
    assert forall|j: int| #![trigger u2.thread_map[td].endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS && j < index + 1
        implies u2.thread_map[td].endpoint_descriptors[j] is None by {
        if j < next { assert(t.endpoint_descriptors[j] is None); } else if j < index { assert(t.endpoint_descriptors[j] is None); }
    };
    assert(exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_release_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitRelease, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_drop_step_pre); reveal(thread_exit_release_step); reveal(kernel_u_endpoint_released);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    let t = u.thread_map[td];
    let next = t.syscall_progress->Some_0->ThreadExit_next;
    let index = (u2.thread_map[td].syscall_progress->Some_0->ThreadExit_next - 1) as EndpointIdx;
    let ctn = u.cpu_array[d as int].owning_container;
    assert(u2.process_map == u.process_map && u2.cpu_array == u.cpu_array && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(u2.container_map[ctn].lock_state == u.container_map[ctn].lock_state);
    assert(in_exit(u2, d) && cur_thread(u2, d) == u2.thread_map[td]);
    assert(u2.thread_map[td].endpoint_descriptors == t.endpoint_descriptors.update(index as int, None));
    assert forall|j: int| #![trigger u2.thread_map[td].endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS && j < index + 1
        implies u2.thread_map[td].endpoint_descriptors[j] is None by {
        if j < next { assert(t.endpoint_descriptors[j] is None); } else if j < index { assert(t.endpoint_descriptors[j] is None); }
    };
    assert(exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_lock_table_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitLockTable, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_lock_table_step_pre); reveal(thread_exit_lock_table_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    let pd = u.thread_map[td].owning_proc;
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_exit(u2, d) && cur_thread(u2, d) == u2.thread_map[td]);
    assert(exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    sole_thread_implies_table_unworked(u, d, pd);
    assert(table_killer(u2, d) && table_killer_proc(u2, d) == pd);
    assert(kill_target_table_step(u, u2, d, pd));
}

proof fn exit_table_hidden_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitTableHidden, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_reclaim_step_pre); reveal(process_table_hidden_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    let pd = u.thread_map[td].owning_proc;
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map == u.thread_map);
    assert(in_exit(u2, d) && exit_holds(u2, d));
    proc_shapes_same_implies_processes_wf(u, u2);
    sole_thread_implies_table_unworked(u, d, pd);
    assert(table_killer(u2, d) && table_killer_proc(u2, d) == pd);
    assert(kill_target_table_step(u, u2, d, pd));
}

proof fn exit_tlb_flush_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitTlbFlush, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    assert(u2.process_map == u.process_map && u2.thread_map == u.thread_map && u2.cpu_array == u.cpu_array);
    assert(u2.container_map.dom() =~= u.container_map.dom());
    assert(in_exit(u2, d) && exit_holds(u2, d));
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_flushed_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitFlushed, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_flushed_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    assert(u2.process_map == u.process_map && u2.cpu_array == u.cpu_array && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_exit(u2, d) && cur_thread(u2, d) == u2.thread_map[td] && exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_unown_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitUnown, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_unown_step_pre); reveal(thread_exit_unown_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map == u.thread_map);
    assert(in_exit(u2, d) && exit_holds(u2, d));
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_iommu_leaf_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitIommuLeaf, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_iommu_leaf_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map == u.thread_map);
    assert(in_exit(u2, d) && exit_holds(u2, d));
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_refund_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitRefund, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_refund_step);
    reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_container_quota_2m_increased); reveal(kernel_u_container_quota_1g_increased);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    assert(u2.process_map == u.process_map && u2.thread_map == u.thread_map && u2.cpu_array == u.cpu_array);
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c) implies u2.container_map[c].lock_state == u.container_map[c].lock_state
        && u2.container_map[c].pcid_allocator_lock == u.container_map[c].pcid_allocator_lock && u2.container_map[c].free_pcids == u.container_map[c].free_pcids by {};
    assert(in_exit(u2, d) && exit_holds(u2, d));
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_quota_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitQuota, u, u2, d),
        exit_quota_after_unown(u, StepLabel::ThreadExitQuota, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_quota_step_pre); reveal(thread_exit_quota_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.cpu_array == u.cpu_array && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_exit(u2, d) && cur_thread(u2, d) == u2.thread_map[td] && exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_unlock_table_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitUnlockTable, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_unlock_table_step_pre); reveal(thread_exit_unlock_table_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    let pd = u.thread_map[td].owning_proc;
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.cpu_array == u.cpu_array && u2.thread_map.dom() =~= u.thread_map.dom());
    assert(in_exit(u2, d) && cur_thread(u2, d) == u2.thread_map[td] && exit_holds(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        if t2 != td { assert(thread_wf_at(u.thread_map[t2])); }
    };
    proc_shapes_same_implies_processes_wf(u, u2);
    sole_thread_implies_table_unworked(u, d, pd);
    assert(table_killer(u, d) && table_killer_proc(u, d) == pd && !table_killer(u2, d));
    assert(kill_target_table_step(u, u2, d, pd));
}

proof fn exit_lock_pcid_allocator_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitLockPcidAllocator, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_lock_pcid_allocator_step_pre); reveal(thread_exit_finish_step_pre); reveal(thread_exit_lock_pcid_allocator_step);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    assert(u2.process_map == u.process_map && u2.thread_map == u.thread_map && u2.cpu_array == u.cpu_array);
    assert(u2.container_map.dom() =~= u.container_map.dom());
    assert(in_exit(u2, d) && exit_holds(u2, d));
    proc_shapes_same_implies_processes_wf(u, u2);
    assert(tables_kept(u, u2));
}

proof fn exit_finish_implies_post(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), labeled_step(StepLabel::ThreadExitFinish, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    reveal(thread_exit_finish_step_pre); reveal(thread_exit_finish_step); reveal(kernel_u_thread_exit_changed); reveal(kernel_u_cpu_ownership_wf);
    assert(in_exit(u, d));
    exit_middle_pre(u, d);
    let cpu = u.cpu_array[d as int];
    let td = cpu.current_thread->Some_0;
    let pd = cpu.current_process->Some_0;
    let pr = u.process_map[pd];
    proc_wf_at_of(u, pd);
    no_dup_remove_value_implies_removed(pr.owned_threads, td);
    assert(u2.process_map.dom() =~= u.process_map.dom() && u2.thread_map.dom() =~= u.thread_map.dom().remove(td));
    assert(!pr.killed);
    assert(cpu_outside(u2, d) && !(u2.cpu_array[d as int].op is InStep) && !in_exit(u2, d));
    assert forall|t2: RwLockThreadPtr| #![trigger u2.thread_map[t2]] u2.thread_map.dom().contains(t2) implies thread_wf_at(u2.thread_map[t2]) by {
        assert(thread_wf_at(u.thread_map[t2]));
    };
    owned_removed_implies_processes_wf(u, u2, pd, td);
    if pr.owned_threads.len() == 1 {
        let r = pr.owned_threads.remove_value(td);
        if r.len() > 0 {
            let x = r[0];
            assert(r.contains(x));
            assert(pr.owned_threads.contains(x) && pr.owned_threads.contains(td));
            assert(pr.owned_threads[0] == x && pr.owned_threads[0] == td);
        }
        sole_thread_implies_table_unworked(u, d, pd);
        assert(kill_target_table_step(u, u2, d, pd));
    } else {
        let s = pr.owned_threads;
        let other = if s[0] != td { s[0] } else { s[1] };
        assert(s.contains(other) && other != td);
        assert(s.remove_value(td).contains(other));
        assert(tables_kept(u, u2));
    }
}

/// Every exit step in the world proves what its cpu owes.
pub proof fn exit_step_implies_own_post(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), exit_label(l), exit_quota_after_unown(u, l, d), labeled_step(l, u, u2, d),
    ensures exit_own_post(u, u2, d),
{
    match l {
        StepLabel::ThreadExitEnter => exit_enter_implies_post(u, u2, d),
        StepLabel::ThreadExitDrop => exit_drop_implies_post(u, u2, d),
        StepLabel::ThreadExitRelease => exit_release_implies_post(u, u2, d),
        StepLabel::ThreadExitLockTable => exit_lock_table_implies_post(u, u2, d),
        StepLabel::ThreadExitTableHidden => exit_table_hidden_implies_post(u, u2, d),
        StepLabel::ThreadExitTlbFlush => exit_tlb_flush_implies_post(u, u2, d),
        StepLabel::ThreadExitFlushed => exit_flushed_implies_post(u, u2, d),
        StepLabel::ThreadExitUnown => exit_unown_implies_post(u, u2, d),
        StepLabel::ThreadExitIommuLeaf => exit_iommu_leaf_implies_post(u, u2, d),
        StepLabel::ThreadExitRefund => exit_refund_implies_post(u, u2, d),
        StepLabel::ThreadExitQuota => exit_quota_implies_post(u, u2, d),
        StepLabel::ThreadExitUnlockTable => exit_unlock_table_implies_post(u, u2, d),
        StepLabel::ThreadExitLockPcidAllocator => exit_lock_pcid_allocator_implies_post(u, u2, d),
        StepLabel::ThreadExitFinish => exit_finish_implies_post(u, u2, d),
        _ => {},
    }
}

/// An exit step keeps every other cpu, every foreign hold, the kill invariants, and the exit holds.
pub proof fn exit_step_implies_kill_world_inv_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), exit_locks_held(u), exit_label(l), exit_quota_after_unown(u, l, d), labeled_step(l, u, u2, d),
    ensures others_kept(u, u2, d), foreign_holds_kept(u, u2, d), kill_world_inv(u2), exit_own_post(u, u2, d), exit_locks_held(u2),
{
    exit_step_implies_own_post(u, u2, l, d);
    kill_d_frame_implies_others_kept(u, u2, d);
    kill_d_frame_implies_held_procs_kept(u, u2, d);
    frame_implies_exit_locks_held_kept(u, u2, d);
    assert(!in_kill(u2, d));
    assert forall|c: CpuId| #![trigger u2.cpu_array[c as int]] in_kill(u2, c) implies kill_holds(u2, c) by {};
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) implies {
        &&& cpu_outside(u2, x) ==> !(u2.cpu_array[x as int].op is InStep)
        &&& !cpu_outside(u2, x) && u2.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u2, x).syscall_progress is None
    } by { if x == d && in_exit(u2, d) { assert(exit_holds(u2, d)); } };
}
} // verus!

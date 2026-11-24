//! What every world step does to the run queues, one lemma per family. Nine labels touch a run queue or make a thread
//! wait (`sched_special`): the switch, the two pulls, the two thread creations, the offline step that requeues the running
//! thread, the IPC rendezvous that wakes the queue head, the kill's dequeue of a scheduled victim, and the exit's entry that
//! wakes the caller. Every other world step has the scheduling frame. Every world step has the cpu frame.
use vstd::prelude::*;
use crate::*;
use crate::run_queue::*;
use crate::frame::*;
use crate::world::*;
use crate::family_traced::*;
use crate::trace::*;
use crate::family_alloc::*;
use crate::family_new_thread::*;
use crate::family_cpu::*;
use crate::family_pci::*;
use crate::family_schedule::*;
use crate::family_env::*;
use crate::family_split_merge::*;
use crate::family_kill::*;
use crate::family_new_process::*;
use crate::family_exit::*;
use crate::family_offline::*;
use crate::family_ipc::*;
use veriflat_map_4k::*;
use veriflat_map_4k::map_4k::share_mapping_4k_spec::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;
use veriflat_syscall_new_thread::{syscall_new_endpoint::syscall_new_endpoint_spec::*, syscall_new_thread::syscall_new_thread_spec::*};
use veriflat_syscall_alloc_quota::syscall_alloc_quota::{syscall_alloc_quota_spec::*, syscall_alloc_quota_1g_spec::*};
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::{syscall_cpu_hotplug_spec::*, syscall_cpu_offline_check_spec::*};
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;
use veriflat_syscall_schedule::{rebalance_pull::rebalance_pull_spec::*, syscall_schedule::syscall_schedule_spec::*};
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;
use veriflat_syscall_new_process::syscall_new_process::syscall_new_process_spec::*;
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;
use veriflat_syscall_ipc::syscall_ipc::syscall_ipc_spec::*;

verus! {
/// The labels that touch a run queue or make a thread wait.
pub open spec fn sched_special(l: StepLabel) -> bool {
    ||| l is Schedule || l is RebalancePull || l is OrphanPull || l is NewThreadFinish || l is NewProcessFinish || l is CpuOfflineCheck
    ||| l is IpcRendezvous || l is KillProcessDequeueScheduled || l is ThreadExitEnter
}

/// A step that pushes `n` at the tail of shard `s` of container `c0` and makes `n` SCHEDULED there, `n` not waiting before;
/// every other thread keeps what scheduling reads.
pub open spec fn push_shape(u: KernelU, u2: KernelU, c0: RwLockContainerPtr, s: CpuId, n: RwLockThreadPtr) -> bool {
    &&& index_valid(NUM_CPUS, s) && u.container_map.dom().contains(c0)
    &&& u2.container_map.dom() =~= u.container_map.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c) ==> u2.container_map[c].scheduler
        == if c == c0 { u.container_map[c0].scheduler.update(s as int, u.container_map[c0].scheduler[s as int].push(n)) } else { u.container_map[c].scheduler }
    &&& u2.thread_map.dom().contains(n) && !waiting(u, n)
    &&& u2.thread_map[n].state == (ThreadState::SCHEDULED { cpu_id: s }) && u2.thread_map[n].owning_container == c0 && index_valid(NUM_CPUS, u2.thread_map[n].last_cpu)
    &&& forall|x: RwLockThreadPtr| #![trigger u2.thread_map[x]] u2.thread_map.dom().contains(x) && x != n ==> u.thread_map.dom().contains(x)
        && u2.thread_map[x].state == u.thread_map[x].state && u2.thread_map[x].killed == u.thread_map[x].killed
        && u2.thread_map[x].owning_container == u.thread_map[x].owning_container && u2.thread_map[x].last_cpu == u.thread_map[x].last_cpu
    &&& forall|x: RwLockThreadPtr| #![trigger u.thread_map[x]] u.thread_map.dom().contains(x) ==> u2.thread_map.dom().contains(x)
}

/// A push keeps the run-queue invariant and leaves every waiting thread where it was.
proof fn push_shape_implies_run_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, c0: RwLockContainerPtr, s: CpuId, n: RwLockThreadPtr, t: RwLockThreadPtr)
    requires queue_inv(u), push_shape(u, u2, c0, s, n), !(l is Schedule || l is RebalancePull || l is OrphanPull),
    ensures queue_inv(u2), waiting(u, t) ==> waiting_step(u, u2, l, d, t),
{
    reveal(queue_inv);
    let q = u.container_map[c0].scheduler[s as int];
    assert(u.container_map[c0].scheduler.len() == NUM_CPUS);
    assert(u2.container_map[c0].scheduler[s as int] == q.push(n));
    assert forall|x: RwLockThreadPtr| #![trigger waiting(u2, x)] waiting(u2, x) implies queued(u2, x) by {
        if x == n { assert(q.push(n)[q.len() as int] == n); } else {
            assert(u2.thread_map.dom().contains(x));
            assert(u.thread_map.dom().contains(x));
            assert(u2.thread_map[x].state == u.thread_map[x].state);
            assert(waiting(u, x));
            assert(queued(u, x));
            assert(u.container_map[ctn_of(u, x)].scheduler.len() == NUM_CPUS);
            if ctn_of(u, x) == c0 && shard_of(u, x) == s { push_implies_seq_pos_kept(q, x, n); }
        }
    };
    assert forall|x: RwLockThreadPtr| #![trigger u2.thread_map[x]] u2.thread_map.dom().contains(x) implies index_valid(NUM_CPUS, u2.thread_map[x].last_cpu) by {
        if x != n { assert(index_valid(NUM_CPUS, u.thread_map[x].last_cpu)); }
    };
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u2.container_map.dom().contains(c) implies u2.container_map[c].scheduler.len() == NUM_CPUS by {
        assert(u.container_map[c].scheduler.len() == NUM_CPUS);
    };
    if waiting(u, t) {
        assert(t != n && u2.thread_map.dom().contains(t) && waiting(u2, t));
        assert(queued(u, t));
        assert(u.container_map[ctn_of(u, t)].scheduler.len() == NUM_CPUS);
        if ctn_of(u, t) == c0 && shard_of(u, t) == s { push_implies_seq_pos_kept(q, t, n); } else { assert(queue_of(u2, t) == queue_of(u, t)); }
    }
}

/// A pull of cpu `d` moving the live head `x` of shard `v` of its container to the tail of shard `d`.
pub open spec fn pull_shape(u: KernelU, u2: KernelU, d: CpuId, v: CpuId, x: RwLockThreadPtr) -> bool {
    let cpu = u.cpu_array[d as int];
    let container = u.container_map[cpu.owning_container];
    let queues = container.scheduler;
    let tx = u.thread_map[x];
    &&& index_valid(NUM_CPUS, d) && index_valid(NUM_CPUS, v) && v != d && !(cpu.state is Off) && u.cpu_array.len() == NUM_CPUS
    &&& u.container_map.dom().contains(cpu.owning_container)
    &&& queues[v as int].len() > 0 && queues[v as int][0] == x
    &&& u.thread_map.dom().contains(x) && !tx.killed && tx.state == (ThreadState::SCHEDULED { cpu_id: v }) && tx.owning_container == cpu.owning_container
    &&& u2 == (KernelU {
        container_map: u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: queues.update(v as int, queues[v as int].skip(1)).update(d as int, queues[d as int].push(x)), ..container
        }),
        thread_map: u.thread_map.insert(x, ThreadU { state: ThreadState::SCHEDULED { cpu_id: d }, ..tx }),
        ..u
    })
}

/// A pull keeps the run-queue invariant and the cpu frame; a waiting thread other than the pulled head keeps its shard,
/// and the pulled head moves from the head of shard `v` to shard `d`.
proof fn pull_shape_implies_run_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, v: CpuId, x: RwLockThreadPtr, t: RwLockThreadPtr)
    requires
        queue_inv(u), pull_shape(u, u2, d, v, x), l is RebalancePull || l is OrphanPull, pops_head(u, l, d, u.cpu_array[d as int].owning_container, v),
        l is RebalancePull ==> u.container_map[u.cpu_array[d as int].owning_container].scheduler[d as int].len() == 0,
        l is OrphanPull ==> !cpu_serves_container(u, u.cpu_array[d as int].owning_container, v),
    ensures queue_inv(u2), cpu_frame(u, u2, l, d), waiting(u, t) ==> waiting_step(u, u2, l, d, t),
{
    reveal(queue_inv);
    let c0 = u.cpu_array[d as int].owning_container;
    let queues = u.container_map[c0].scheduler;
    let qv = queues[v as int];
    let qd = queues[d as int];
    assert(queues.len() == NUM_CPUS);
    assert(u2.container_map[c0].scheduler[v as int] == qv.skip(1));
    assert(u2.container_map[c0].scheduler[d as int] == qd.push(x));
    assert forall|y: RwLockThreadPtr| #![trigger waiting(u2, y)] waiting(u2, y) implies queued(u2, y) by {
        if y == x { assert(qd.push(x)[qd.len() as int] == x); } else {
            assert(u2.thread_map[y] == u.thread_map[y]);
            assert(waiting(u, y));
            assert(queued(u, y));
            assert(u.container_map[ctn_of(u, y)].scheduler.len() == NUM_CPUS);
            if ctn_of(u, y) == c0 && shard_of(u, y) == v { skip_head_implies_seq_pos_lowered(qv, y); }
            else if ctn_of(u, y) == c0 && shard_of(u, y) == d { push_implies_seq_pos_kept(qd, y, x); }
        }
    };
    assert forall|y: RwLockThreadPtr| #![trigger u2.thread_map[y]] u2.thread_map.dom().contains(y) implies index_valid(NUM_CPUS, u2.thread_map[y].last_cpu) by {
        assert(index_valid(NUM_CPUS, u.thread_map[y].last_cpu));
    };
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u2.container_map.dom().contains(c) implies u2.container_map[c].scheduler.len() == NUM_CPUS by {
        assert(u.container_map[c].scheduler.len() == NUM_CPUS);
    };
    if waiting(u, t) {
        assert(queued(u, t));
        assert(u.container_map[ctn_of(u, t)].scheduler.len() == NUM_CPUS);
        if t == x {
            first_at_implies_seq_pos(qv, t, 0);
            assert(queue_of(u2, t) == qd.push(x));
            assert(qd.push(x)[qd.len() as int] == x);
            contains_implies_seq_pos_facts(qd.push(x), t);
        } else if ctn_of(u, t) == c0 && shard_of(u, t) == v {
            skip_head_implies_seq_pos_lowered(qv, t);
        } else if ctn_of(u, t) == c0 && shard_of(u, t) == d {
            push_implies_seq_pos_kept(qd, t, x);
        } else {
            assert(queue_of(u2, t) == queue_of(u, t));
        }
    }
}

/// A switch keeps the run-queue invariant and the cpu frame; the head of the cpu's shard runs and every other waiting
/// thread keeps its shard.
proof fn schedule_implies_run_step(u: KernelU, u2: KernelU, fp: Option<Pcid>, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::Schedule { flushed_pcid: fp }, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::Schedule { flushed_pcid: fp }, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::Schedule { flushed_pcid: fp }, d, t),
{
    reveal(schedule_step_pre); reveal(kernel_u_context_switch_changed); reveal(kernel_u_cpu_ownership_wf); reveal(queue_inv);
    let cpu = u.cpu_array[d as int];
    let c0 = cpu.owning_container;
    let q = u.container_map[c0].scheduler[d as int];
    let next = q[0];
    let prev = cpu.current_thread;
    let q2 = match prev { Some(p) => q.skip(1).push(p), None => q.skip(1) };
    assert(u.container_map[c0].scheduler.len() == NUM_CPUS);
    assert(u2.container_map[c0].scheduler[d as int] == q2);
    if prev is Some {
        assert(u.thread_map[prev->Some_0].state == (ThreadState::RUNNING { cpu_id: d }));
        assert(u.thread_map[prev->Some_0].owning_container == c0);
    }
    assert forall|x: RwLockThreadPtr| #![trigger waiting(u2, x)] waiting(u2, x) implies queued(u2, x) by {
        if prev == Some(x) { assert(q2[q2.len() - 1] == x); } else {
            assert(x != next);
            assert(u2.thread_map[x] == u.thread_map[x]);
            assert(waiting(u, x));
            assert(queued(u, x));
            assert(u.container_map[ctn_of(u, x)].scheduler.len() == NUM_CPUS);
            if ctn_of(u, x) == c0 && shard_of(u, x) == d { switch_queue_implies_seq_pos_lowered(q, x, prev); }
        }
    };
    assert forall|x: RwLockThreadPtr| #![trigger u2.thread_map[x]] u2.thread_map.dom().contains(x) implies index_valid(NUM_CPUS, u2.thread_map[x].last_cpu) by {
        if x != next { assert(index_valid(NUM_CPUS, u.thread_map[x].last_cpu)); }
    };
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u2.container_map.dom().contains(c) implies u2.container_map[c].scheduler.len() == NUM_CPUS by {
        assert(u.container_map[c].scheduler.len() == NUM_CPUS);
    };
    if waiting(u, t) {
        assert(queued(u, t));
        assert(u.container_map[ctn_of(u, t)].scheduler.len() == NUM_CPUS);
        if ctn_of(u, t) == c0 && shard_of(u, t) == d { contains_implies_seq_pos_facts(q, t); }
        if t != next {
            assert(prev != Some(t));
            assert(u2.thread_map[t] == u.thread_map[t]);
            if ctn_of(u, t) == c0 && shard_of(u, t) == d { switch_queue_implies_seq_pos_lowered(q, t, prev); } else { assert(queue_of(u2, t) == queue_of(u, t)); }
        }
    }
}

/// A rebalance pull keeps the run-queue invariant and the cpu frame.
proof fn rebalance_pull_implies_run_step(u: KernelU, u2: KernelU, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::RebalancePull, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::RebalancePull, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::RebalancePull, d, t),
{
    reveal(rebalance_pull_step_pre); reveal(kernel_u_rebalance_pull_changed); reveal(kernel_u_cpu_ownership_wf);
    let c0 = u.cpu_array[d as int].owning_container;
    let queues = u.container_map[c0].scheduler;
    let v = first_nonempty_shard(queues, 0, d)->Some_0;
    pull_shape_implies_run_step(u, u2, StepLabel::RebalancePull, d, v, queues[v as int][0], t);
}

/// An orphan pull keeps the run-queue invariant and the cpu frame.
proof fn orphan_pull_implies_run_step(u: KernelU, u2: KernelU, cursor: CpuId, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::OrphanPull { cursor }, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::OrphanPull { cursor }, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::OrphanPull { cursor }, d, t),
{
    reveal(orphan_pull_step_pre); reveal(kernel_u_orphan_pull_changed); reveal(kernel_u_cpu_ownership_wf);
    let c0 = u.cpu_array[d as int].owning_container;
    let queues = u.container_map[c0].scheduler;
    let v = orphan_victim(u, c0, cursor, d)->Some_0;
    pull_shape_implies_run_step(u, u2, StepLabel::OrphanPull { cursor }, d, v, queues[v as int][0], t);
}

/// The kill's dequeue keeps the run-queue invariant and the cpu frame: it removes its killed victim from the victim's shard.
proof fn kill_dequeue_implies_run_step(u: KernelU, u2: KernelU, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::KillProcessDequeueScheduled, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::KillProcessDequeueScheduled, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::KillProcessDequeueScheduled, d, t),
{
    reveal(kill_process_dequeue_scheduled_step); reveal(kernel_u_cpu_ownership_wf); reveal(queue_inv);
    let v = kill_stage(u, d)->Thread_thread;
    let vt = u.thread_map[v];
    let c0 = vt.owning_container;
    let sh = vt.state->SCHEDULED_cpu_id;
    let queues = u.container_map[c0].scheduler;
    assert(queues.len() == NUM_CPUS);
    assert(u2.container_map[c0].scheduler == queues.update(sh as int, queues[sh as int].remove_value(v)));
    assert forall|x: RwLockThreadPtr| #![trigger waiting(u2, x)] waiting(u2, x) implies queued(u2, x) by {
        assert(x != v && waiting(u, x) && queued(u, x));
        assert(u.container_map[ctn_of(u, x)].scheduler.len() == NUM_CPUS);
        if ctn_of(u, x) == c0 && shard_of(u, x) == sh { remove_value_implies_seq_pos_kept_or_lowered(queues[sh as int], x, v); }
    };
    assert forall|x: RwLockThreadPtr| #![trigger u2.thread_map[x]] u2.thread_map.dom().contains(x) implies index_valid(NUM_CPUS, u2.thread_map[x].last_cpu) by {
        assert(index_valid(NUM_CPUS, u.thread_map[x].last_cpu));
    };
    assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u2.container_map.dom().contains(c) implies u2.container_map[c].scheduler.len() == NUM_CPUS by {
        assert(u.container_map[c].scheduler.len() == NUM_CPUS);
    };
    if waiting(u, t) {
        assert(t != v && u2.thread_map[t] == u.thread_map[t]);
        assert(queued(u, t));
        assert(u.container_map[ctn_of(u, t)].scheduler.len() == NUM_CPUS);
        if ctn_of(u, t) == c0 && shard_of(u, t) == sh && index_valid(NUM_CPUS, sh) {
            remove_value_implies_seq_pos_kept_or_lowered(queues[sh as int], t, v);
        } else { assert(queue_of(u2, t) == queue_of(u, t)); }
    }
}

/// Thread creation pushes the new thread at the tail of the creating cpu's shard.
proof fn new_thread_finish_implies_run_step(u: KernelU, u2: KernelU, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::NewThreadFinish, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::NewThreadFinish, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::NewThreadFinish, d, t),
{
    reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    let cpu = u.cpu_array[d as int];
    let n = u2.process_map[cpu.current_process->Some_0].owned_threads.last();
    assert(push_shape(u, u2, cpu.owning_container, d, n));
    push_shape_implies_run_step(u, u2, StepLabel::NewThreadFinish, d, cpu.owning_container, d, n, t);
}

/// Process creation pushes the child's first thread at the tail of the creating cpu's shard.
proof fn new_process_finish_implies_run_step(u: KernelU, u2: KernelU, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::NewProcessFinish, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::NewProcessFinish, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::NewProcessFinish, d, t),
{
    reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    let cpu = u.cpu_array[d as int];
    let th = u.thread_map[cpu.current_thread->Some_0];
    let child = th.syscall_progress->Some_0->Share4k_origin->NewProcess_0.child->Some_0;
    let n = u2.process_map[child].owned_threads.last();
    assert(push_shape(u, u2, th.owning_container, d, n));
    push_shape_implies_run_step(u, u2, StepLabel::NewProcessFinish, d, th.owning_container, d, n, t);
}

/// The offline step requeues the running thread, if any, at the tail of the cpu's own shard.
proof fn offline_implies_run_step(u: KernelU, u2: KernelU, f: bool, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::CpuOfflineCheck { flushed_default_pcid: f }, u, u2, d),
    ensures
        queue_inv(u2), cpu_frame(u, u2, StepLabel::CpuOfflineCheck { flushed_default_pcid: f }, d),
        waiting(u, t) ==> waiting_step(u, u2, StepLabel::CpuOfflineCheck { flushed_default_pcid: f }, d, t),
{
    reveal(cpu_offline_check_step_pre); reveal(kernel_u_cpu_went_off_changed); reveal(kernel_u_cpu_ownership_wf); reveal(queue_inv);
    let cpu = u.cpu_array[d as int];
    if cpu.current_thread is Some {
        assert(push_shape(u, u2, cpu.owning_container, d, cpu.current_thread->Some_0));
        push_shape_implies_run_step(u, u2, StepLabel::CpuOfflineCheck { flushed_default_pcid: f }, d, cpu.owning_container, d, cpu.current_thread->Some_0, t);
    } else {
        assert(sched_frame(u, u2));
        sched_frame_implies_run_step(u, u2, StepLabel::CpuOfflineCheck { flushed_default_pcid: f }, d, t);
    }
}

/// A rendezvous wakes the endpoint's head onto the caller's shard, or for a cross-container peer onto its last cpu's shard.
proof fn rendezvous_implies_run_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), l is IpcRendezvous, labeled_step(l, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, l, d), waiting(u, t) ==> waiting_step(u, u2, l, d, t),
{
    reveal(ipc_rendezvous_step_pre); reveal(kernel_u_ipc_rendezvous_changed); reveal(kernel_u_cpu_ownership_wf); reveal(queue_inv);
    let ep_idx = l->IpcRendezvous_channel_index;
    let caller = u.cpu_array[d as int].current_thread->Some_0;
    let ep = u.thread_map[caller].endpoint_descriptors[ep_idx as int]->Some_0;
    let peer = u.endpoint_map[ep].queue[0];
    let pt = u.thread_map[peer];
    let wake = if pt.owning_container == u.thread_map[caller].owning_container { d } else { pt.last_cpu };
    assert(index_valid(NUM_CPUS, pt.last_cpu));
    assert(push_shape(u, u2, pt.owning_container, wake, peer));
    push_shape_implies_run_step(u, u2, l, d, pt.owning_container, wake, peer, t);
}

/// The exit's entry wakes a live caller onto the exiting cpu's shard of the caller's container.
proof fn exit_enter_implies_run_step(u: KernelU, u2: KernelU, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), labeled_step(StepLabel::ThreadExitEnter, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, StepLabel::ThreadExitEnter, d), waiting(u, t) ==> waiting_step(u, u2, StepLabel::ThreadExitEnter, d, t),
{
    reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); reveal(queue_inv);
    let td = u.cpu_array[d as int].current_thread->Some_0;
    let th = u.thread_map[td];
    if th.caller is Some && !(u.thread_map[th.caller->Some_0].state is DANGLING) {
        let caller = th.caller->Some_0;
        assert(caller != td);
        assert(push_shape(u, u2, u.thread_map[caller].owning_container, d, caller));
        push_shape_implies_run_step(u, u2, StepLabel::ThreadExitEnter, d, u.thread_map[caller].owning_container, d, caller, t);
    } else {
        assert(sched_frame(u, u2));
        sched_frame_implies_run_step(u, u2, StepLabel::ThreadExitEnter, d, t);
    }
}

/// The steps of `new_endpoint`, `alloc_quota_4k`, `mmap_4k`, and `unmap_4k` touch no run queue.
proof fn traced_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::NewEndpointEnter { .. } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { .. } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { .. } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { .. } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        StepLabel::Unmap4kEnter { .. } => { reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); },
        _ => {},
    }
}

/// Quota allocations touch no run queue.
proof fn alloc_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), alloc_label(l), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::AllocThreadQuota4k { .. } => { reveal(alloc_thread_quota_4k_step_pre); reveal(kernel_u_only_process2thread_quota_4k_changed); },
        StepLabel::AllocQuota2m { .. } => { reveal(alloc_quota_2m_step_pre); reveal(kernel_u_only_process_quota_2m_changed); },
        StepLabel::AllocThreadQuota2m { .. } => { reveal(alloc_thread_quota_2m_step_pre); reveal(kernel_u_only_process2thread_quota_2m_changed); },
        StepLabel::AllocQuota1g { .. } => { reveal(alloc_quota_1g_step_pre); reveal(kernel_u_only_process_quota_1g_changed); },
        StepLabel::AllocThreadQuota1g { .. } => { reveal(alloc_thread_quota_1g_step_pre); reveal(kernel_u_only_process2thread_quota_1g_changed); },
        _ => {},
    }
}

/// Hotplug requests touch no run queue and no running thread.
proof fn cpu_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), cpu_label(l), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::CpuOfflineRequest { .. } => { reveal(cpu_offline_request_step_pre); reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnline { .. } => { reveal(cpu_online_step_pre); reveal(kernel_u_cpu_online_changed); },
        StepLabel::CpuOfflineRequestChild { .. } => { reveal(cpu_offline_request_child_step_pre); reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnlineChild { .. } => { reveal(cpu_online_child_step_pre); reveal(kernel_u_cpu_online_changed); },
        _ => {},
    }
}

/// PCI attach and claim touch no run queue.
proof fn pci_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), pci_label(l), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::PciAttach { .. } => { reveal(pci_attach_dma_step_pre); reveal(kernel_u_pci_attach_changed); },
        StepLabel::PciClaim { .. } => { reveal(pci_claim_step_pre); reveal(kernel_u_pci_claim_changed); },
        _ => {},
    }
}

/// Splits and merges touch no run queue.
proof fn split_merge_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), split_merge_label(l), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{ reveal(kernel_u_cpu_ownership_wf); }

/// Environment events touch no run queue.
proof fn env_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), env_label(l), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::TrapEnter => { reveal(kernel_u_trap_enter_step_pre); reveal(kernel_u_trap_enter_step); },
        StepLabel::TrapReturn => { reveal(kernel_u_trap_return_step_pre); reveal(kernel_u_trap_return_step); },
        StepLabel::TrapDivert => { reveal(kernel_u_trap_divert_step_pre); reveal(kernel_u_trap_divert_step); },
        StepLabel::RegsChanged { .. } => { reveal(kernel_u_regs_changed_step_pre); reveal(kernel_u_regs_changed_step); },
        StepLabel::TrapReturnValuesWritten { .. } => { reveal(kernel_u_trap_return_values_written_step_pre); reveal(kernel_u_trap_return_values_written_step); },
        StepLabel::CpuTlbFilled { .. } => { reveal(kernel_u_cpu_tlb_filled_step); },
        StepLabel::IommuTlbFilled { .. } => { reveal(kernel_u_iommu_tlb_filled_step); },
        StepLabel::IommuContextCacheFilled => { reveal(kernel_u_iommu_context_cache_filled_step); },
        _ => {},
    }
}

/// The kill's steps other than the dequeue touch no run queue; the victims they change are killed.
proof fn kill_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_label(l), !(l is KillProcessDequeueScheduled), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kill_process_step_pre);
    match l {
        StepLabel::KillProcessEnter { .. } => { reveal(kill_process_enter_step_pre); reveal(kill_process_enter_step); },
        StepLabel::KillProcessMarkChild => { reveal(kill_process_mark_child_step); },
        StepLabel::KillProcessDangling => { reveal(kill_process_dangling_step); },
        StepLabel::KillProcessMarkThread => { reveal(kill_process_mark_thread_step); },
        StepLabel::KillProcessDequeueEndpoint => { reveal(kill_process_dequeue_endpoint_step); },
        StepLabel::KillProcessCpuToIdle => { reveal(kill_process_cpu_to_idle_step); },
        StepLabel::KillProcessUnlink => { reveal(kill_process_unlink_step); },
        StepLabel::KillProcessLockTable => { reveal(kill_process_lock_table_step); },
        StepLabel::KillProcessTableHidden => { reveal(kill_process_table_hidden_step); reveal(process_table_hidden_step); },
        StepLabel::KillProcessTlbCleared => { reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::KillProcessFlushed => { reveal(kill_process_flushed_step); },
        StepLabel::KillProcessUnownFunctions => { reveal(kill_process_unown_functions_step); },
        StepLabel::KillProcessIommuLeaf => { reveal(kill_process_iommu_leaf_step); },
        StepLabel::KillProcessRefund => {
            reveal(kill_process_refund_step);
            reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_container_quota_2m_increased); reveal(kernel_u_container_quota_1g_increased);
        },
        StepLabel::KillProcessQuota => { reveal(kill_process_quota_step); },
        StepLabel::KillProcessUnlockTable => { reveal(kill_process_unlock_table_step); },
        StepLabel::KillProcessZombify => { reveal(kill_process_zombify_step); },
        StepLabel::KillProcessZombieRetire => { reveal(kill_process_zombie_retire_step); },
        StepLabel::KillProcessRetire => { reveal(kill_process_retire_step); },
        StepLabel::KillProcessFinish => { reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step); },
        _ => {},
    }
}

/// Process creation other than its last step touches no run queue.
proof fn new_process_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), new_process_label(l), !(l is NewProcessFinish), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::NewProcessEnter { .. } => { reveal(new_process_enter_step_pre); reveal(new_process_enter_step); },
        StepLabel::NewProcessPublish => { reveal(new_process_publish_step_pre); reveal(new_process_publish_step); },
        StepLabel::Share4kDirectory => { reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(share_4k_directory_pre_at); },
        StepLabel::Share4kLeaf => { reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_at); reveal(share_4k_leaf_pre_at); },
        _ => {},
    }
}

/// Thread creation's entry touches no run queue.
proof fn new_thread_enter_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), l is NewThreadEnter, labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{ reveal(kernel_u_cpu_ownership_wf); reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); }

/// The exit's steps after its entry touch no run queue; the last removes the exiting, running thread.
proof fn exit_step_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), exit_label(l), !(l is ThreadExitEnter), labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::ThreadExitDrop => { reveal(thread_exit_drop_step_pre); reveal(thread_exit_drop_step); },
        StepLabel::ThreadExitRelease => { reveal(thread_exit_drop_step_pre); reveal(thread_exit_release_step); reveal(kernel_u_endpoint_released); },
        StepLabel::ThreadExitLockTable => { reveal(thread_exit_lock_table_step_pre); reveal(thread_exit_lock_table_step); },
        StepLabel::ThreadExitTableHidden => { reveal(thread_exit_reclaim_step_pre); reveal(process_table_hidden_step); },
        StepLabel::ThreadExitTlbFlush => { reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::ThreadExitFlushed => { reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_flushed_step); },
        StepLabel::ThreadExitUnown => { reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_unown_step_pre); reveal(thread_exit_unown_step); },
        StepLabel::ThreadExitIommuLeaf => { reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_iommu_leaf_step); },
        StepLabel::ThreadExitRefund => {
            reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_refund_step);
            reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_container_quota_2m_increased); reveal(kernel_u_container_quota_1g_increased);
        },
        StepLabel::ThreadExitQuota => { reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_quota_step_pre); reveal(thread_exit_quota_step); },
        StepLabel::ThreadExitUnlockTable => { reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_unlock_table_step_pre); reveal(thread_exit_unlock_table_step); },
        StepLabel::ThreadExitLockPcidAllocator => {
            reveal(thread_exit_lock_pcid_allocator_step_pre); reveal(thread_exit_finish_step_pre); reveal(thread_exit_lock_pcid_allocator_step);
        },
        StepLabel::ThreadExitFinish => { reveal(thread_exit_finish_step_pre); reveal(thread_exit_finish_step); reveal(kernel_u_thread_exit_changed); },
        _ => {},
    }
}

/// The offline check's hold and release touch no run queue.
proof fn offline_hold_release_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), l is CpuOfflineCheckHold || l is CpuOfflineCheckRelease, labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::CpuOfflineCheckHold => { reveal(cpu_offline_check_hold_step_pre); reveal(cpu_offline_check_hold_step); },
        StepLabel::CpuOfflineCheckRelease => { reveal(cpu_offline_check_release_step_pre); reveal(cpu_offline_check_release_step); },
        _ => {},
    }
}

/// A blocking IPC takes the running thread off its cpu and touches no run queue.
proof fn ipc_block_implies_sched_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), l is IpcBlock, labeled_step(l, u, u2, d),
    ensures sched_frame(u, u2), cpu_frame(u, u2, l, d),
{ reveal(kernel_u_cpu_ownership_wf); reveal(ipc_step_pre); reveal(ipc_block_step_pre); reveal(kernel_u_ipc_block_changed); }

/// Every world step keeps the run-queue invariant and the cpu frame, and does to a waiting thread what `waiting_step` says.
pub proof fn world_step_implies_run_step(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, t: RwLockThreadPtr)
    requires kernel_u_ownership_wf(u), queue_inv(u), world_label(l), labeled_step(l, u, u2, d),
    ensures queue_inv(u2), cpu_frame(u, u2, l, d), waiting(u, t) ==> waiting_step(u, u2, l, d, t),
{
    match l {
        StepLabel::Schedule { flushed_pcid } => { schedule_implies_run_step(u, u2, flushed_pcid, d, t); return; },
        StepLabel::RebalancePull => { rebalance_pull_implies_run_step(u, u2, d, t); return; },
        StepLabel::OrphanPull { cursor } => { orphan_pull_implies_run_step(u, u2, cursor, d, t); return; },
        StepLabel::NewThreadFinish => { new_thread_finish_implies_run_step(u, u2, d, t); return; },
        StepLabel::NewProcessFinish => { new_process_finish_implies_run_step(u, u2, d, t); return; },
        StepLabel::CpuOfflineCheck { flushed_default_pcid } => { offline_implies_run_step(u, u2, flushed_default_pcid, d, t); return; },
        StepLabel::IpcRendezvous { .. } => { rendezvous_implies_run_step(u, u2, l, d, t); return; },
        StepLabel::KillProcessDequeueScheduled => { kill_dequeue_implies_run_step(u, u2, d, t); return; },
        StepLabel::ThreadExitEnter => { exit_enter_implies_run_step(u, u2, d, t); return; },
        _ => {},
    }
    if traced_label(l) { traced_step_implies_sched_frame(u, u2, l, d); }
    else if alloc_label(l) { alloc_step_implies_sched_frame(u, u2, l, d); }
    else if new_thread_label(l) { new_thread_enter_implies_sched_frame(u, u2, l, d); }
    else if cpu_label(l) { cpu_step_implies_sched_frame(u, u2, l, d); }
    else if pci_label(l) { pci_step_implies_sched_frame(u, u2, l, d); }
    else if split_merge_label(l) { split_merge_step_implies_sched_frame(u, u2, l, d); }
    else if env_label(l) { env_step_implies_sched_frame(u, u2, l, d); }
    else if kill_label(l) { kill_step_implies_sched_frame(u, u2, l, d); }
    else if new_process_label(l) { new_process_step_implies_sched_frame(u, u2, l, d); }
    else if exit_label(l) { exit_step_implies_sched_frame(u, u2, l, d); }
    else if offline_label(l) { offline_hold_release_implies_sched_frame(u, u2, l, d); }
    else { ipc_block_implies_sched_frame(u, u2, l, d); }
    sched_frame_implies_run_step(u, u2, l, d, t);
}
} // verus!

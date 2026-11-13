//! Round 8: `kill_process`. A killer walks down from the child it enters on, marking and write-locking each process it
//! descends into, marks and removes every thread of the process it stands on, reclaims an empty process under its page
//! table and IOMMU table write locks, retires it, and walks back up to the parent; it finishes when the walk is back on
//! its own process. The steps that lock an object another cpu may hold name that object in a wanted-lock spec
//! (`kill_*_wanted`), and a cpu inside a kill whose wanted locks are free always has an enabled step
//! (`kill_world_inv_wanted_free_implies_kill_enabled`). The five killed-thread reclaim steps are left out of the world:
//! `kernel_u_dangling_thread_reclaimed` does not yet pin its writer, so a killer can remove another killer's victim.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_env::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;

verus! {
/// The labels of `kill_process` in the world.
pub open spec fn kill_label(l: StepLabel) -> bool {
    ||| l is KillProcessEnter || l is KillProcessMarkChild || l is KillProcessDangling || l is KillProcessMarkThread
    ||| l is KillProcessDequeueScheduled || l is KillProcessDequeueEndpoint || l is KillProcessCpuToIdle || l is KillProcessUnlink
    ||| l is KillProcessReassignFunctions || l is KillProcessLockTable || l is KillProcessTableHidden || l is KillProcessTlbCleared
    ||| l is KillProcessFlushed || l is KillProcessIommuLeaf || l is KillProcessRefund || l is KillProcessQuota || l is KillProcessUnlockTable
    ||| l is KillProcessZombify || l is KillProcessZombieRetire || l is KillProcessRetire || l is KillProcessFinish
}

/// `c` is inside `kill_process`: its cpu is write-locked and its running thread records `KillProcess` progress.
pub open spec fn in_kill(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some
    &&& cur_thread(u, c).syscall_progress->Some_0 is KillProcess
}

/// The killer's own process.
pub open spec fn kill_own(u: KernelU, c: CpuId) -> RwLockProcessPtr { u.cpu_array[c as int].current_process->Some_0 }

/// Process `p` lies on the walk of killer `x`: it is the target or lies between the target and the killer's own process.
pub open spec fn kill_on_path(u: KernelU, x: CpuId, p: RwLockProcessPtr) -> bool {
    ||| p == kill_target(u, x)
    ||| u.process_map[kill_target(u, x)].uppertree_seq.contains(p) && u.process_map[p].uppertree_seq.contains(kill_own(u, x))
}

/// The stages at which the target has neither children, threads, nor PCI functions.
pub open spec fn kill_stage_emptied(st: KillStage) -> bool { st is Reclaim || st is Quota || st is Zombie || st is Retire }

/// The stages at which the killer write-holds the target's tables.
pub open spec fn kill_stage_reclaiming(st: KillStage) -> bool { st is Reclaim || st is Quota }

/// The stages after the flush is recorded and before the tables are unlocked.
pub open spec fn kill_stage_flushed(st: KillStage) -> bool { st == (KillStage::Reclaim { flushed: true }) || st is Quota }

/// The marked victim of killer `c`: write-held by `c`, killed, a thread of the target other than the killer, and in a
/// state the kill can take it from.
pub open spec fn kill_victim_ok(u: KernelU, c: CpuId) -> bool {
    let v = kill_stage(u, c)->Thread_thread;
    let vt = u.thread_map[v];
    &&& u.thread_map.dom().contains(v)
    &&& vt.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& vt.killed
    &&& u.process_map[kill_target(u, c)].owned_threads.contains(v)
    &&& v != u.cpu_array[c as int].current_thread->Some_0
    &&& !vt.state.is_reply_waiting()
    &&& !(vt.state is IPC_TRANSIT)
}

/// The target's page table, and its IOMMU table if any, are write-held by `c`, and the target is no zombie.
pub open spec fn kill_tables_held(u: KernelU, c: CpuId) -> bool {
    let t = u.process_map[kill_target(u, c)];
    &&& !t.zombie
    &&& t.pagetable is Some
    &&& t.pagetable->Some_0.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& t.iommu_table is Some ==> t.iommu_table->Some_0.lock_state == (LockStateU::WriteLocked { writer: c })
}

/// The target's page table keeps no user 4K mapping, 2M or 1G mapping, or window lock.
pub open spec fn kill_table_cleared(u: KernelU, c: CpuId) -> bool {
    let pt = u.process_map[kill_target(u, c)].pagetable->Some_0;
    &&& process_user_4k_unmapped(u, pt)
    &&& pt.mapping_2m.dom() == Set::<VAddr>::empty()
    &&& pt.mapping_1g.dom() == Set::<VAddr>::empty()
    &&& pt.pagetable_window_locks.dom() == Set::<WindowVa>::empty()
}

/// What killer `c` holds: its cpu's process, unmarked, its thread, and the target; every process on its walk is marked
/// and write-held by it; and the facts of its stage.
pub open spec fn kill_holds(u: KernelU, c: CpuId) -> bool {
    let cpu = u.cpu_array[c as int];
    let pp = kill_own(u, c);
    let tp = kill_target(u, c);
    let st = kill_stage(u, c);
    let t = u.process_map[tp];
    &&& cpu.current_process is Some
    &&& u.process_map.dom().contains(pp)
    &&& u.process_map[pp].lock_state == (LockStateU::WriteLocked { writer: c })
    &&& !u.process_map[pp].killed
    &&& cur_thread(u, c).lock_state == (LockStateU::WriteLocked { writer: c })
    &&& u.process_map.dom().contains(tp)
    &&& t.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& tp == pp ==> st is Walk
    &&& tp != pp ==> t.killed && t.uppertree_seq.contains(pp)
    &&& forall|q: RwLockProcessPtr| #![trigger u.process_map[kill_target(u, c)].uppertree_seq.contains(q)]
        u.process_map.dom().contains(q) && u.process_map[kill_target(u, c)].uppertree_seq.contains(q) && u.process_map[q].uppertree_seq.contains(pp)
            ==> u.process_map[q].killed && u.process_map[q].lock_state == (LockStateU::WriteLocked { writer: c })
    &&& kill_stage_ok(u, c)
}

/// The facts of the stage of killer `c`.
pub open spec fn kill_stage_ok(u: KernelU, c: CpuId) -> bool {
    let st = kill_stage(u, c);
    let t = u.process_map[kill_target(u, c)];
    &&& st is Thread ==> kill_victim_ok(u, c)
    &&& kill_stage_emptied(st) ==> t.children.len() == 0 && t.owned_threads.len() == 0 && t.owned_pci_functions.is_empty()
    &&& kill_stage_reclaiming(st) ==> kill_tables_held(u, c)
    &&& kill_stage_flushed(st) ==> kill_table_cleared(u, c)
    &&& st is Quota ==> (t.iommu_table is Some ==> process_iommu_4k_unmapped(t.iommu_table->Some_0))
    &&& st is Zombie ==> !t.zombie
    &&& st is Retire ==> t.zombie
}

/// Every killer holds what its walk and stage need.
pub open spec fn kill_locks_held(u: KernelU) -> bool { forall|c: CpuId| #![trigger u.cpu_array[c as int]] in_kill(u, c) ==> kill_holds(u, c) }

/// Every marked process is write-held by a killer on whose walk it lies.
pub open spec fn killed_held(u: KernelU) -> bool {
    forall|p: RwLockProcessPtr| #![trigger u.process_map[p].killed] u.process_map.dom().contains(p) && u.process_map[p].killed ==> {
        let w = u.process_map[p].lock_state->WriteLocked_writer;
        &&& u.process_map[p].lock_state is WriteLocked
        &&& in_kill(u, w)
        &&& kill_on_path(u, w, p)
    }
}

/// A thread with a syscall in progress or in IPC transit is write-locked, one waiting on an endpoint names it, no thread is
/// inside `kill_container`, which the world leaves out, and a thread sharing pages shares them into a new process.
pub open spec fn thread_wf_at(t: ThreadU) -> bool {
    &&& t.syscall_progress is Some ==> t.lock_state is WriteLocked && !(t.syscall_progress->Some_0 is KillContainer)
    &&& t.syscall_progress is Some && t.syscall_progress->Some_0 is Share4k ==> t.syscall_progress->Some_0->Share4k_origin is NewProcess
    &&& t.state is IPC_TRANSIT ==> t.lock_state is WriteLocked
    &&& t.state.is_endpoint_waiting() ==> t.blocking_endpoint_ptr is Some
    &&& t.endpoint_descriptors.len() == MAX_NUM_ENDPOINT_DESCRIPTORS
}

/// What `thread_wf_at` reads of a thread.
pub open spec fn thread_wf_view(t: ThreadU) -> (bool, bool, bool, bool, bool, bool, bool, bool) {
    (t.endpoint_descriptors.len() == MAX_NUM_ENDPOINT_DESCRIPTORS, t.syscall_progress is Some, t.lock_state is WriteLocked, t.state is IPC_TRANSIT, t.state.is_endpoint_waiting(), t.blocking_endpoint_ptr is Some,
        t.syscall_progress is Some && t.syscall_progress->Some_0 is KillContainer,
        t.syscall_progress is Some && t.syscall_progress->Some_0 is Share4k && !(t.syscall_progress->Some_0->Share4k_origin is NewProcess))
}

pub open spec fn threads_wf(u: KernelU) -> bool { forall|t: RwLockThreadPtr| #![trigger u.thread_map[t]] u.thread_map.dom().contains(t) ==> thread_wf_at(u.thread_map[t]) }

/// An unlocked cpu runs outside a kernel step, and a write-locked cpu write-holds its running thread unless that thread
/// records no syscall progress, as in the offline-check window between the hold and the release or offline step.
pub open spec fn cpus_wf(u: KernelU) -> bool {
    forall|x: CpuId| #![trigger u.cpu_array[x as int]] index_valid(NUM_CPUS, x) ==> {
        &&& cpu_outside(u, x) ==> !(u.cpu_array[x as int].op is InStep)
        &&& !cpu_outside(u, x) && u.cpu_array[x as int].current_thread is Some ==> cur_thread(u, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u, x).syscall_progress is None
    }
}

/// The process tree around `p`: children and parent agree and extend the ancestor sequence by one, ancestors have shorter
/// ancestor sequences, children and threads are listed once, every thread of `p` names `p` and is not dangling, and a live process
/// has a page table.
pub open spec fn proc_wf_at(u: KernelU, p: RwLockProcessPtr) -> bool {
    let pr = u.process_map[p];
    let par = pr.parent->Some_0;
    &&& forall|ch: RwLockProcessPtr| #![trigger pr.children.contains(ch)] pr.children.contains(ch)
        ==> u.process_map.dom().contains(ch) && u.process_map[ch].parent == Some(p) && u.process_map[ch].uppertree_seq == pr.uppertree_seq.push(p)
    &&& pr.parent is Some ==> u.process_map.dom().contains(par) && u.process_map[par].children.contains(p) && pr.uppertree_seq == u.process_map[par].uppertree_seq.push(par)
    &&& pr.parent is None ==> pr.uppertree_seq.len() == 0
    &&& forall|q: RwLockProcessPtr| #![trigger pr.uppertree_seq.contains(q)] pr.uppertree_seq.contains(q) && u.process_map.dom().contains(q)
        ==> u.process_map[q].uppertree_seq.len() < pr.uppertree_seq.len()
    &&& pr.children.no_duplicates()
    &&& pr.owned_threads.no_duplicates()
    &&& forall|t: RwLockThreadPtr| #![trigger pr.owned_threads.contains(t)] pr.owned_threads.contains(t) ==> !(u.thread_map[t].state is DANGLING) && u.thread_map[t].owning_proc == p
    &&& !pr.zombie ==> pr.pagetable is Some
    &&& pr.owned_threads.len() > 0 ==> !pr.zombie
}

pub open spec fn processes_wf(u: KernelU) -> bool { forall|p: RwLockProcessPtr| #![trigger proc_wf_at(u, p)] u.process_map.dom().contains(p) ==> proc_wf_at(u, p) }

/// The invariants the kill needs from the whole world.
pub open spec fn kill_world_inv(u: KernelU) -> bool { kill_locks_held(u) && killed_held(u) && threads_wf(u) && cpus_wf(u) && processes_wf(u) }

/// The boot facts the kill invariants start from: no process is marked, every thread and process is well formed, and no
/// cpu runs a kernel step.
pub open spec fn kill_quiescent(u: KernelU) -> bool {
    &&& forall|p: RwLockProcessPtr| #![trigger u.process_map[p].killed] u.process_map.dom().contains(p) ==> !u.process_map[p].killed
    &&& threads_wf(u)
    &&& processes_wf(u)
    &&& forall|x: CpuId| #![trigger u.cpu_array[x as int]] index_valid(NUM_CPUS, x) ==> !(u.cpu_array[x as int].op is InStep)
}

/// A killer that is not on its own process has a target other than its own process; used to name the target's facts.
pub proof fn kill_holds_at(u: KernelU, c: CpuId)
    requires kill_locks_held(u), in_kill(u, c),
    ensures kill_holds(u, c),
{ assert(u.cpu_array[c as int] == u.cpu_array[c as int]); }

pub proof fn proc_wf_at_of(u: KernelU, p: RwLockProcessPtr)
    requires processes_wf(u), u.process_map.dom().contains(p),
    ensures proc_wf_at(u, p),
{}

// ---------------------------------------------------------------------------------------------------------------------
// Wanted locks.

/// Entering locks the cpu, its process, its running thread, and the child at `child_index`.
pub open spec fn kill_enter_wanted(u: KernelU, c: CpuId, child_index: usize) -> bool {
    let cpu = u.cpu_array[c as int];
    let pp = cpu.current_process->Some_0;
    &&& cpu.lock_state is Unlocked
    &&& u.process_map[pp].lock_state is Unlocked
    &&& u.thread_map[cpu.current_thread->Some_0].lock_state is Unlocked
    &&& u.process_map[u.process_map[pp].children[child_index as int]].lock_state is Unlocked
}

/// Descending locks the target's first child.
pub open spec fn kill_mark_child_wanted(u: KernelU, c: CpuId) -> bool {
    u.process_map[u.process_map[kill_target(u, c)].children[0]].lock_state is Unlocked
}

/// Marking, or leaving dangling, the target's first thread locks it.
pub open spec fn kill_thread_wanted(u: KernelU, c: CpuId) -> bool {
    u.thread_map[u.process_map[kill_target(u, c)].owned_threads[0]].lock_state is Unlocked
}

/// Dequeuing a victim that waits on an endpoint needs that endpoint unlocked; forcing the cpu running the victim to idle
/// needs that cpu unlocked.
pub open spec fn kill_victim_wanted(u: KernelU, c: CpuId) -> bool {
    let vt = u.thread_map[kill_stage(u, c)->Thread_thread];
    &&& vt.state.is_endpoint_waiting() ==> u.endpoint_map[vt.blocking_endpoint_ptr->Some_0].lock_state is Unlocked
    &&& vt.state is RUNNING ==> u.cpu_array[vt.state->RUNNING_cpu_id as int].lock_state is Unlocked
}

/// Locking the empty target's tables needs its page table and IOMMU table unlocked.
pub open spec fn kill_lock_table_wanted(u: KernelU, c: CpuId) -> bool {
    let t = u.process_map[kill_target(u, c)];
    &&& t.pagetable->Some_0.lock_state is Unlocked
    &&& t.iommu_table is Some ==> t.iommu_table->Some_0.lock_state is Unlocked
}

/// Zombifying frees the target's PCID into its container under the container's PCID allocator lock.
pub open spec fn kill_zombify_wanted(u: KernelU, c: CpuId) -> bool {
    u.container_map[u.process_map[kill_target(u, c)].owning_container].pcid_allocator_lock is Unlocked
}

/// Not a lock: retiring raises the container's 4K quota, which U lets fail only at `usize::MAX`.
pub open spec fn kill_retire_quota_room(u: KernelU, c: CpuId) -> bool {
    u.container_map[u.process_map[kill_target(u, c)].owning_container].quota_4k < usize::MAX
}

/// The objects the next step of killer `c` must lock are free.
pub open spec fn kill_wanted_free(u: KernelU, c: CpuId) -> bool {
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let st = kill_stage(u, c);
    let away = tp != kill_own(u, c);
    &&& away && st is Walk && t.children.len() > 0 ==> kill_mark_child_wanted(u, c)
    &&& away && st is Walk && t.children.len() == 0 && t.owned_threads.len() > 0 ==> kill_thread_wanted(u, c)
    &&& away && st is Walk && kill_process_target_empty(u, c) && t.owned_pci_functions.is_empty() && !t.zombie ==> kill_lock_table_wanted(u, c)
    &&& st is Thread ==> kill_victim_wanted(u, c)
    &&& st is Zombie ==> kill_zombify_wanted(u, c)
    &&& st is Retire ==> kill_retire_quota_room(u, c)
}

/// Some kill step of `c` is enabled.
pub open spec fn kill_enabled(u: KernelU, c: CpuId) -> bool {
    exists|l: StepLabel, u2: KernelU| #[trigger] labeled_step(l, u, u2, c) && kill_label(l)
}

/// The kill step preconditions every middle step shares hold for a killer away from its own process.
pub proof fn kill_holds_implies_step_pre(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), in_kill(u, c), kill_holds(u, c), kill_target(u, c) != kill_own(u, c),
    ensures kill_process_step_pre(u, c),
{
    reveal(kill_process_step_pre); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_ownership_wf);
    let tp = kill_target(u, c);
    let pp = kill_own(u, c);
    assert(u.process_map[tp].uppertree_seq.contains(pp));
    assert(u.process_map[pp].owning_container == u.process_map[tp].owning_container);
}

/// Entering is enabled once its wanted locks are free, for a cpu running a live thread whose process has the child.
pub proof fn kill_enter_wanted_free_implies_enter_enabled(u: KernelU, c: CpuId, child_index: usize)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), cpu_runs_live_thread_at_entry(u, c),
        child_index < u.process_map[u.cpu_array[c as int].current_process->Some_0].children.len(), kill_enter_wanted(u, c, child_index),
    ensures kill_process_enter_step_pre(u, c, child_index),
{
    reveal(kill_process_enter_step_pre);
    let pp = u.cpu_array[c as int].current_process->Some_0;
    let ch = u.process_map[pp].children[child_index as int];
    proc_wf_at_of(u, pp);
    assert(u.process_map[pp].children.contains(ch));
    assert(!u.process_map[pp].killed && !u.process_map[ch].killed);
}
} // verus!

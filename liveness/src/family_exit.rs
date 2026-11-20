//! Round 10: `thread_exit` in the world, without its five killed-thread reclaim steps. A cpu inside holds its cpu, its
//! thread, its process, and its container; a process's last thread also holds the process's tables while it reclaims them
//! (it is a `table_killer` then). `exit_holds` lists what each stage keeps, `exit_wanted_free` the objects the next step
//! locks or needs, and `exit_holds_wanted_free_implies_enabled` shows that some step is then enabled.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_kill::*;
use crate::kill_steps::*;
use crate::kill_frame::*;
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;

verus! {
/// The `thread_exit` steps in the world: all but the five killed-thread reclaim steps.
pub open spec fn exit_label(l: StepLabel) -> bool {
    ||| l is ThreadExitEnter || l is ThreadExitDrop || l is ThreadExitRelease || l is ThreadExitLockTable || l is ThreadExitTableHidden
    ||| l is ThreadExitTlbFlush || l is ThreadExitFlushed || l is ThreadExitUnown || l is ThreadExitIommuLeaf || l is ThreadExitRefund || l is ThreadExitQuota
    ||| l is ThreadExitUnlockTable || l is ThreadExitLockPcidAllocator || l is ThreadExitFinish
}

pub open spec fn exit_progress(p: SyscallProgress) -> bool { p is ThreadExit || p is ThreadExitReclaim || p is ThreadExitQuota || p is ThreadExitZombie }

/// `c` is inside `thread_exit`: its cpu is write-locked and its running thread records exit progress.
pub open spec fn in_exit(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some
    &&& exit_progress(cur_thread(u, c).syscall_progress->Some_0)
}

/// The stages that hold the process's tables.
pub open spec fn exit_reclaiming(p: SyscallProgress) -> bool { p is ThreadExitReclaim || p is ThreadExitQuota }

/// The stages after the flush is recorded and before the tables are unlocked.
pub open spec fn exit_cleared(p: SyscallProgress) -> bool { p == (SyscallProgress::ThreadExitReclaim { flushed: true }) || p is ThreadExitQuota }

/// The stage has returned the quota of `size`.
pub open spec fn exit_returned(p: SyscallProgress, size: PageSize) -> bool {
    ||| p is ThreadExitZombie
    ||| p is ThreadExitQuota && (size is SZ4k || size is SZ2m && !(p->ThreadExitQuota_returned is SZ4k) || size is SZ1g && p->ThreadExitQuota_returned is SZ1g)
}

/// What exiting cpu `c` holds: its cpu runs its thread's process; it write-holds its thread, without a caller, its process,
/// and its container; the descriptors before its position are released, all once it reclaims; a reclaiming thread is its
/// process's last, write-holds the page table, finds it cleared after the flush and without PCI functions once it returns quota, and
/// has returned the quota sizes it records.
pub open spec fn exit_holds(u: KernelU, c: CpuId) -> bool {
    let cpu = u.cpu_array[c as int];
    let t = cur_thread(u, c);
    let p = t.owning_proc;
    let pr = u.process_map[p];
    let prog = t.syscall_progress->Some_0;
    let pt = pr.pagetable->Some_0;
    &&& cpu.current_process == Some(p)
    &&& t.owning_container == cpu.owning_container
    &&& t.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& t.caller is None
    &&& u.process_map.dom().contains(p) && pr.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& u.container_map[cpu.owning_container].lock_state == (LockStateU::WriteLocked { writer: c })
    &&& prog is ThreadExit ==> prog->ThreadExit_next <= MAX_NUM_ENDPOINT_DESCRIPTORS
    &&& forall|j: int| #![trigger t.endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS && (!(prog is ThreadExit) || j < prog->ThreadExit_next)
        ==> t.endpoint_descriptors[j] is None
    &&& !(prog is ThreadExit) ==> pr.owned_threads.len() == 1
    &&& exit_reclaiming(prog) ==> pr.pagetable is Some && pt.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& prog is ThreadExitQuota ==> pt.pci_functions == Map::<PciBdf, nat>::empty()
    &&& exit_cleared(prog) ==> pt.mapping_4k == Map::<VAddr, MapEntry>::empty() && pt.mapping_2m == Map::<VAddr, MapEntry>::empty()
        && pt.mapping_1g == Map::<VAddr, MapEntry>::empty() && pt.pagetable_window_locks == Map::<WindowVa, LockStateU>::empty()
    &&& prog is ThreadExitQuota ==> (pr.iommu_table is Some ==> process_iommu_4k_unmapped(pr.iommu_table->Some_0))
    &&& exit_returned(prog, PageSize::SZ4k) ==> pr.quota_4k == 0 && t.quota_4k == 0
    &&& exit_returned(prog, PageSize::SZ2m) ==> pr.quota_2m == 0 && t.quota_2m == 0
    &&& exit_returned(prog, PageSize::SZ1g) ==> pr.quota_1g == 0 && t.quota_1g == 0
}

/// Every exiting cpu holds what its stage needs.
pub open spec fn exit_locks_held(u: KernelU) -> bool { forall|c: CpuId| #![trigger u.cpu_array[c as int]] in_exit(u, c) ==> exit_holds(u, c) }

pub proof fn exit_holds_at(u: KernelU, c: CpuId)
    requires exit_locks_held(u), in_exit(u, c),
    ensures exit_holds(u, c),
{ assert(u.cpu_array[c as int] == u.cpu_array[c as int]); }

/// `d` runs a thread of `p`.
pub open spec fn runs_proc(u: KernelU, d: CpuId, p: RwLockProcessPtr) -> bool {
    index_valid(NUM_CPUS, d) && u.cpu_array[d as int].current_thread is Some && u.cpu_array[d as int].current_process == Some(p)
}

/// A process another cpu write-holds stays with its lock and threads, and changes beyond its subtree set only when `d` runs
/// one of its threads.
pub open spec fn held_procs_kept(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d) ==> {
        &&& u2.process_map.dom().contains(p)
        &&& u2.process_map[p].lock_state == u.process_map[p].lock_state
        &&& u2.process_map[p].owned_threads == u.process_map[p].owned_threads
        &&& proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p]) || runs_proc(u, d, p)
    }
}

pub proof fn kill_frame_implies_held_procs_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kill_frame(u, u2, d),
    ensures held_procs_kept(u, u2, d),
{
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d) implies {
        &&& u2.process_map.dom().contains(p)
        &&& u2.process_map[p].lock_state == u.process_map[p].lock_state
        &&& u2.process_map[p].owned_threads == u.process_map[p].owned_threads
        &&& proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p]) || runs_proc(u, d, p)
    } by { assert(proc_kept(u, u2, d, p)); };
}

pub proof fn kill_d_frame_implies_held_procs_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kill_d_frame(u, u2, d),
    ensures held_procs_kept(u, u2, d),
{
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d) implies {
        &&& u2.process_map.dom().contains(p)
        &&& u2.process_map[p].lock_state == u.process_map[p].lock_state
        &&& u2.process_map[p].owned_threads == u.process_map[p].owned_threads
        &&& proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p]) || runs_proc(u, d, p)
    } by { assert(proc_kview(u2.process_map[p]).lock_state == proc_kview(u.process_map[p]).lock_state); };
}

/// The only thread of a process runs on one cpu: no other cpu runs a thread of it.
pub proof fn sole_thread_implies_not_run_by_other(u: KernelU, x: CpuId, d: CpuId, p: RwLockProcessPtr)
    requires
        kernel_u_ownership_wf(u), index_valid(NUM_CPUS, x), u.cpu_array[x as int].current_thread is Some, u.cpu_array[x as int].current_process == Some(p),
        u.process_map[p].owned_threads.len() == 1, x != d,
    ensures !runs_proc(u, d, p),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    if runs_proc(u, d, p) {
        let tx = u.cpu_array[x as int].current_thread->Some_0;
        let td = u.cpu_array[d as int].current_thread->Some_0;
        assert(u.cpu_array[d as int] == u.cpu_array[d as int]);
        assert(u.thread_map.dom().contains(tx) && u.thread_map.dom().contains(td));
        assert(u.process_map[p].owned_threads.contains(tx) && u.process_map[p].owned_threads.contains(td));
        let s = u.process_map[p].owned_threads;
        let i = choose|i: int| 0 <= i < s.len() && s[i] == tx;
        let j = choose|j: int| 0 <= j < s.len() && s[j] == td;
        assert(i == 0 && j == 0);
        assert(u.thread_map[tx].state == (ThreadState::RUNNING { cpu_id: x }));
        assert(u.thread_map[td].state == (ThreadState::RUNNING { cpu_id: d }));
    }
}

/// The only thread of `tp` runs on `d`, which works on no page table, so no cpu works on the page table of `tp`.
pub proof fn sole_thread_implies_table_unworked(u: KernelU, d: CpuId, tp: RwLockProcessPtr)
    requires
        kernel_u_ownership_wf(u), index_valid(NUM_CPUS, d), u.cpu_array[d as int].current_thread is Some, u.cpu_array[d as int].current_process == Some(tp),
        u.process_map[tp].owned_threads.len() == 1, !table_op(u, d), !table_sharer(u, d),
    ensures table_unworked(u, tp),
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|c: CpuId| #![trigger table_op(u, c)] #![trigger table_sharer(u, c)] table_op(u, c) || table_sharer(u, c) implies table_proc(u, c) != tp by {
        if table_proc(u, c) == tp {
            assert(u.cpu_array[c as int] == u.cpu_array[c as int]);
            sole_thread_implies_not_run_by_other(u, d, c, tp);
        }
    };
}

/// A step that keeps every other cpu, every foreign hold, and every process another cpu holds keeps the holds of every
/// exiting cpu but `d`, given those of `d`.
pub proof fn frame_implies_exit_locks_held_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        kernel_u_ownership_wf(u), exit_locks_held(u), others_kept(u, u2, d), foreign_holds_kept(u, u2, d), held_procs_kept(u, u2, d),
        in_exit(u2, d) ==> exit_holds(u2, d),
    ensures exit_locks_held(u2),
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] in_exit(u2, x) implies exit_holds(u2, x) by {
        if x != d {
            assert(cpu_kept(u, u2, x));
            assert(cur_thread(u2, x) == cur_thread(u, x));
            assert(in_exit(u, x));
            exit_holds_at(u, x);
            let p = cur_thread(u, x).owning_proc;
            let ctn = u.cpu_array[x as int].owning_container;
            assert(held_by_other(u.process_map[p].lock_state, d));
            assert(u.container_map.dom().contains(ctn));
            assert(held_by_other(u.container_map[ctn].lock_state, d));
            if !(cur_thread(u, x).syscall_progress->Some_0 is ThreadExit) {
                sole_thread_implies_not_run_by_other(u, x, d, p);
                assert(proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p]));
                assert(u2.process_map[p].pagetable == u.process_map[p].pagetable && u2.process_map[p].iommu_table == u.process_map[p].iommu_table);
                assert(u2.process_map[p].quota_4k == u.process_map[p].quota_4k && u2.process_map[p].quota_2m == u.process_map[p].quota_2m);
                assert(u2.process_map[p].quota_1g == u.process_map[p].quota_1g);
            }
        }
    };
}

// ---------------------------------------------------------------------------------------------------------------------
// Enabledness.

/// The first descriptor at or after `j` that holds an endpoint, or `MAX_NUM_ENDPOINT_DESCRIPTORS`.
pub open spec fn exit_first_desc(t: ThreadU, j: int) -> int
    decreases MAX_NUM_ENDPOINT_DESCRIPTORS as int - j,
{
    if j < 0 || j >= MAX_NUM_ENDPOINT_DESCRIPTORS as int { MAX_NUM_ENDPOINT_DESCRIPTORS as int }
    else if t.endpoint_descriptors[j] is Some { j } else { exit_first_desc(t, j + 1) }
}

pub proof fn exit_first_desc_bounds(t: ThreadU, j: int)
    requires 0 <= j <= MAX_NUM_ENDPOINT_DESCRIPTORS,
    ensures
        j <= exit_first_desc(t, j) <= MAX_NUM_ENDPOINT_DESCRIPTORS,
        exit_first_desc(t, j) < MAX_NUM_ENDPOINT_DESCRIPTORS ==> t.endpoint_descriptors[exit_first_desc(t, j)] is Some,
        forall|k: int| #![trigger t.endpoint_descriptors[k]] j <= k < exit_first_desc(t, j) ==> t.endpoint_descriptors[k] is None,
    decreases MAX_NUM_ENDPOINT_DESCRIPTORS as int - j,
{
    if j < MAX_NUM_ENDPOINT_DESCRIPTORS as int && !(t.endpoint_descriptors[j] is Some) { exit_first_desc_bounds(t, j + 1); }
}

/// The descriptor the next drop or release of exiting cpu `c` clears, or `MAX_NUM_ENDPOINT_DESCRIPTORS`.
pub open spec fn exit_next_desc(u: KernelU, c: CpuId) -> int { exit_first_desc(cur_thread(u, c), cur_thread(u, c).syscall_progress->Some_0->ThreadExit_next as int) }

/// The objects the next step of exiting cpu `c` locks or needs free: the endpoint of its next descriptor, its process's
/// page table before reclaiming, its container's cpu set while flushing, its process's IOMMU table before giving up the PCI
/// functions, and its container's PCID allocator before finishing.
pub open spec fn exit_wanted_free(u: KernelU, c: CpuId) -> bool {
    let t = cur_thread(u, c);
    let prog = t.syscall_progress->Some_0;
    let pr = u.process_map[t.owning_proc];
    let i = exit_next_desc(u, c);
    let ctn = u.container_map[u.cpu_array[c as int].owning_container];
    &&& prog is ThreadExit && i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> u.endpoint_map[t.endpoint_descriptors[i]->Some_0].lock_state is Unlocked
    &&& prog is ThreadExit && i >= MAX_NUM_ENDPOINT_DESCRIPTORS && pr.owned_threads.len() == 1 ==> pr.pagetable->Some_0.lock_state is Unlocked
    &&& prog == (SyscallProgress::ThreadExitReclaim { flushed: true }) && !exit_unowned(u, c) ==> (pr.iommu_table is Some ==> pr.iommu_table->Some_0.lock_state is Unlocked)
    &&& prog == (SyscallProgress::ThreadExitReclaim { flushed: false }) ==> ctn.cpu_set_lock.read_held_by(c) || !(ctn.cpu_set_lock is WriteLocked)
    &&& prog is ThreadExitZombie ==> ctn.pcid_allocator_lock is Unlocked || ctn.pcid_allocator_lock == (LockStateU::WriteLocked { writer: c })
}

/// The process of exiting cpu `c` has given up its PCI functions: its function array is empty and its IOMMU table, if any, is
/// write-locked.
pub open spec fn exit_unowned(u: KernelU, c: CpuId) -> bool {
    let pr = u.process_map[cur_thread(u, c).owning_proc];
    &&& pr.pagetable->Some_0.pci_functions == Map::<PciBdf, nat>::empty()
    &&& pr.iommu_table is Some ==> pr.iommu_table->Some_0.lock_state is WriteLocked
}

/// Restriction `exit_quota_after_unown` (G22): the first quota step of a reclaiming exit starts once the process has no PCI
/// function. The kernel gives up the functions before returning quota, and every complete `thread_exit` trace does too (its
/// unlock step needs an empty array, and only the flushed reclaim stage can empty it), but `thread_exit_quota_step_pre` does
/// not say so.
pub open spec fn exit_quota_after_unown(u: KernelU, l: StepLabel, d: CpuId) -> bool {
    l is ThreadExitQuota && cur_thread(u, d).syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: true })
        ==> u.process_map[cur_thread(u, d).owning_proc].pagetable->Some_0.pci_functions == Map::<PciBdf, nat>::empty()
}

/// Not a lock (gap G11 in u_gaps.md): the endpoint of the next descriptor, when this is its last reference, has no queue,
/// so that a drop or a release applies.
pub open spec fn exit_endpoint_room(u: KernelU, c: CpuId) -> bool {
    let t = cur_thread(u, c);
    let i = exit_next_desc(u, c);
    let ep = u.endpoint_map[t.endpoint_descriptors[i]->Some_0];
    t.syscall_progress->Some_0 is ThreadExit && i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> ep.owning_threads.len() > 1 || ep.queue.len() == 0
}

/// Some exit step of `c` is enabled.
pub open spec fn exit_enabled(u: KernelU, c: CpuId) -> bool {
    exists|l: StepLabel, u2: KernelU| #[trigger] labeled_step(l, u, u2, c) && exit_label(l)
}

/// A set of at most one element that contains `x` is `{x}`.
pub proof fn small_set_contains_implies_singleton<A>(s: Set<A>, x: A)
    requires s.len() <= 1, s.contains(x),
    ensures s == set![x],
{
    assert(s.remove(x).len() == 0);
    s.remove(x).lemma_len0_is_empty();
    assert forall|y: A| s.contains(y) implies y == x by { if y != x { assert(s.remove(x).contains(y)); } };
    assert(s =~= set![x]);
}

/// The state after `c` finishes its exit, without flushing the default PCID.
pub open spec fn exit_finish_witness(u: KernelU, c: CpuId) -> KernelU {
    let cpu = u.cpu_array[c as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let td = cpu.current_thread->Some_0;
    let container = u.container_map[ctn_ptr];
    let zombie = u.process_map[prc_ptr].owned_threads.remove_value(td).len() == 0;
    let pcid_allocator_lock = if zombie { LockStateU::Unlocked } else { container.pcid_allocator_lock };
    let unlocked = KernelU {
        cpu_array: u.cpu_array.update(c as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..cpu }),
        container_map: u.container_map.insert(ctn_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, pcid_allocator_lock, ..container }),
        process_map: u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..u.process_map[prc_ptr] }),
        ..u
    };
    let thread = unlocked.thread_map[td];
    let process = unlocked.process_map[thread.owning_proc];
    let threads = process.owned_threads.remove_value(td);
    let z = threads.len() == 0;
    KernelU {
        cpu_array: unlocked.cpu_array.update(c as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..unlocked.cpu_array[c as int] }),
        container_map: Map::new(unlocked.container_map.dom(), |cc: RwLockContainerPtr| {
            let ct = unlocked.container_map[cc];
            let quota_4k = if ct.owned_pages.contains(td) { (ct.quota_4k + 1) as usize } else { ct.quota_4k };
            if cc == thread.owning_container {
                ContainerU {
                    zombie: ct.zombie || (z && ct.root_process == thread.owning_proc), owned_threads: ct.owned_threads.remove(td), quota_4k,
                    free_pcids: if z { ct.free_pcids.insert(process.pcid) } else { ct.free_pcids }, ..ct
                }
            } else { ContainerU { quota_4k, ..ct } }
        }),
        process_map: unlocked.process_map.insert(thread.owning_proc, ProcessU {
            zombie: z, pagetable: if z { None } else { process.pagetable }, iommu_table: if z { None } else { process.iommu_table },
            quota_4k: (process.quota_4k + thread.quota_4k) as usize, quota_2m: (process.quota_2m + thread.quota_2m) as usize,
            quota_1g: (process.quota_1g + thread.quota_1g) as usize, owned_threads: threads, ..process
        }),
        thread_map: unlocked.thread_map.remove(td),
        ..unlocked
    }
}

/// Finishing is enabled once its precondition holds.
proof fn exit_finish_pre_implies_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), thread_exit_finish_step_pre(u, c),
    ensures exit_enabled(u, c),
{
    reveal(thread_exit_finish_step); reveal(kernel_u_thread_exit_changed); reveal(kernel_u_cpu_ownership_wf); reveal(thread_exit_finish_step_pre);
    let u2 = exit_finish_witness(u, c);
    assert(u.cpu_array[c as int] == u.cpu_array[c as int]);
    assert(labeled_step(StepLabel::ThreadExitFinish, u, u2, c));
}

/// The quota step of `c` from its progress.
pub open spec fn exit_quota_witness(u: KernelU, c: CpuId) -> KernelU {
    let thrd_ptr = u.cpu_array[c as int].current_thread->Some_0;
    let thread = u.thread_map[thrd_ptr];
    let process = u.process_map[thread.owning_proc];
    let container = u.container_map[thread.owning_container];
    let progress = thread_exit_quota_progress_after(thread.syscall_progress->Some_0);
    let size = progress->Some_0->ThreadExitQuota_returned;
    KernelU {
        container_map: u.container_map.insert(thread.owning_container, match size {
            PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
            PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
            PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
        }),
        process_map: u.process_map.insert(thread.owning_proc, match size {
            PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
            PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
            PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
        }),
        thread_map: u.thread_map.insert(thrd_ptr, match size {
            PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
            PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
            PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
        }),
        ..u
    }
}

/// Before reclaiming the exiting thread drops or releases its next descriptor, locks the tables, or finishes.
proof fn exit_descriptors_implies_enabled(u: KernelU, c: CpuId)
    requires
        kernel_u_ownership_wf(u), processes_wf(u), in_exit(u, c), exit_holds(u, c), exit_wanted_free(u, c), exit_endpoint_room(u, c),
        cur_thread(u, c).syscall_progress->Some_0 is ThreadExit,
    ensures exit_enabled(u, c),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
    let cpu = u.cpu_array[c as int];
    let td = cpu.current_thread->Some_0;
    let t = u.thread_map[td];
    let p = t.owning_proc;
    let pr = u.process_map[p];
    let next = t.syscall_progress->Some_0->ThreadExit_next;
    let i = exit_next_desc(u, c);
    assert(u.cpu_array[c as int] == u.cpu_array[c as int]);
    exit_first_desc_bounds(t, next as int);
    if i < MAX_NUM_ENDPOINT_DESCRIPTORS {
        let e = t.endpoint_descriptors[i]->Some_0;
        let ep = u.endpoint_map[e];
        let ix = i as EndpointIdx;
        assert(u.thread_map[td].endpoint_descriptors[ix as int] is Some);
        assert(u.endpoint_map.dom().contains(e) && ep.owning_threads.contains((td, ix)));
        let nt = ThreadU { endpoint_descriptors: t.endpoint_descriptors.update(i, None), syscall_progress: Some(SyscallProgress::ThreadExit { next: (ix + 1) as EndpointIdx }), ..t };
        reveal(thread_exit_drop_step_pre);
        if ep.owning_threads.len() > 1 {
            reveal(thread_exit_drop_step);
            let u2 = KernelU {
                thread_map: u.thread_map.insert(td, nt),
                endpoint_map: u.endpoint_map.insert(e, EndpointU { owning_threads: ep.owning_threads.remove((td, ix)), ..ep }),
                ..u
            };
            assert(labeled_step(StepLabel::ThreadExitDrop, u, u2, c));
        } else {
            reveal(thread_exit_release_step); reveal(kernel_u_endpoint_released);
            small_set_contains_implies_singleton(ep.owning_threads, (td, ix));
            assert(ep.queue =~= Seq::<RwLockThreadPtr>::empty());
            let cm = Map::new(u.container_map.dom(), |cc: RwLockContainerPtr| {
                let container = u.container_map[cc];
                ContainerU {
                    owned_endpoints: if cc == ep.owning_container { container.owned_endpoints.remove(e) } else { container.owned_endpoints },
                    quota_4k: if container.owned_pages.contains(e) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
                }
            });
            let u2 = KernelU { container_map: cm, thread_map: u.thread_map.insert(td, nt), endpoint_map: u.endpoint_map.remove(e), ..u };
            assert(labeled_step(StepLabel::ThreadExitRelease, u, u2, c));
        }
    } else {
        assert forall|j: int| #![trigger t.endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS implies t.endpoint_descriptors[j] is None by {
            if j >= next { assert(t.endpoint_descriptors[j] is None); }
        };
        assert(pr.owned_threads.contains(td));
        proc_wf_at_of(u, p);
        if pr.owned_threads.len() == 1 {
            reveal(thread_exit_lock_table_step_pre); reveal(thread_exit_lock_table_step);
            let u2 = KernelU {
                thread_map: u.thread_map.insert(td, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..t }),
                process_map: u.process_map.insert(p, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: c }, ..pr.pagetable->Some_0 }), ..pr }),
                ..u
            };
            assert(labeled_step(StepLabel::ThreadExitLockTable, u, u2, c));
        } else {
            reveal(thread_exit_finish_step_pre);
            assert(thread_exit_finish_step_pre(u, c));
            exit_finish_pre_implies_enabled(u, c);
        }
    }
}

/// While reclaiming the exiting thread hides, flushes, removes an IOMMU leaf, returns quota, or unlocks; a zombie locks
/// the PCID allocator or finishes.
proof fn exit_reclaim_implies_enabled(u: KernelU, c: CpuId)
    requires
        kernel_u_ownership_wf(u), in_exit(u, c), exit_holds(u, c), exit_wanted_free(u, c), !(cur_thread(u, c).syscall_progress->Some_0 is ThreadExit),
    ensures exit_enabled(u, c),
{
    reveal(kernel_u_cpu_ownership_wf);
    let cpu = u.cpu_array[c as int];
    let td = cpu.current_thread->Some_0;
    let t = u.thread_map[td];
    let p = t.owning_proc;
    let pr = u.process_map[p];
    let prog = t.syscall_progress->Some_0;
    let ctn_ptr = t.owning_container;
    let ctn = u.container_map[ctn_ptr];
    assert(u.cpu_array[c as int] == u.cpu_array[c as int]);
    reveal(thread_exit_reclaim_step_pre);
    if prog == (SyscallProgress::ThreadExitReclaim { flushed: false }) {
        reveal(thread_exit_flush_step_pre);
        if thread_exit_flush_step_pre(u, c) {
            if ctn.cpu_set_lock.read_held_by(c) {
                reveal(thread_exit_flushed_step);
                let u2 = KernelU {
                    thread_map: u.thread_map.insert(td, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: true }), ..t }),
                    container_map: u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: ctn.cpu_set_lock.without_reader(c), ..ctn }),
                    ..u
                };
                assert(labeled_step(StepLabel::ThreadExitFlushed, u, u2, c));
            } else {
                reveal(thread_exit_tlb_flush_step);
                let u2 = KernelU { container_map: u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: ctn.cpu_set_lock.with_reader(c), ..ctn }), ..u };
                assert(labeled_step(StepLabel::ThreadExitTlbFlush, u, u2, c));
            }
        } else {
            reveal(process_table_hidden_step);
            let o = pr.pagetable->Some_0;
            assert(o.mapping_4k.restrict(o.mapping_4k.dom()) =~= o.mapping_4k);
            assert(o.mapping_2m.restrict(o.mapping_2m.dom()) =~= o.mapping_2m);
            assert(o.mapping_1g.restrict(o.mapping_1g.dom()) =~= o.mapping_1g);
            assert(o.pagetable_window_locks.restrict(o.pagetable_window_locks.dom()) =~= o.pagetable_window_locks);
            assert(u.process_map.insert(p, pr) =~= u.process_map);
            assert(labeled_step(StepLabel::ThreadExitTableHidden, u, u, c));
        }
    } else if prog == (SyscallProgress::ThreadExitReclaim { flushed: true }) && !exit_unowned(u, c) {
        reveal(thread_exit_unown_step_pre); reveal(thread_exit_unown_step);
        let pagetable = pr.pagetable->Some_0;
        let functions = pagetable.pci_functions.dom();
        let table = u.iommu_root_table;
        let u2 = KernelU {
            process_map: u.process_map.insert(p, ProcessU {
                pagetable: Some(PageTableU { pci_functions: Map::empty(), ..pagetable }),
                iommu_table: match pr.iommu_table { Some(x) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: c }, did: None, ..x }), None => None },
                ..pr
            }),
            iommu_root_table: IommuRootTableU {
                owners: if functions == Set::<PciBdf>::empty() { table.owners } else { pci_owners_released(table.owners, functions) },
                attached: if pr.iommu_table is Some { thread_exit_detached_attached(table, functions) } else { table.attached },
            },
            iommu_tlb: if pr.iommu_table is Some && pr.iommu_table->Some_0.did is Some {
                u.iommu_tlb.insert(pr.iommu_table->Some_0.did->Some_0, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            } else { u.iommu_tlb },
            ..u
        };
        assert(labeled_step(StepLabel::ThreadExitUnown, u, u2, c));
    } else if prog == (SyscallProgress::ThreadExitReclaim { flushed: true }) && pr.iommu_table is Some && !process_iommu_4k_unmapped(pr.iommu_table->Some_0) {
        reveal(thread_exit_iommu_leaf_step);
        let it = pr.iommu_table->Some_0;
        let m = it.mapping_4k;
        let iova = choose|iova: VAddr| m.dom().contains(iova);
        let kept = m.dom().remove(iova);
        let u2 = KernelU { process_map: u.process_map.insert(p, ProcessU { iommu_table: Some(PageTableU { mapping_4k: m.restrict(kept), ..it }), ..pr }), ..u };
        assert(m.restrict(kept).dom() =~= kept);
        assert(m.dom().difference(kept) =~= set![iova]);
        assert(labeled_step(StepLabel::ThreadExitIommuLeaf, u, u2, c));
    } else if prog == (SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g }) {
        reveal(thread_exit_unlock_table_step_pre); reveal(thread_exit_unlock_table_step);
        let u2 = KernelU {
            thread_map: u.thread_map.insert(td, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitZombie), ..t }),
            process_map: u.process_map.insert(p, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pr.pagetable->Some_0 }),
                iommu_table: match pr.iommu_table { Some(x) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..x }), None => None },
                ..pr
            }),
            ..u
        };
        assert(labeled_step(StepLabel::ThreadExitUnlockTable, u, u2, c));
    } else if prog is ThreadExitZombie {
        reveal(thread_exit_finish_step_pre);
        assert(forall|j: int| #![trigger t.endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> t.endpoint_descriptors[j] is None);
        assert(thread_exit_finish_step_pre(u, c));
        if ctn.pcid_allocator_lock is Unlocked {
            reveal(thread_exit_lock_pcid_allocator_step_pre); reveal(thread_exit_lock_pcid_allocator_step);
            let u2 = KernelU { container_map: u.container_map.insert(ctn_ptr, ContainerU { pcid_allocator_lock: LockStateU::WriteLocked { writer: c }, ..ctn }), ..u };
            assert(labeled_step(StepLabel::ThreadExitLockPcidAllocator, u, u2, c));
        } else {
            exit_finish_pre_implies_enabled(u, c);
        }
    } else {
        reveal(thread_exit_quota_step_pre); reveal(thread_exit_quota_step);
        assert(thread_exit_quota_progress_after(prog) is Some);
        assert(labeled_step(StepLabel::ThreadExitQuota, u, exit_quota_witness(u, c), c));
    }
}

/// Property (a) for `thread_exit`, never blocked on free objects: an exiting cpu that holds what its stage needs and whose
/// wanted objects are free has an enabled exit step.
pub proof fn exit_holds_wanted_free_implies_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), processes_wf(u), in_exit(u, c), exit_holds(u, c), exit_wanted_free(u, c), exit_endpoint_room(u, c),
    ensures exit_enabled(u, c),
{
    if cur_thread(u, c).syscall_progress->Some_0 is ThreadExit { exit_descriptors_implies_enabled(u, c); } else { exit_reclaim_implies_enabled(u, c); }
}
} // verus!

use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// The running thread of cpu `c`.
pub open spec fn cur_thread(u: KernelU, c: CpuId) -> ThreadU { u.thread_map[u.cpu_array[c as int].current_thread->Some_0] }

/// What a step of another cpu must leave alone for `c`: its cpu entry and its running thread.
pub open spec fn cpu_slice(u: KernelU, c: CpuId) -> (CpuU, ThreadU) { (u.cpu_array[c as int], cur_thread(u, c)) }

/// `c` is inside endpoint creation: its cpu is write-locked and its running thread records `NewEndpoint` progress.
pub open spec fn in_new_endpoint(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some
    &&& cur_thread(u, c).syscall_progress->Some_0 is NewEndpoint
}

/// `c` is inside a 4K mapping: its cpu is write-locked and its running thread records `Mmap4k` progress, or records none
/// and is write-locked since the hold step.
pub open spec fn in_mmap_4k(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some ==> cur_thread(u, c).syscall_progress->Some_0 is Mmap4k
    &&& cur_thread(u, c).syscall_progress is None ==> cur_thread(u, c).lock_state == (LockStateU::WriteLocked { writer: c })
        && u.cpu_array[c as int].lock_state == (LockStateU::WriteLocked { writer: c })
}

/// `c` is inside a multi-step pilot syscall (`alloc_quota_4k` is a single step and has no inside).
pub open spec fn in_pilot(u: KernelU, c: CpuId) -> bool { in_new_endpoint(u, c) || in_mmap_4k(u, c) }

/// Remaining work of `c` inside a pilot syscall: every 4K mapping step but downgrading and entering to fill consumes one
/// 4K quota of the thread, so the thread's quota plus one for a pending downgrade and two for a pending fill entry bounds
/// the steps before the exit step; endpoint creation has only its finish step left.
pub open spec fn pilot_measure(u: KernelU, c: CpuId) -> nat {
    let t = cur_thread(u, c);
    if !in_mmap_4k(u, c) { 0 }
    else if t.syscall_progress is None { t.quota_4k as nat + 2 }
    else if t.syscall_progress->Some_0->Mmap4k_phase is Fill { t.quota_4k as nat + 1 }
    else { t.quota_4k as nat }
}

/// Some step of `c` inside a pilot syscall is enabled: finishing endpoint creation, or a release, directory, downgrade,
/// leaf, or exit step of a 4K mapping.
pub open spec fn pilot_next_pre(u: KernelU, c: CpuId) -> bool {
    ||| new_endpoint_finish_step_pre(u, c) || mmap_4k_release_step_pre(u, c) || mmap_4k_directory_step_pre(u, c)
    ||| mmap_4k_downgrade_step_pre(u, c) || mmap_4k_leaf_step_pre(u, c) || mmap_4k_exit_step_pre(u, c)
}

/// `c` is inside a pilot syscall and a step of it is enabled.
pub open spec fn pilot_enabled(c: CpuId) -> spec_fn(KernelU) -> bool { |u: KernelU| in_pilot(u, c) && pilot_next_pre(u, c) }

/// Cpu `w` can move `amount` 4K quota from its container to its process.
pub open spec fn alloc_enabled(w: CpuId, amount: usize) -> spec_fn(KernelU) -> bool { |u: KernelU| alloc_quota_4k_step_pre(u, w, amount) }

/// The 4K quota allocation of `amount`.
pub open spec fn alloc_taken(amount: usize) -> spec_fn(StepLabel) -> bool { |l: StepLabel| l == (StepLabel::AllocQuota4k { alloc_amount: amount }) }

/// Container `ctn` is unlocked and has no concrete lock owner.
pub open spec fn container_unlocked(u: KernelU, ctn: RwLockContainerPtr) -> bool {
    u.container_map[ctn].lock_state is Unlocked && u.container_map[ctn].lock_process_owner is None
}

/// `alloc_quota_4k` of a process at depth `depth` in container `ctn` would return `ErrorContainerLockOrderConflict`:
/// `ctn` is write-held by a live owner below that depth.
pub open spec fn lock_order_conflict(u: KernelU, ctn: RwLockContainerPtr, depth: usize) -> bool {
    u.container_map[ctn].lock_process_owner is Some && u.container_map[ctn].lock_process_owner->Some_0 < LockOwnerId::Some(depth)
}

/// Every cpu inside endpoint creation write-holds its container, its process, and its running thread, and records a
/// valid descriptor index.
pub open spec fn new_endpoint_locks_held(u: KernelU) -> bool {
    forall|x: CpuId| #![trigger u.cpu_array[x as int]] in_new_endpoint(u, x) ==> {
        let cpu = u.cpu_array[x as int];
        &&& u.container_map[cpu.owning_container].lock_state == (LockStateU::WriteLocked { writer: x })
        &&& u.process_map[cpu.current_process->Some_0].lock_state == (LockStateU::WriteLocked { writer: x })
        &&& cur_thread(u, x).lock_state == (LockStateU::WriteLocked { writer: x })
        &&& edp_idx_valid(cur_thread(u, x).syscall_progress->Some_0->NewEndpoint_slot)
    }
}

/// A concrete owner of container `ctn` is the cpu that write-holds it inside endpoint creation of its own container.
pub open spec fn container_owner_held(u: KernelU, ctn: RwLockContainerPtr) -> bool {
    let x = u.container_map[ctn].lock_state->WriteLocked_writer;
    u.container_map[ctn].lock_process_owner is Some ==> {
        &&& u.container_map[ctn].lock_state is WriteLocked
        &&& in_new_endpoint(u, x)
        &&& u.cpu_array[x as int].owning_container == ctn
    }
}

/// An own pilot step of `c`: only entering creates endpoint-creation progress, which writes the three locks and keeps the
/// cpu's container and process; inside a pilot syscall the step is not an entry, from endpoint creation it is the finish
/// step, and it leaves the syscall or decreases `pilot_measure`.
pub proof fn pilot_own_step_implies_measure_decreases(u: KernelU, u2: KernelU, l: StepLabel, c: CpuId)
    requires kernel_u_ownership_wf(u), pilot_label(l), labeled_step(l, u, u2, c),
    ensures
        in_new_endpoint(u2, c) ==> l is NewEndpointEnter,
        l is NewEndpointEnter ==> {
            &&& in_new_endpoint(u2, c)
            &&& u2.cpu_array[c as int].owning_container == u.cpu_array[c as int].owning_container
            &&& u2.cpu_array[c as int].current_process == u.cpu_array[c as int].current_process
            &&& cur_thread(u2, c).lock_state == (LockStateU::WriteLocked { writer: c })
            &&& edp_idx_valid(cur_thread(u2, c).syscall_progress->Some_0->NewEndpoint_slot)
        },
        in_pilot(u, c) ==> !(l is NewEndpointEnter) && (in_pilot(u2, c) ==> pilot_measure(u2, c) < pilot_measure(u, c)),
        in_new_endpoint(u, c) ==> l is NewEndpointFinish,
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        _ => {},
    }
}

/// A pilot step of another cpu `d` leaves the cpu entry of `c` and, when `c` runs a thread, that thread unchanged: the two
/// running threads differ because each is RUNNING on its own cpu.
pub proof fn pilot_other_step_implies_cpu_slice_unchanged(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, c: CpuId)
    requires kernel_u_ownership_wf(u), pilot_label(l), labeled_step(l, u, u2, d), d != c, index_valid(NUM_CPUS, c),
    ensures
        u2.cpu_array[c as int] == u.cpu_array[c as int],
        u.cpu_array[c as int].current_thread is Some ==> cur_thread(u2, c) == cur_thread(u, c),
        cpu_slice(u2, c) == cpu_slice(u, c) || u.cpu_array[c as int].current_thread is None,
{
    reveal(kernel_u_cpu_ownership_wf);
    let uc = u.cpu_array[c as int];
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        _ => {},
    }
    if uc.current_thread is Some && ud.current_thread is Some && uc.current_thread == ud.current_thread {
        assert(u.thread_map[uc.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: c }));
    }
}

/// Container `ctn` changes its lock only when the stepping cpu `d` enters endpoint creation in it, which write-locks it
/// under the depth of `d`'s process, or finishes endpoint creation in it, which unlocks it with no owner.
pub proof fn pilot_step_implies_container_lock_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, ctn: RwLockContainerPtr)
    requires kernel_u_ownership_wf(u), pilot_label(l), labeled_step(l, u, u2, d),
    ensures ({
        let o = u.container_map[ctn];
        let n = u2.container_map[ctn];
        let cpu = u.cpu_array[d as int];
        if l is NewEndpointEnter && ctn == cpu.owning_container {
            n.lock_state == (LockStateU::WriteLocked { writer: d }) && n.lock_process_owner == Some(LockOwnerId::Some(u.process_map[cpu.current_process->Some_0].depth))
        } else if l is NewEndpointFinish && ctn == cpu.owning_container {
            container_unlocked(u2, ctn)
        } else { n.lock_state == o.lock_state && n.lock_process_owner == o.lock_process_owner }
    }),
{
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        _ => {},
    }
}

/// Process `prc` changes its lock only when the stepping cpu `d` enters endpoint creation from it, which write-locks it,
/// or finishes endpoint creation from it, which unlocks it.
pub proof fn pilot_step_implies_process_lock_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, prc: RwLockProcessPtr)
    requires kernel_u_ownership_wf(u), pilot_label(l), labeled_step(l, u, u2, d),
    ensures ({
        let n = u2.process_map[prc].lock_state;
        let cpu = u.cpu_array[d as int];
        if l is NewEndpointEnter && prc == cpu.current_process->Some_0 { n == (LockStateU::WriteLocked { writer: d }) }
        else if l is NewEndpointFinish && prc == cpu.current_process->Some_0 { n is Unlocked }
        else { n == u.process_map[prc].lock_state }
    }),
{
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        _ => {},
    }
}

/// Every pilot step keeps `new_endpoint_locks_held`.
pub proof fn pilot_step_implies_new_endpoint_locks_held(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), new_endpoint_locks_held(u), pilot_label(l), labeled_step(l, u, u2, d),
    ensures new_endpoint_locks_held(u2),
{
    pilot_own_step_implies_measure_decreases(u, u2, l, d);
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] in_new_endpoint(u2, x) implies {
        let cpu = u2.cpu_array[x as int];
        &&& u2.container_map[cpu.owning_container].lock_state == (LockStateU::WriteLocked { writer: x })
        &&& u2.process_map[cpu.current_process->Some_0].lock_state == (LockStateU::WriteLocked { writer: x })
        &&& cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x })
        &&& edp_idx_valid(cur_thread(u2, x).syscall_progress->Some_0->NewEndpoint_slot)
    } by {
        let cx = u.cpu_array[x as int];
        let cd = u.cpu_array[d as int];
        pilot_step_implies_container_lock_frame(u, u2, l, d, cx.owning_container);
        pilot_step_implies_process_lock_frame(u, u2, l, d, cx.current_process->Some_0);
        if x != d {
            pilot_other_step_implies_cpu_slice_unchanged(u, u2, l, d, x);
            assert(in_new_endpoint(u, x));
            if l is NewEndpointEnter { reveal(new_endpoint_enter_step_pre); }
            if l is NewEndpointFinish {
                reveal(new_endpoint_finish_step_pre);
                assert(in_new_endpoint(u, d) && u.cpu_array[d as int] == cd);
            }
        }
    };
}

/// Every pilot step keeps `container_owner_held` for container `ctn`.
pub proof fn pilot_step_implies_container_owner_held(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, ctn: RwLockContainerPtr)
    requires kernel_u_ownership_wf(u), container_owner_held(u, ctn), pilot_label(l), labeled_step(l, u, u2, d),
    ensures container_owner_held(u2, ctn),
{
    pilot_own_step_implies_measure_decreases(u, u2, l, d);
    pilot_step_implies_container_lock_frame(u, u2, l, d, ctn);
    let x = u.container_map[ctn].lock_state->WriteLocked_writer;
    if u.container_map[ctn].lock_process_owner is Some && x != d { pilot_other_step_implies_cpu_slice_unchanged(u, u2, l, d, x); }
}

/// The cpu `c` inside endpoint creation can finish when `new_endpoint_locks_held` holds.
pub proof fn new_endpoint_locks_held_implies_finish_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), new_endpoint_locks_held(u), in_new_endpoint(u, c),
    ensures new_endpoint_finish_step_pre(u, c), pilot_enabled(c)(u),
{
    reveal(kernel_u_cpu_ownership_wf);
    reveal(new_endpoint_finish_step_pre);
    assert(u.cpu_array[c as int] == u.cpu_array[c as int]);
}

/// A pilot step that does not let a process shallower than `depth` enter endpoint creation in container `ctn` keeps
/// `ctn` free of a lock-order conflict for that depth.
pub proof fn pilot_step_implies_no_lock_order_conflict_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, ctn: RwLockContainerPtr, depth: usize)
    requires
        kernel_u_ownership_wf(u), pilot_label(l), labeled_step(l, u, u2, d), !lock_order_conflict(u, ctn, depth),
        l is NewEndpointEnter && u.cpu_array[d as int].owning_container == ctn ==> u.process_map[u.cpu_array[d as int].current_process->Some_0].depth >= depth,
    ensures !lock_order_conflict(u2, ctn, depth),
{ pilot_step_implies_container_lock_frame(u, u2, l, d, ctn); }

/// Without a lock-order conflict for the depth of its process, `alloc_quota_4k` on cpu `w` does not return
/// `ErrorContainerLockOrderConflict`.
pub proof fn no_lock_order_conflict_implies_alloc_quota_4k_result_not_conflict(u: KernelU, w: CpuId, amount: usize)
    requires !lock_order_conflict(u, u.cpu_array[w as int].owning_container, u.process_map[u.cpu_array[w as int].current_process->Some_0].depth),
    ensures alloc_quota_4k_syscall_result(u, w, amount) != RetValueType::ErrorContainerLockOrderConflict,
{}

/// Finding about `unmap_4k`: when the cpu already reads the cpu set of its container, its whole-PCID flush step may leave
/// the user state unchanged, so the step relation lets the cpu flush forever without progress and no measure on the
/// user state decreases on every own step of `unmap_4k`.
pub proof fn unmap_4k_flush_pre_and_cpu_set_read_implies_flush_stutter(u: KernelU, c: CpuId)
    requires
        unmap_4k_flush_step_pre(u, c),
        TLB_FLUSH_VA_RANGE_MAX_PAGES_4K < cur_thread(u, c).syscall_progress->Some_0->Unmap4k_range.len,
        u.container_map[cur_thread(u, c).owning_container].cpu_set_lock.read_held_by(c),
    ensures labeled_step(StepLabel::Unmap4kTlbFlush, u, u, c),
{
    reveal(unmap_4k_flush_step_pre);
    reveal(unmap_4k_tlb_flush_step);
    let ctn = cur_thread(u, c).owning_container;
    let lock = u.container_map[ctn].cpu_set_lock;
    assert(lock.with_reader(c) == lock) by { assert(lock.readers().insert(c) =~= lock->readers); };
    assert(u.container_map.insert(ctn, ContainerU { cpu_set_lock: lock.with_reader(c), ..u.container_map[ctn] }) =~= u.container_map);
}
} // verus!

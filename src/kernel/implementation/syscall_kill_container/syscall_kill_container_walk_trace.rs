use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::*;

verus! {
/// A cpu that is not running or is marked by a killer makes the container kill return CpuIdle.
pub(crate) proof fn kill_container_idle_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        !(krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !krnl.cpu_arr.spec_index(cpu_id).view().being_killed()),
    ensures kill_container_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index) is CpuIdle,
{ kernel_cpu_projection_at(krnl, cpu_id); }

/// On a running unmarked cpu that runs `thread_ptr` of `process_ptr` in `container_ptr`, a marked container, a
/// container write-held by a live owner below the process's depth, a marked process or thread, a child index past the
/// container's children, and a marked child container each reject the kill.
pub(crate) proof fn kill_container_result_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, child_index: usize, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.ctn_mp.dom().contains(container_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
    ensures
        ({
            let container = krnl.ctn_mp.spec_index(container_ptr);
            let children = container.view().children.view();
            let owner = container.lock_process_owner_u();
            let conflict = owner is Some && owner->Some_0 < LockOwnerId::Some(krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth);
            let live = !container.being_killed() && !conflict && !krnl.prc_mp.spec_index(process_ptr).being_killed() && !krnl.thr_mp.spec_index(thread_ptr).being_killed();
            let result = kill_container_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index);
            &&& container.being_killed() ==> result is ErrorContainerKilled
            &&& !container.being_killed() && conflict ==> result is ErrorContainerLockOrderConflict
            &&& !container.being_killed() && !conflict && krnl.prc_mp.spec_index(process_ptr).being_killed() ==> result is ErrorProcessKilled
            &&& !container.being_killed() && !conflict && !krnl.prc_mp.spec_index(process_ptr).being_killed() && krnl.thr_mp.spec_index(thread_ptr).being_killed() ==> result is ErrorThreadKilled
            &&& live && child_index >= children.len() ==> result is ErrorInvalidChild
            &&& live && child_index < children.len() && krnl.ctn_mp.dom().contains(children[child_index as int]) && krnl.ctn_mp.spec_index(children[child_index as int]).being_killed() ==> result is ErrorContainerKilled
        }),
{
    let children = krnl.ctn_mp.spec_index(container_ptr).view().children.view();
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_thread_projection_at(krnl, thread_ptr); kernel_container_projection_at(krnl, container_ptr);
    kernel_process_projection_at(krnl, process_ptr);
    if child_index < children.len() && krnl.ctn_mp.dom().contains(children[child_index as int]) { kernel_container_projection_at(krnl, children[child_index as int]); }
}

/// The unlocked running unmarked cpu, container, process, and thread with no syscall in progress, whose container's
/// live child at `child_index` is `child_ptr`, are so on the projection, where the container kill succeeds.
pub(crate) proof fn kill_container_enter_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, child_index: usize, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, child_ptr: RwLockContainerPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let container = krnl.ctn_mp.spec_index(container_ptr);
            let process = krnl.prc_mp.spec_index(process_ptr);
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            &&& !cpu.locked()
            &&& cpu.view().view().state is Running
            &&& !cpu.being_killed()
            &&& cpu.view().view().owning_container == container_ptr
            &&& cpu.view().view().current_process == Some(process_ptr)
            &&& cpu.view().view().current_thread == Some(thread_ptr)
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& !container.locked()
            &&& !container.being_killed()
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& !process.locked()
            &&& !process.being_killed()
            &&& krnl.thr_mp.dom().contains(thread_ptr)
            &&& !thread.locked()
            &&& !thread.being_killed()
            &&& thread.view().syscall_progress.view() is None
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == process_ptr
            &&& child_index < container.view().children.view().len()
            &&& container.view().children.view()[child_index as int] == child_ptr
            &&& krnl.ctn_mp.dom().contains(child_ptr)
            &&& !krnl.ctn_mp.spec_index(child_ptr).being_killed()
        }),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let cpu = u.cpu_array[cpu_id as int];
            let container = u.container_map[container_ptr];
            let process = u.process_map[process_ptr];
            let thread = u.thread_map[thread_ptr];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& !cpu.killed
            &&& cpu.owning_container == container_ptr
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& u.container_map.dom().contains(container_ptr)
            &&& container.lock_state is Unlocked
            &&& !container.killed
            &&& u.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& u.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& child_index < container.children.len()
            &&& container.children[child_index as int] == child_ptr
            &&& u.container_map.dom().contains(child_ptr)
            &&& !u.container_map[child_ptr].killed
            &&& process.depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
        }),
        kill_container_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index) is Success,
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_thread_projection_at(krnl, thread_ptr); kernel_process_projection_at(krnl, process_ptr);
    kernel_container_projection_at(krnl, container_ptr); kernel_container_projection_at(krnl, child_ptr);
}

/// Write-locking the cpu, its container `container_ptr`, the process, and the thread, marking and write-locking the
/// container's child `child_ptr` at `child_index`, and recording the walk of the child is the enter step.
pub(crate) proof fn kill_container_enter_step_from_u(
    pre: KernelU, locked: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, child_ptr: RwLockContainerPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        container_ptr != child_ptr,
        ({
            let cpu = pre.cpu_array[cpu_id as int];
            let container = pre.container_map[container_ptr];
            let process = pre.process_map[process_ptr];
            let thread = pre.thread_map[thread_ptr];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.owning_container == container_ptr
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.container_map.dom().contains(container_ptr)
            &&& container.lock_state is Unlocked
            &&& !container.killed
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& child_index < container.children.len()
            &&& container.children[child_index as int] == child_ptr
            &&& pre.container_map.dom().contains(child_ptr)
            &&& !pre.container_map[child_ptr].killed
        }),
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(pre.process_map[process_ptr].depth)), ..pre.container_map[container_ptr]
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
        marked == (KernelU {
            container_map: locked.container_map.insert(child_ptr, ContainerU { lock_state: LockStateU::WriteLocked, killed: true, ..locked.container_map[child_ptr] }), ..locked
        }),
        post == (KernelU {
            thread_map: marked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_container_progress(child_ptr, ContainerKillStage::Walk), ..marked.thread_map[thread_ptr] }),
            ..marked
        }),
    ensures
        kill_container_enter_step_pre(pre, cpu_id, child_index),
        kill_container_enter_step(pre, post, cpu_id, child_index),
{
    reveal(kill_container_enter_step_pre); reveal(kill_container_enter_step);
    assert(post.thread_map =~= pre.thread_map.insert(thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked, syscall_progress: kill_container_progress(child_ptr, ContainerKillStage::Walk), ..pre.thread_map[thread_ptr]
    }));
}

/// The one step pushed since `before` is the partial trace of the container kill after entering.
pub(crate) proof fn kill_container_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        kill_container_enter_step_pre(pre, cpu_id, child_index),
        kill_container_enter_step(pre, post, cpu_id, child_index),
    ensures kill_partial_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, KillTraceCtx::Container { child_index }),
{ reveal(kill_partial_trace); reveal(kill_container_partial_trace); }

/// The container `child_ptr` on `krnl` is a container on the projection.
pub(crate) proof fn kill_container_mark_child_pre_from_k(krnl: &KernelK, child_ptr: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(child_ptr),
    ensures kernel_k_to_kernel_u(*krnl).container_map.dom().contains(child_ptr),
{ kernel_u_domains_projection(krnl); }

/// The root process `root_ptr` of the target `target` on `krnl` is its root process on the projection.
pub(crate) proof fn kill_container_mark_root_pre_from_k(krnl: &KernelK, target: RwLockContainerPtr, root_ptr: RwLockProcessPtr)
    requires
        krnl.ctn_mp.dom().contains(target),
        krnl.ctn_mp.spec_index(target).view().root_process == root_ptr,
        krnl.prc_mp.dom().contains(root_ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map[target].root_process == root_ptr,
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(root_ptr),
{ kernel_container_projection_at(krnl, target); kernel_u_domains_projection(krnl); }

/// Marking and write-locking the first child `child_ptr` of the target `target` and walking the child is a middle step
/// of the container kill.
pub(crate) proof fn kill_container_mark_child_step_from_u(
    pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockContainerPtr, child_ptr: RwLockContainerPtr,
)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_container_target(pre, cpu_id) == target,
        kill_container_stage(pre, cpu_id) is Walk,
        0 < pre.container_map[target].children.len(),
        pre.container_map[target].children[0] == child_ptr,
        pre.container_map.dom().contains(child_ptr),
        marked == (KernelU {
            container_map: pre.container_map.insert(child_ptr, ContainerU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.container_map[child_ptr] }), ..pre
        }),
        post == (KernelU {
            thread_map: marked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_container_progress(child_ptr, ContainerKillStage::Walk), ..marked.thread_map[thread_ptr] }),
            ..marked
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_container_mark_child_step); }

/// Marking and write-locking the root process `root_ptr` of the childless target `target`, which owns processes, and
/// walking that process is a middle step of the container kill.
pub(crate) proof fn kill_container_mark_root_step_from_u(
    pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockContainerPtr, root_ptr: RwLockProcessPtr,
)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_container_target(pre, cpu_id) == target,
        kill_container_stage(pre, cpu_id) is Walk,
        pre.container_map[target].children.len() == 0,
        !pre.container_map[target].owned_processes.is_empty(),
        pre.container_map[target].root_process == root_ptr,
        pre.process_map.dom().contains(root_ptr),
        marked == (KernelU {
            process_map: pre.process_map.insert(root_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.process_map[root_ptr] }), ..pre
        }),
        post == (KernelU {
            thread_map: marked.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: kill_container_progress(target, ContainerKillStage::Process { process: root_ptr, stage: KillStage::Walk }), ..marked.thread_map[thread_ptr]
            }),
            ..marked
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_container_mark_root_step); }

/// The killer write-holding its cpu, its cpu's container `container_ptr`, its process, and itself, whose progress walks
/// that container again, is so on the projection.
pub(crate) proof fn kill_container_finish_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Walk),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& u.cpu_array[cpu_id as int].owning_container == container_ptr
            &&& u.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& u.container_map.dom().contains(container_ptr)
            &&& u.container_map[container_ptr].lock_state is WriteLocked
            &&& u.process_map.dom().contains(process_ptr)
            &&& u.process_map[process_ptr].lock_state is WriteLocked
            &&& u.thread_map.dom().contains(thread_ptr)
            &&& u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& u.thread_map[thread_ptr].syscall_progress == kill_container_progress(container_ptr, ContainerKillStage::Walk)
        }),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, cpu_id);
    krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr); kernel_container_projection_at(krnl, container_ptr);
}

/// Clearing the progress and unlocking the thread, the process, the cpu's container `container_ptr`, and the cpu is the
/// finish step of the container kill.
pub(crate) proof fn kill_container_finish_step_from_u(
    pre: KernelU, cleared: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_array[cpu_id as int].lock_state is WriteLocked,
        pre.cpu_array[cpu_id as int].owning_container == container_ptr,
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.container_map.dom().contains(container_ptr),
        pre.container_map[container_ptr].lock_state is WriteLocked,
        pre.process_map.dom().contains(process_ptr),
        pre.process_map[process_ptr].lock_state is WriteLocked,
        pre.thread_map.dom().contains(thread_ptr),
        pre.thread_map[thread_ptr].lock_state is WriteLocked,
        pre.thread_map[thread_ptr].syscall_progress == kill_container_progress(container_ptr, ContainerKillStage::Walk),
        cleared == (KernelU { thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: None, ..pre.thread_map[thread_ptr] }), ..pre }),
        post == (KernelU {
            cpu_array: cleared.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cleared.cpu_array[cpu_id as int].state), ..cleared.cpu_array[cpu_id as int] }),
            container_map: cleared.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..cleared.container_map[container_ptr] }),
            process_map: cleared.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..cleared.process_map[process_ptr] }),
            thread_map: cleared.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..cleared.thread_map[thread_ptr] }),
            ..cleared
        }),
    ensures
        kill_container_finish_step_pre(pre, cpu_id),
        kill_container_finish_step(pre, post, cpu_id),
{
    reveal(kill_container_finish_step_pre); reveal(kill_container_finish_step);
    assert(post.thread_map =~= pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map[thread_ptr] }));
}

/// The finish step pushed after the partial trace of the container kill that starts at `start` completes its trace.
pub(crate) proof fn kill_container_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize,
)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, KillTraceCtx::Container { child_index }),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        kill_container_finish_step_pre(finish_pre, cpu_id),
        kill_container_finish_step(finish_pre, post, cpu_id),
    ensures kill_container_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, child_index, true),
{
    reveal(kill_partial_trace); reveal(kill_container_partial_trace); reveal(kill_container_syscall_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: finish_pre, new_u: post }));
}

/// A rejected container kill records no step.
pub(crate) proof fn kill_container_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, child_index: usize)
    requires trace.len() == 0,
    ensures kill_container_syscall_trace(trace, pre, pre, cpu_id, child_index, false),
{ reveal(kill_container_syscall_trace); }
} // verus!

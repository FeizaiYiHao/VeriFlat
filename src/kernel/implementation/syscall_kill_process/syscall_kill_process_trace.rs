use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
use crate::*;
use super::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_container::syscall_kill_container_spec::kill_container_partial_trace;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk_spec::{KillScope, kill_scope_progress};
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::hide_user_l4_entries_eof::hide_user_l4_entry_eof_transition_framing;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::hide_user_l4_entries_eof::hide_user_l4_entry_eof_transition_framing;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::hide_user_l4_entries_trace::hide_user_l4_entries_hide_step_from_k;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::hide_user_l4_entries_trace::hide_user_l4_entries_hide_step_from_k;

verus! {
/// The killer on `cpu_id` write-holding its cpu, its process `prc_ptr`, itself `thrd_ptr`, the marked `target`, and
/// the victim container of `scope`, if any, with its progress recording the kill of `target` at `stage` in `scope`,
/// satisfies the kill's step precondition on `krnl`. The target lies in its cpu's container in a subtree kill, and in
/// the victim container, below its cpu's container, in a container kill; so it does on the projection.
pub(crate) proof fn kill_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, scope: KillScope,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> krnl.ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && krnl.ctn_mp.spec_index(container).view().uppertree_seq.view().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
    ensures
        kill_process_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kill_killer(kernel_k_to_kernel_u(*krnl), cpu_id) == thrd_ptr,
        kill_target(kernel_k_to_kernel_u(*krnl), cpu_id) == target,
        kill_stage(kernel_k_to_kernel_u(*krnl), cpu_id) == stage,
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, stage),
        scope is Subtree ==> kernel_k_to_kernel_u(*krnl).process_map[target].owning_container == kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container,
        scope matches KillScope::Container { container }
            ==> kernel_k_to_kernel_u(*krnl).process_map[target].owning_container == container
                && kernel_k_to_kernel_u(*krnl).container_map[container].uppertree_seq.contains(kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_write_held_context_projection(krnl, lctx, cpu_id, target, thrd_ptr, None);
    kernel_cpu_projection_at(krnl, cpu_id); kernel_process_projection_at(krnl, target);
    if let KillScope::Container { container } = scope { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container); kernel_container_projection_at(krnl, container); }
    reveal(kill_process_step_pre);
}

/// A cpu that is not running or is marked by a killer makes the kill return CpuIdle.
pub(crate) proof fn kill_idle_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        !(krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !krnl.cpu_arr.spec_index(cpu_id).view().being_killed()),
    ensures kill_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index) is CpuIdle,
{ kernel_cpu_projection_at(krnl, cpu_id); }

/// On a running unmarked cpu that runs `thrd_ptr` of `prc_ptr`, a marked process or thread, a child index past the
/// children, and a marked child each reject the kill.
pub(crate) proof fn kill_result_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
    ensures
        ({
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let children = process.view().children.view();
            let result = kill_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index);
            &&& process.being_killed() ==> result is ErrorProcessKilled
            &&& !process.being_killed() && krnl.thrd_mp.spec_index(thrd_ptr).being_killed() ==> result is ErrorThreadKilled
            &&& !process.being_killed() && !krnl.thrd_mp.spec_index(thrd_ptr).being_killed() && child_index >= children.len() ==> result is ErrorInvalidChild
            &&& !process.being_killed() && !krnl.thrd_mp.spec_index(thrd_ptr).being_killed() && child_index < children.len()
                && krnl.prc_mp.dom().contains(children[child_index as int]) && krnl.prc_mp.spec_index(children[child_index as int]).being_killed() ==> result is ErrorProcessKilled
        }),
{
    let children = krnl.prc_mp.spec_index(prc_ptr).view().children.view();
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_process_projection_at(krnl, prc_ptr);
    if child_index < children.len() && krnl.prc_mp.dom().contains(children[child_index as int]) { kernel_process_projection_at(krnl, children[child_index as int]); }
}

/// The unlocked running unmarked cpu, process, and thread with no syscall in progress, whose live child at `child_index`
/// is `child_ptr`, are so on the projection, where the kill succeeds.
pub(crate) proof fn kill_enter_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, child_ptr: RwLockProcessPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            &&& !cpu.locked()
            &&& cpu.view().view().state is Running
            &&& !cpu.being_killed()
            &&& cpu.view().view().current_process == Some(prc_ptr)
            &&& cpu.view().view().current_thread == Some(thrd_ptr)
            &&& krnl.prc_mp.dom().contains(prc_ptr)
            &&& !process.locked()
            &&& !process.being_killed()
            &&& krnl.thrd_mp.dom().contains(thrd_ptr)
            &&& !thread.locked()
            &&& !thread.being_killed()
            &&& thread.view().syscall_progress.view() is None
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == prc_ptr
            &&& child_index < process.view().children.view().len()
            &&& process.view().children.view()[child_index as int] == child_ptr
            &&& krnl.prc_mp.dom().contains(child_ptr)
            &&& !krnl.prc_mp.spec_index(child_ptr).being_killed()
            &&& !krnl.prc_mp.spec_index(child_ptr).locked()
        }),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let cpu = u.cpu_array[cpu_id as int];
            let process = u.process_map[prc_ptr];
            let thread = u.thread_map[thrd_ptr];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& !cpu.killed
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& u.process_map.dom().contains(prc_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& u.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == prc_ptr
            &&& child_index < process.children.len()
            &&& process.children[child_index as int] == child_ptr
            &&& u.process_map.dom().contains(child_ptr)
            &&& !u.process_map[child_ptr].killed
            &&& u.process_map[child_ptr].lock_state is Unlocked
        }),
        kill_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index) is Success,
{ kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_thread_projection_at(krnl, thrd_ptr); kernel_process_projection_at(krnl, prc_ptr); kernel_process_projection_at(krnl, child_ptr); }

/// The first child `child_ptr` of the target on `krnl` is its first child on the projection.
pub(crate) proof fn kill_mark_child_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.dom().contains(child_ptr),
        0 < krnl.prc_mp.spec_index(target).view().children.view().len(),
        krnl.prc_mp.spec_index(target).view().children.view()[0] == child_ptr,
        !krnl.prc_mp.spec_index(child_ptr).locked(),
        !krnl.prc_mp.spec_index(child_ptr).being_killed(),
    ensures
        0 < kernel_k_to_kernel_u(*krnl).process_map[target].children.len(),
        kernel_k_to_kernel_u(*krnl).process_map[target].children[0] == child_ptr,
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(child_ptr),
        kernel_k_to_kernel_u(*krnl).process_map[child_ptr].lock_state is Unlocked,
        !kernel_k_to_kernel_u(*krnl).process_map[child_ptr].killed,
{ kernel_process_projection_at(krnl, target); kernel_process_projection_at(krnl, child_ptr); }

/// The unlocked first thread `victim_ptr` of the childless target on `krnl`, waiting for a reply, is so on the projection.
pub(crate) proof fn kill_dangling_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.thrd_mp.dom().contains(victim_ptr),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        0 < krnl.prc_mp.spec_index(target).view().owned_threads.view().len(),
        krnl.prc_mp.spec_index(target).view().owned_threads.view()[0] == victim_ptr,
        krnl.thrd_mp.spec_index(victim_ptr).view().state is WAITING_REPLY,
        !krnl.thrd_mp.spec_index(victim_ptr).locked(),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.process_map[target].children.len() == 0
            &&& 0 < u.process_map[target].owned_threads.len()
            &&& u.process_map[target].owned_threads[0] == victim_ptr
            &&& u.thread_map.dom().contains(victim_ptr)
            &&& u.thread_map[victim_ptr].state is WAITING_REPLY
            &&& u.thread_map[victim_ptr].lock_state is Unlocked
        }),
{ kernel_process_projection_at(krnl, target); kernel_thread_projection_at(krnl, victim_ptr); }

/// The first thread `victim_ptr` of the childless target on `krnl`, not waiting for a reply, is so on the projection.
pub(crate) proof fn kill_mark_thread_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.thrd_mp.dom().contains(victim_ptr),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        0 < krnl.prc_mp.spec_index(target).view().owned_threads.view().len(),
        krnl.prc_mp.spec_index(target).view().owned_threads.view()[0] == victim_ptr,
        !krnl.thrd_mp.spec_index(victim_ptr).view().state.is_reply_waiting(),
        !krnl.thrd_mp.spec_index(victim_ptr).locked(),
        krnl.thrd_mp.spec_index(victim_ptr).view().syscall_progress.view() is None,
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.process_map[target].children.len() == 0
            &&& 0 < u.process_map[target].owned_threads.len()
            &&& u.process_map[target].owned_threads[0] == victim_ptr
            &&& u.thread_map.dom().contains(victim_ptr)
            &&& !u.thread_map[victim_ptr].state.is_reply_waiting()
            &&& u.thread_map[victim_ptr].lock_state is Unlocked
            &&& u.thread_map[victim_ptr].syscall_progress is None
        }),
{ kernel_process_projection_at(krnl, target); kernel_thread_projection_at(krnl, victim_ptr); }

/// The marked victim `victim_ptr` of the kill's target `target` that the killer on `cpu_id` write-holds with its cpu and
/// the target, recorded by the kill, in state `state`, owned by `ctn_ptr`, and waiting on `endpoint`, is the kill's
/// write-locked marked victim of its target on the projection.
pub(crate) proof fn kill_victim_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, state: ThreadState, ctn_ptr: RwLockContainerPtr,
    endpoint: Option<RwLockEndpointPtr>,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), victim_ptr, TypedLockMode::Write),
        krnl.thrd_mp.dom().contains(victim_ptr),
        krnl.thrd_mp.spec_index(victim_ptr).being_killed(),
        krnl.thrd_mp.spec_index(victim_ptr).view().state == state,
        krnl.thrd_mp.spec_index(victim_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(victim_ptr).view().blocking_endpoint_ptr == endpoint,
        kill_stage(kernel_k_to_kernel_u(*krnl), cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        kill_target(kernel_k_to_kernel_u(*krnl), cpu_id) == target,
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().owned_threads.view().contains(victim_ptr),
        state is RUNNING ==> index_valid(NUM_CPUS, state->RUNNING_cpu_id),
        state is RUNNING ==> !krnl.cpu_arr.spec_index(state->RUNNING_cpu_id).view().locked() && !(krnl.cpu_op.view().view()[state->RUNNING_cpu_id as int] is InStep),
        state.is_endpoint_waiting() && endpoint is Some ==> krnl.ep_mp.dom().contains(endpoint->Some_0) && !krnl.ep_mp.spec_index(endpoint->Some_0).locked(),
    ensures
        kill_process_victim_marked(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).thread_map[victim_ptr].state == state,
        kernel_k_to_kernel_u(*krnl).thread_map[victim_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[victim_ptr].blocking_endpoint_ptr == endpoint,
        state is RUNNING ==> kernel_k_to_kernel_u(*krnl).cpu_array[state->RUNNING_cpu_id as int].lock_state is Unlocked,
        state is RUNNING ==> !(kernel_k_to_kernel_u(*krnl).cpu_array[state->RUNNING_cpu_id as int].op is InStep),
        state.is_endpoint_waiting() && endpoint is Some ==> kernel_k_to_kernel_u(*krnl).endpoint_map[endpoint->Some_0].lock_state is Unlocked,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, target, victim_ptr, None); kernel_thread_projection_at(krnl, victim_ptr); kernel_process_projection_at(krnl, target);
    if state is RUNNING { kernel_cpu_projection_at(krnl, state->RUNNING_cpu_id); }
    if state.is_endpoint_waiting() && endpoint is Some { kernel_endpoint_projection_at(krnl, endpoint->Some_0); }
}

/// The killer's write-held cpu, process, and thread, with its progress walking its own process, are so on the
/// projection.
pub(crate) proof fn kill_finish_pre_from_k(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_progress(prc_ptr, KillStage::Walk),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& u.cpu_array[cpu_id as int].current_process == Some(prc_ptr)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& u.process_map.dom().contains(prc_ptr)
            &&& u.process_map[prc_ptr].lock_state is WriteLocked
            &&& u.thread_map.dom().contains(thrd_ptr)
            &&& u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& u.thread_map[thrd_ptr].syscall_progress == kill_progress(prc_ptr, KillStage::Walk)
        }),
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_cpu_projection_at(krnl, cpu_id); }

/// The empty live target on `krnl`, whose page table is unlocked, is so on the projection.
pub(crate) proof fn kill_lock_table_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(target).view().pagetable),
        !krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(target).view().pagetable).locked(),
    ensures
        ({
            let process = kernel_k_to_kernel_u(*krnl).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& !process.zombie
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is Unlocked
        }),
{ kernel_process_projection_at(krnl, target); kernel_pagetable_mappings_projection_at(krnl, target); }

/// The empty zombie target on `krnl` is so on the projection.
pub(crate) proof fn kill_zombie_retire_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().zombie,
    ensures
        ({
            let process = kernel_k_to_kernel_u(*krnl).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& process.zombie
        }),
{ kernel_process_projection_at(krnl, target); }

/// The empty zombie target, a child of `parent_ptr`, on `krnl` is so on the projection.
pub(crate) proof fn kill_retire_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
    ensures
        ({
            let process = kernel_k_to_kernel_u(*krnl).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& process.zombie
            &&& process.parent == Some(parent_ptr)
        }),
{ kernel_process_projection_at(krnl, target); }

/// The live target on `krnl`, whose container's PCID allocator is free, is live on the projection with that
/// allocator free.
pub(crate) proof fn kill_zombify_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.ctn_mp.dom().contains(krnl.prc_mp.spec_index(target).view_rodata().view().owning_container),
        krnl.pcid_allc_mp.spec_index(krnl.ctn_mp.spec_index(krnl.prc_mp.spec_index(target).view_rodata().view().owning_container).view_rodata().view().pcid_allocator).locking_thread() is None,
    ensures
        !kernel_k_to_kernel_u(*krnl).process_map[target].zombie,
        kernel_k_to_kernel_u(*krnl).container_map[kernel_k_to_kernel_u(*krnl).process_map[target].owning_container].pcid_allocator_lock is Unlocked,
{ kernel_process_projection_at(krnl, target); kernel_container_projection_at(krnl, krnl.prc_mp.spec_index(target).view_rodata().view().owning_container); }

/// The live target's page table `pagetable`, write-held by the killer `thrd_ptr` on `cpu_id` that reclaims the target at
/// `stage`, is write-locked on the projection, which shows the target's PCID and, when the killer write-holds the target's
/// IOMMU table `iommu_table`, that table write-locked.
pub(crate) proof fn kill_reclaim_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(target).view().iommu_table == iommu_table,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        kill_target(kernel_k_to_kernel_u(*krnl), cpu_id) == target,
        kill_stage(kernel_k_to_kernel_u(*krnl), cpu_id) == stage,
    ensures
        kill_process_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, stage),
        (kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table is Some) == (iommu_table is Some),
        kernel_k_to_kernel_u(*krnl).process_map[target].pcid == krnl.prc_mp.spec_index(target).view_rodata().view().pcid,
        iommu_table matches Some(t) && typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write)
            ==> kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table->Some_0.lock_state is WriteLocked,
        krnl.pt_mp.dom().contains(pagetable) && krnl.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty()
            ==> kernel_k_to_kernel_u(*krnl).process_map[target].pagetable->Some_0.pci_functions == Map::<PciBdf, nat>::empty(),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, target, thrd_ptr, None); kernel_process_projection_at(krnl, target);
    if let Some(t) = iommu_table {
        if typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write) {
            krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t); kernel_iommu_table_mappings_projection_at(krnl, target);
        }
    }
}

/// With no present user 4K leaf at or above the kernel L4 end of the live target's page table on `krnl`, and no 2M or 1G
/// mapping or window lock in it, the target's projected page table has no user 4K mapping, 2M or 1G mapping, or window lock.
pub(crate) proof fn kill_table_unmapped_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(target).view().pagetable),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(target).view().pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i
                && krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(target).view().pagetable).view().higher.kernel_l4_end <= l4i
                && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(target).view().pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(target).view().pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(target).view().pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(target).view().pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(target).view().pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
    ensures
        kernel_k_to_kernel_u(*krnl).process_map[target].pagetable is Some,
        ({
            let pagetable = kernel_k_to_kernel_u(*krnl).process_map[target].pagetable->Some_0;
            &&& process_user_4k_unmapped(kernel_k_to_kernel_u(*krnl), pagetable)
            &&& pagetable.mapping_2m.dom() == Set::<VAddr>::empty()
            &&& pagetable.mapping_1g.dom() == Set::<VAddr>::empty()
            &&& pagetable.pagetable_window_locks.dom() == Set::<WindowVa>::empty()
        }),
{
    kernel_pagetable_user_4k_unmapped_projection_at(krnl, target); kernel_process_projection_at(krnl, target);
    let pagetable = kernel_k_to_kernel_u(*krnl).process_map[target].pagetable->Some_0;
    assert(pagetable.mapping_2m.dom() =~= Set::<VAddr>::empty()); assert(pagetable.mapping_1g.dom() =~= Set::<VAddr>::empty());
}

/// With no 4K leaf in the live target's IOMMU table on `krnl`, its projected IOMMU table has no 4K mapping.
pub(crate) proof fn kill_iommu_unmapped_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view().iommu_table is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger krnl.it_mp.spec_index(krnl.prc_mp.spec_index(target).view().iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !krnl.it_mp.spec_index(krnl.prc_mp.spec_index(target).view().iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    ensures
        kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table is Some,
        process_iommu_4k_unmapped(kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table->Some_0),
{ kernel_iommu_table_4k_unmapped_projection_at(krnl, target); }

/// The target, owned by `ctn_ptr` on `krnl`, is owned by it on the projection.
pub(crate) proof fn kill_refund_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
    ensures kernel_k_to_kernel_u(*krnl).process_map[target].owning_container == ctn_ptr,
{ kernel_process_projection_at(krnl, target); }

/// Write-locking the cpu, the process, and the thread, marking and write-locking the live child at `child_index`, and
/// recording the walk of that child is the enter step on `pre`/`post`.
pub(crate) proof fn kill_enter_step_from_u(
    pre: KernelU, locked: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    child_ptr: RwLockProcessPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        prc_ptr != child_ptr,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let process = pre.process_map[prc_ptr];
            let thread = pre.thread_map[thrd_ptr];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& !cpu.killed
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& pre.process_map.dom().contains(prc_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == prc_ptr
            &&& child_index < process.children.len()
            &&& process.children[child_index as int] == child_ptr
            &&& pre.process_map.dom().contains(child_ptr)
            &&& !pre.process_map[child_ptr].killed
            &&& pre.process_map[child_ptr].lock_state is Unlocked
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..pre.process_map[prc_ptr] }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..pre.thread_map[thrd_ptr] }),
            ..pre
        }),
        marked == (KernelU { process_map: locked.process_map.insert(child_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, killed: true, ..locked.process_map[child_ptr] }), ..locked }),
        post == (KernelU { thread_map: marked.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_progress(child_ptr, KillStage::Walk), ..marked.thread_map[thrd_ptr] }), ..marked }),
    ensures
        kill_process_enter_step_pre(pre, cpu_id, child_index),
        kill_process_enter_step(pre, post, cpu_id, child_index),
{
    reveal(kill_process_enter_step_pre); reveal(kill_process_enter_step);
    assert(post.thread_map =~= pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: kill_progress(child_ptr, KillStage::Walk), ..pre.thread_map[thrd_ptr] }));
}

/// Marking and write-locking the first child `child_ptr` of the target and recording its walk is a middle step.
pub(crate) proof fn kill_mark_child_step_from_u(pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, child_ptr: RwLockProcessPtr, scope: KillScope)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        0 < pre.process_map[target].children.len(),
        pre.process_map[target].children[0] == child_ptr,
        pre.process_map.dom().contains(child_ptr),
        pre.process_map[child_ptr].lock_state is Unlocked,
        !pre.process_map[child_ptr].killed,
        marked == (KernelU { process_map: pre.process_map.insert(child_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, killed: true, ..pre.process_map[child_ptr] }), ..pre }),
        post == (KernelU { thread_map: marked.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, child_ptr, KillStage::Walk), ..marked.thread_map[thrd_ptr] }), ..marked }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_mark_child_step); }

/// The first thread `victim_ptr` of the childless target, waiting for a reply and unlocked, leaving the target as a dangling thread
/// is a middle step.
pub(crate) proof fn kill_dangling_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        0 < pre.process_map[target].owned_threads.len(),
        pre.process_map[target].owned_threads[0] == victim_ptr,
        pre.thread_map.dom().contains(victim_ptr),
        pre.thread_map[victim_ptr].state is WAITING_REPLY,
        pre.thread_map[victim_ptr].lock_state is Unlocked,
        ({
            let process = pre.process_map[target];
            let victim = pre.thread_map[victim_ptr];
            post == (KernelU {
                process_map: pre.process_map.insert(target, kill_process_absorb_thread(process, victim_ptr, victim)),
                thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::DANGLING, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..victim }),
                ..pre
            })
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_dangling_step); }

/// Marking and write-locking the first thread `victim_ptr` of the childless target, not waiting for a reply, and
/// recording it is a middle step.
pub(crate) proof fn kill_mark_thread_step_from_u(
    pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, scope: KillScope,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        0 < pre.process_map[target].owned_threads.len(),
        pre.process_map[target].owned_threads[0] == victim_ptr,
        pre.thread_map.dom().contains(victim_ptr),
        !pre.thread_map[victim_ptr].state.is_reply_waiting(),
        pre.thread_map[victim_ptr].lock_state is Unlocked,
        pre.thread_map[victim_ptr].syscall_progress is None,
        victim_ptr != thrd_ptr,
        marked == (KernelU { thread_map: pre.thread_map.insert(victim_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, killed: true, ..pre.thread_map[victim_ptr] }), ..pre }),
        post == (KernelU {
            thread_map: marked.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Thread { thread: victim_ptr }), ..marked.thread_map[thrd_ptr] }),
            ..marked
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_mark_thread_step); }

/// The recorded victim leaving shard `shard` of its container's scheduler and becoming killed is a middle step.
pub(crate) proof fn kill_dequeue_scheduled_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, shard: CpuId)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_marked(pre, cpu_id),
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state == (ThreadState::SCHEDULED { cpu_id: shard }),
        pre.thread_map[victim_ptr].owning_container == ctn_ptr,
        pre.container_map.dom().contains(ctn_ptr),
        ({
            let container = pre.container_map[ctn_ptr];
            post == (KernelU {
                container_map: pre.container_map.insert(ctn_ptr, ContainerU {
                    scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(victim_ptr)), ..container
                }),
                thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..pre.thread_map[victim_ptr] }),
                ..pre
            })
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_dequeue_scheduled_step); }

/// The recorded victim leaving the queue of the endpoint `ep_ptr` it waits on and becoming killed is a middle step.
pub(crate) proof fn kill_dequeue_endpoint_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_marked(pre, cpu_id),
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state.is_endpoint_waiting(),
        pre.thread_map[victim_ptr].blocking_endpoint_ptr == Some(ep_ptr),
        pre.endpoint_map.dom().contains(ep_ptr),
        pre.endpoint_map[ep_ptr].lock_state is Unlocked,
        post == (KernelU {
            endpoint_map: pre.endpoint_map.insert(ep_ptr, EndpointU { queue: pre.endpoint_map[ep_ptr].queue.remove_value(victim_ptr), ..pre.endpoint_map[ep_ptr] }),
            thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..pre.thread_map[victim_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_dequeue_endpoint_step); }

/// Forcing the remote cpu `remote` that runs the recorded victim from running to idle is a middle step.
pub(crate) proof fn kill_cpu_to_idle_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim_ptr: RwLockThreadPtr, remote: CpuId)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_marked(pre, cpu_id),
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state == (ThreadState::RUNNING { cpu_id: remote }),
        index_valid(NUM_CPUS, remote),
        remote != cpu_id,
        pre.cpu_array[remote as int].lock_state is Unlocked,
        !(pre.cpu_array[remote as int].op is InStep),
        post == (KernelU {
            cpu_array: pre.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..pre.cpu_array[remote as int] }),
            thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, ..pre.thread_map[victim_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_cpu_to_idle_step); }

/// The killed recorded victim leaving the target, which absorbs its quota, and the kill walking the target again is a
/// middle step.
pub(crate) proof fn kill_unlink_step_from_u(
    pre: KernelU, left: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, scope: KillScope,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_marked(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state is KILLED,
        thrd_ptr != victim_ptr,
        ({
            let process = pre.process_map[target];
            let victim = pre.thread_map[victim_ptr];
            left == (KernelU {
                process_map: pre.process_map.insert(target, kill_process_absorb_thread(process, victim_ptr, victim)),
                thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..victim }),
                ..pre
            })
        }),
        post == (KernelU { thread_map: left.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Walk), ..left.thread_map[thrd_ptr] }), ..left }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_unlink_step); }

/// Clearing the progress of the killer, which walks its own process again, and unlocking it, its process, and its cpu is
/// the finish step on `pre`/`post`.
pub(crate) proof fn kill_finish_step_from_u(pre: KernelU, cleared: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = pre.cpu_array[cpu_id as int];
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.current_thread == Some(thrd_ptr)
        }),
        pre.process_map.dom().contains(prc_ptr),
        pre.process_map[prc_ptr].lock_state is WriteLocked,
        pre.thread_map.dom().contains(thrd_ptr),
        pre.thread_map[thrd_ptr].lock_state is WriteLocked,
        pre.thread_map[thrd_ptr].syscall_progress == kill_progress(prc_ptr, KillStage::Walk),
        cleared == (KernelU { thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: None, ..pre.thread_map[thrd_ptr] }), ..pre }),
        post == (KernelU {
            cpu_array: cleared.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cleared.cpu_array[cpu_id as int].state), ..cleared.cpu_array[cpu_id as int] }),
            process_map: cleared.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..cleared.process_map[prc_ptr] }),
            thread_map: cleared.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..cleared.thread_map[thrd_ptr] }),
            ..cleared
        }),
    ensures
        kill_process_finish_step_pre(pre, cpu_id),
        kill_process_finish_step(pre, post, cpu_id),
{
    reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step);
    assert(post.thread_map =~= pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map[thrd_ptr] }));
}

/// Write-locking the page table `pagetable` of the empty live target from `pre` to `post`, recording that nothing is flushed
/// yet, and then listing cpus stale for the table (`stale`), is a middle step.
pub(crate) proof fn kill_lock_table_step_from_k(
    pre: &KernelK, post: &KernelK, stale: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, pagetable: RwLockPageTableRoot,
    scope: KillScope,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        typed_lock_maps_aligned(post, lctx),
        lctx.cpu_id() == cpu_id,
        kill_process_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kill_killer(kernel_k_to_kernel_u(*pre), cpu_id) == thrd_ptr,
        kernel_k_to_kernel_u(*pre).thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(kernel_k_to_kernel_u(*pre), cpu_id)),
        kill_target(kernel_k_to_kernel_u(*pre), cpu_id) == target,
        kill_stage(kernel_k_to_kernel_u(*pre), cpu_id) is Walk,
        ({
            let process = kernel_k_to_kernel_u(*pre).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& !process.zombie
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is Unlocked
        }),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().pagetable == pagetable,
        *post == (KernelK { pt_mp: post.pt_mp, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> {
            &&& post.pt_mp.spec_index(p).view().higher == pre.pt_mp.spec_index(p).view().higher
            &&& p != pagetable ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
        },
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, KillStage::Reclaim { flushed: false }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        stale.cpu_tlb == post.cpu_tlb,
        kernel_k_to_kernel_u(*stale) == (KernelU { cpu_tlb: stale.cpu_tlb.view(), ..kernel_k_to_kernel_u(*post) }),
    ensures kill_process_middle_step(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*stale) }, cpu_id),
{
    kernel_pagetable_write_locked_and_progress_changed_implies_u_step(pre, post, lctx, cpu_id, target, pagetable, thrd_ptr); kernel_u_domains_projection(post);
    reveal(kill_process_lock_table_step);
}

/// Dropping every 4K, 2M and 1G mapping and every window lock under the root entry `l4i` from the target's write-locked page
/// table before the flush, and nothing else, is a middle step.
pub(crate) proof fn kill_table_hidden_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, target: RwLockProcessPtr, l4i: L4Index)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, KillStage::Reclaim { flushed: false }),
        ({
            let table = pre.process_map[target].pagetable->Some_0;
            post == (KernelU {
                process_map: pre.process_map.insert(target, ProcessU {
                    pagetable: if pre.process_map[target].pagetable is Some {
                        Some(PageTableU {
                            mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
                            ..table
                        })
                    } else {
                        None
                    },
                    ..pre.process_map[target]
                }),
                ..pre
            })
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    reveal(kill_process_table_hidden_step); reveal(process_table_hidden_step);
    let o = pre.process_map[target].pagetable->Some_0;
    let n = post.process_map[target].pagetable->Some_0;
    assert(n.mapping_4k =~= o.mapping_4k.restrict(n.mapping_4k.dom()));
    assert(n.mapping_2m =~= o.mapping_2m.restrict(n.mapping_2m.dom()));
    assert(n.mapping_1g =~= o.mapping_1g.restrict(n.mapping_1g.dom()));
    assert(n.pagetable_window_locks =~= o.pagetable_window_locks.restrict(n.pagetable_window_locks.dom()));
}

/// Recording the flush of the target's PCID is a middle step.
pub(crate) proof fn kill_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, scope: KillScope)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_process_flush_step_pre(pre, cpu_id),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Reclaim { flushed: true }), ..pre.thread_map[thrd_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_flushed_step); }

/// Releasing the PCI functions of the page table `pagetable` of the live target, reclaimed and flushed, from `pre` to `post`
/// is a visible middle step once its user mappings and window locks are gone. Up to `mid`, the root-table lock and, when the target has the IOMMU table `iommu_table`, that
/// table's write lock are taken, and each function of the array is detached while the table drops its DID; from `mid`, each
/// function of the array becomes unowned and the array empties. A target holding no function only write-locks its IOMMU table.
pub(crate) proof fn kill_unown_step_from_k(
    pre: &KernelK, mid: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>,
)
    requires
        pre.inv(),
        kill_process_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kill_target(kernel_k_to_kernel_u(*pre), cpu_id) == target,
        kill_process_reclaim_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, KillStage::Reclaim { flushed: true }),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().pagetable == pagetable,
        pre.prc_mp.spec_index(target).view().iommu_table == iommu_table,
        iommu_table matches Some(t) ==> pre.it_mp.spec_index(t).locking_thread() is None,
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() != Set::<PciBdf>::empty() || iommu_table is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        typed_lock_maps_aligned(post, lctx),
        lctx.cpu_id() == cpu_id,
        iommu_table matches Some(t) ==> typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write),
        *mid == (KernelK { irt: mid.irt, iommu_tlb: mid.iommu_tlb, it_mp: mid.it_mp, ..*pre }),
        mid.irt.view().owners() == pre.irt.view().owners(),
        iommu_table is None ==> mid.irt.view().iommu_roots() == pre.irt.view().iommu_roots() && mid.it_mp == pre.it_mp && mid.iommu_tlb == pre.iommu_tlb,
        iommu_table matches Some(t) ==> {
            &&& forall|b: usize, d: usize, f: usize| #![trigger mid.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> mid.irt.view().spec_index_iommu_root(b, d, f)
                == if pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains((b, d, f)) { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
            &&& mid.it_mp.unchanged_except(&pre.it_mp, t)
            &&& mid.it_mp.spec_index(t).view() == (IommuTable { did: None, ..pre.it_mp.spec_index(t).view() })
            &&& pre.it_mp.spec_index(t).view().did matches Some(d) ==> mid.iommu_tlb.view() == pre.iommu_tlb.view().insert(d, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            &&& pre.it_mp.spec_index(t).view().did is None ==> mid.iommu_tlb.view() == pre.iommu_tlb.view()
        },
        *post == (KernelK { irt: post.irt, pt_mp: post.pt_mp, ..*mid }),
        post.irt.view().iommu_roots() == mid.irt.view().iommu_roots(),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty() ==> mid.irt == pre.irt && post.irt == mid.irt,
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() != Set::<PciBdf>::empty()
            ==> post.irt.view().owners() == pci_owners_released(mid.irt.view().owners(), mid.pt_mp.spec_index(pagetable).view().higher.pci.view().dom()),
        post.pt_mp.unchanged_except(&mid.pt_mp, pagetable),
        post.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(pagetable).view().higher.pci, ..mid.pt_mp.spec_index(pagetable).view().higher }),
        post.pt_mp.spec_index(pagetable).view().higher.pci.view() == Map::<PciBdf, Set<PciBarMapping>>::empty(),
    ensures
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
        kill_process_middle_step(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }, cpu_id),
{
    kill_table_unmapped_pre_from_k(pre, target);
    kernel_pci_functions_released_implies_u_step(pre, post, lctx, cpu_id, target, pagetable, iommu_table, mid.irt.view()); reveal(kill_process_unown_functions_step);
}

/// Removing or hiding the 4K leaf `iova` of the target's write-locked IOMMU table after the flush is a middle step; the
/// kill's step precondition, read on `post`, ignores that leaf.
pub(crate) proof fn kill_iommu_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, target: RwLockProcessPtr, iova: VAddr)
    requires
        kill_process_step_pre(post, cpu_id),
        kill_target(post, cpu_id) == target,
        kill_process_reclaim_step_pre(post, cpu_id, KillStage::Reclaim { flushed: true }),
        post.process_map[target].iommu_table->Some_0.lock_state is WriteLocked,
        pre.process_map.dom().contains(target),
        pre.process_map[target].iommu_table is Some,
        pre.process_map[target].iommu_table->Some_0.mapping_4k.dom().contains(iova),
        post == (KernelU {
            process_map: pre.process_map.insert(target, ProcessU {
                iommu_table: Some(PageTableU { mapping_4k: pre.process_map[target].iommu_table->Some_0.mapping_4k.remove(iova), ..pre.process_map[target].iommu_table->Some_0 }),
                ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    reveal(kill_process_iommu_leaf_step); reveal(kill_process_step_pre);
    let mapping = pre.process_map[target].iommu_table->Some_0.mapping_4k;
    let kept = post.process_map[target].iommu_table->Some_0.mapping_4k.dom();
    assert(mapping.dom().difference(kept) =~= set![iova]);
    assert(mapping.remove(iova) =~= mapping.restrict(kept));
}

/// Returning the target's whole `size` quota to its container and recording the return is a middle step.
pub(crate) proof fn kill_quota_step_from_u(
    pre: KernelU, returned: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, size: PageSize, scope: KillScope,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, stage),
        pre.process_map[target].iommu_table is Some ==> pre.process_map[target].iommu_table->Some_0.lock_state is WriteLocked,
        kill_process_quota_stage_after(stage) == Some(KillStage::Quota { returned: size }),
        pre.container_map.dom().contains(pre.process_map[target].owning_container),
        pre.process_map[target].pagetable->Some_0.pci_functions == Map::<PciBdf, nat>::empty(),
        pre.process_map[target].iommu_table is Some ==> process_iommu_4k_unmapped(pre.process_map[target].iommu_table->Some_0),
        ({
            let process = pre.process_map[target];
            let container = pre.container_map[process.owning_container];
            returned == (KernelU {
                container_map: pre.container_map.insert(process.owning_container, match size {
                    PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k) as usize, ..container },
                    PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m) as usize, ..container },
                    PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g) as usize, ..container },
                }),
                process_map: pre.process_map.insert(target, match size {
                    PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                    PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                    PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
                }),
                ..pre
            })
        }),
        post == (KernelU {
            thread_map: returned.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Quota { returned: size }), ..returned.thread_map[thrd_ptr] }),
            ..returned
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_quota_step); }

/// Unlocking the target's reclaimed page table and IOMMU table once every quota size is returned is a middle step.
pub(crate) proof fn kill_unlock_table_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, scope: KillScope)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, KillStage::Quota { returned: PageSize::SZ1g }),
        pre.process_map[target].iommu_table is Some ==> pre.process_map[target].iommu_table->Some_0.lock_state is WriteLocked,
        process_user_4k_unmapped(pre, pre.process_map[target].pagetable->Some_0),
        pre.process_map[target].pagetable->Some_0.mapping_2m.dom() == Set::<VAddr>::empty(),
        pre.process_map[target].pagetable->Some_0.mapping_1g.dom() == Set::<VAddr>::empty(),
        pre.process_map[target].pagetable->Some_0.pagetable_window_locks.dom() == Set::<WindowVa>::empty(),
        pre.process_map[target].pagetable->Some_0.pci_functions == Map::<PciBdf, nat>::empty(),
        pre.process_map[target].iommu_table is Some ==> process_iommu_4k_unmapped(pre.process_map[target].iommu_table->Some_0),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Zombie), ..pre.thread_map[thrd_ptr] }),
            process_map: pre.process_map.insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[target].pagetable->Some_0 }),
                iommu_table: match pre.process_map[target].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
                ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_unlock_table_step); }

/// Making the reclaimed target a zombie that releases its PCID to its container, and starting to retire it, is a middle
/// step.
pub(crate) proof fn kill_zombify_step_from_u(pre: KernelU, zombified: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, scope: KillScope)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Zombie,
        !pre.process_map[target].zombie,
        pre.container_map.dom().contains(pre.process_map[target].owning_container),
        pre.container_map[pre.process_map[target].owning_container].pcid_allocator_lock is Unlocked,
        ({
            let process = pre.process_map[target];
            let container = pre.container_map[process.owning_container];
            zombified == (KernelU {
                container_map: pre.container_map.insert(process.owning_container, ContainerU { free_pcids: container.free_pcids.insert(process.pcid), ..container }),
                process_map: pre.process_map.insert(target, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..process }),
                ..pre
            })
        }),
        post == (KernelU {
            thread_map: zombified.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Retire), ..zombified.thread_map[thrd_ptr] }),
            ..zombified
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_zombify_step); }

/// An empty zombie target going straight to retiring is a middle step.
pub(crate) proof fn kill_zombie_retire_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, scope: KillScope)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        pre.process_map[target].zombie,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, target, KillStage::Retire), ..pre.thread_map[thrd_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_zombie_retire_step); }

/// The one step pushed since `before` is the partial trace after entering, which counts no table-phase or retire step.
pub(crate) proof fn kill_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        kill_process_enter_step_pre(pre, cpu_id, child_index),
        kill_process_enter_step(pre, post, cpu_id, child_index),
    ensures
        kill_partial_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, KillTraceCtx::Process { child_index }),
        kill_process_table_count(steps.view().subrange(before.len() as int, steps.view().len() as int), cpu_id) == 0,
        kill_process_retire_count(steps.view().subrange(before.len() as int, steps.view().len() as int), cpu_id) == 0,
{ reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_process_table_count); reveal(kill_process_retire_count); }

/// Retiring the empty zombie target, which raises its container's 4K quota to `quota`, and walking its parent again is a
/// middle step.
pub(crate) proof fn kill_retire_step_from_u(
    pre: KernelU, retired: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, quota: usize, scope: KillScope,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, kill_stage(pre, cpu_id)),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Retire,
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        pre.process_map[target].zombie,
        pre.process_map[target].parent == Some(parent_ptr),
        pre.container_map.dom().contains(pre.process_map[target].owning_container),
        pre.container_map[pre.process_map[target].owning_container].quota_4k < quota,
        ({
            let process = pre.process_map[target];
            let container = pre.container_map[process.owning_container];
            retired == (KernelU {
                container_map: pre.container_map.insert(process.owning_container, ContainerU { owned_processes: container.owned_processes.remove(target), quota_4k: quota, ..container }),
                process_map: Map::new(pre.process_map.dom().remove(target), |p: RwLockProcessPtr| {
                    let q = pre.process_map[p];
                    if process.uppertree_seq.contains(p) {
                        ProcessU { children: if p == parent_ptr { q.children.remove_value(target) } else { q.children }, subtree_set: q.subtree_set.remove(target), ..q }
                    } else { q }
                }),
                ..pre
            })
        }),
        post == (KernelU {
            thread_map: retired.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_scope_progress(scope, parent_ptr, KillStage::Walk), ..retired.thread_map[thrd_ptr] }),
            ..retired
        }),
    ensures
        kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
        kill_process_retire_step(pre, post, cpu_id),
{ reveal(kill_process_retire_step); }

/// A middle step pushed after the partial trace that starts at `start` extends it. It adds at most one table-phase step and
/// none when it starts walking or working on a thread, and adds one retire step when it retires the target.
pub(crate) proof fn kill_trace_push(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId, ctx: KillTraceCtx)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        steps.view() == before.push(KernelStep { old_u: step_pre, new_u: step_post }),
        kill_process_middle_step(KernelStep { old_u: step_pre, new_u: step_post }, cpu_id),
    ensures
        kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
        kill_process_table_count(steps.view().subrange(start, steps.view().len() as int), cpu_id) <= kill_process_table_count(before.subrange(start, before.len() as int), cpu_id) + 1,
        kill_stage(step_pre, cpu_id) is Walk || kill_stage(step_pre, cpu_id) is Thread
            ==> kill_process_table_count(steps.view().subrange(start, steps.view().len() as int), cpu_id) == kill_process_table_count(before.subrange(start, before.len() as int), cpu_id),
        kill_process_retire_count(before.subrange(start, before.len() as int), cpu_id) <= kill_process_retire_count(steps.view().subrange(start, steps.view().len() as int), cpu_id),
        kill_process_retire_step(step_pre, step_post, cpu_id)
            ==> kill_process_retire_count(steps.view().subrange(start, steps.view().len() as int), cpu_id) == kill_process_retire_count(before.subrange(start, before.len() as int), cpu_id) + 1,
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace);
    let step = KernelStep { old_u: step_pre, new_u: step_post };
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(step));
    trace_push_implies_kill_process_table_count_step_added(before.subrange(start, before.len() as int), step, cpu_id);
    trace_push_implies_kill_process_retire_count_step_added(before.subrange(start, before.len() as int), step, cpu_id);
}

/// Steps reclaiming killed threads of `victim_container`, the target's container, recorded after the partial trace that
/// starts at `start` while the killer's cpu, the killer, the lock modes, kill marks, and owning containers of its held
/// processes, and the lock mode and upper tree of the victim container of `scope` keep their projection at `entry`,
/// extend it. They add no retire step, and no table-phase step while the kill walks or works on a thread.
pub(crate) proof fn kill_trace_from_killed_thread_reclaim(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, prc_ptr: RwLockProcessPtr,
    target: RwLockProcessPtr, victim_container: RwLockContainerPtr, stage: KillStage, scope: KillScope,
)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        kernel_steps_prefix_unchanged(before, steps.view()),
        kill_process_step_pre(entry, cpu_id),
        entry.thread_map[kill_killer(entry, cpu_id)].syscall_progress == kill_scope_progress(scope, target, stage),
        entry.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        kill_target(entry, cpu_id) == target,
        scope is Subtree ==> entry.process_map[target].owning_container == entry.cpu_array[cpu_id as int].owning_container,
        scope matches KillScope::Container { container } ==> entry.process_map[target].owning_container == container && entry.container_map[container].uppertree_seq.contains(entry.cpu_array[cpu_id as int].owning_container),
        entry.process_map[target].owning_container == victim_container,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let new_u = steps.view()[j].new_u;
            let thrd_ptr = entry.cpu_array[cpu_id as int].current_thread->Some_0;
            &&& kernel_u_killed_thread_reclaim_step(old_u, new_u, cpu_id)
            &&& forall|t: RwLockThreadPtr| #![trigger old_u.thread_map[t]]
                old_u.thread_map.dom().contains(t) && (!new_u.thread_map.dom().contains(t) || new_u.thread_map[t] != old_u.thread_map[t]) ==> old_u.thread_map[t].owning_container == victim_container
            &&& old_u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].lock_state == entry.process_map[prc_ptr].lock_state
            &&& old_u.process_map.dom().contains(target)
            &&& old_u.process_map[target].lock_state == entry.process_map[target].lock_state
            &&& old_u.process_map[target].killed == entry.process_map[target].killed
            &&& old_u.process_map[target].owning_container == entry.process_map[target].owning_container
            &&& scope matches KillScope::Container { container } ==> old_u.container_map.dom().contains(container) && old_u.container_map[container].lock_state == entry.container_map[container].lock_state
                && old_u.container_map[container].uppertree_seq == entry.container_map[container].uppertree_seq
        },
    ensures
        kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
        stage is Walk || stage is Thread ==> kill_process_table_count(steps.view().subrange(start, steps.view().len() as int), cpu_id) == kill_process_table_count(before.subrange(start, before.len() as int), cpu_id),
        kill_process_retire_count(before.subrange(start, before.len() as int), cpu_id) <= kill_process_retire_count(steps.view().subrange(start, steps.view().len() as int), cpu_id),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace); reveal(kill_process_step_pre); reveal(kernel_steps_prefix_unchanged);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int) + steps.view().subrange(before.len() as int, steps.view().len() as int));
    steps_extended_implies_kill_process_retire_count_monotone(before, steps.view(), start, cpu_id);
    if stage is Walk || stage is Thread { steps_extended_outside_table_phase_implies_kill_process_table_count_unchanged(before, steps.view(), start, cpu_id); }
}

/// A section that flushes cpu `c`'s TLB for `pcid` and changes only cpu state, TLBs, needflush flags, and page-table ghost
/// state that keeps every table's lock mode, mappings, and window locks changes only the TLB projection, and, if it changes
/// it, clears what `c` caches under `pcid` down to what it may cache in the state with `pre`'s page tables.
pub(crate) proof fn kill_tlb_flush_step_from_k(pre: &KernelK, post: &KernelK, c: CpuId, pcid: Pcid, flushed: bool)
    requires
        post.inv(),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        forall|cpu: CpuId| #![trigger post.cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> post.cpu_arr.spec_index(cpu).value.locking_thread() == pre.cpu_arr.spec_index(cpu).value.locking_thread(),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt)] pre.pt_mp.dom().contains(pt) ==> {
            &&& post.pt_mp.spec_index(pt).locking_thread() == pre.pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g()
            &&& post.pt_mp.spec_index(pt).view().higher.pci.mapping_counts() == pre.pt_mp.spec_index(pt).view().higher.pci.mapping_counts()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).lower.pagetable_window_locks
        },
        index_valid(NUM_CPUS, c),
        post.cpu_tlb.view() == if flushed { pre.cpu_tlb.view().insert((c, pcid), post.cpu_tlb.spec_index((c, pcid))) } else { pre.cpu_tlb.view() },
        (KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*post }).inv(),
        flushed ==> cpu_tlb_within_may_cache(KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*post }, c, pcid, post.cpu_tlb.spec_index((c, pcid)), post.cpu_tlb.structure_cache((c, pcid))),
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU { cpu_tlb: post.cpu_tlb.view(), ..kernel_k_to_kernel_u(*pre) }),
        (kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post)) == (pre.cpu_tlb.view() == post.cpu_tlb.view()),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post) ==> kernel_u_cpu_tlb_cleared(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), pcid),
{
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
    kernel_cpu_tlb_updated_implies_u_step(pre, post); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    if pre_u != post_u {
        assert(flushed) by { if !flushed { assert(post_u == pre_u); } };
        reveal(kernel_u_cpu_tlb_cleared);
        let mid = KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*post };
        kernel_cpu_tlb_updated_implies_u_step(pre, &mid); kernel_cpu_tlb_within_may_cache_projection(&mid, c, pcid, post.cpu_tlb.spec_index((c, pcid)), post.cpu_tlb.structure_cache((c, pcid)));
        assert(!pre_u.cpu_tlb.dom().contains((c, pcid)) || pre_u.cpu_tlb[(c, pcid)] != post.cpu_tlb.spec_index((c, pcid))) by {
            if pre_u.cpu_tlb.dom().contains((c, pcid)) && pre_u.cpu_tlb[(c, pcid)] == post.cpu_tlb.spec_index((c, pcid)) { assert_maps_equal!(pre_u.cpu_tlb, post.cpu_tlb.view(), key => {}); }
        };
        assert_sets_equal!(post.cpu_tlb.view().dom().filter(|key: (CpuId, Pcid)| !pre_u.cpu_tlb.dom().contains(key) || pre_u.cpu_tlb[key] != post.cpu_tlb.view()[key]), set![(c, pcid)]);
    }
}

/// A flush step of the target's PCID `pcid`, recorded after the partial trace that starts at `start` once every user 4K
/// leaf of the target is cleared, extends it by at most one step.
pub(crate) proof fn kill_trace_push_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, pcid: Pcid,
)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        steps.view() == record_user_view_change(before, step_pre, step_post),
        step_pre != step_post ==> kernel_u_cpu_tlb_cleared(step_pre, step_post, pcid),
        kill_process_step_pre(step_pre, cpu_id),
        kill_process_flush_step_pre(step_pre, cpu_id),
        step_pre.process_map[kill_target(step_pre, cpu_id)].pcid == pcid,
    ensures
        kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
        before.len() <= steps.view().len() <= before.len() + 1,
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace);
    if step_pre == step_post { assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        assert(steps.view()[before.len() as int] == KernelStep { old_u: step_pre, new_u: step_post });
        assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: step_pre, new_u: step_post }));
    }
}

/// The steps recorded after the partial trace `before`, which starts at `start`, each hiding the user root entry
/// `hidden[k].0` of the target's page table `pagetable` from `hidden[k].1` to `hidden[k].2`, extend it. The killer on
/// `cpu_id` reclaims the target before the flush in `scope` and write-holds its tables; every hide starts from a state whose
/// typed lock maps align with `lctx` and that keeps the objects it holds at `entry`.
pub(crate) proof fn hidden_root_steps_implies_kill_trace(
    steps: Seq<KernelStep>, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, entry: KernelK, lctx: LocalContext, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, scope: KillScope, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
    hidden: Seq<(L4Index, KernelK, KernelK)>, count: int,
)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        0 <= count <= hidden.len(),
        steps.len() == before.len() + hidden.len(),
        forall|j: int| #![trigger steps[j]] 0 <= j < before.len() ==> steps[j] == before[j],
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        entry.prc_mp.dom().contains(target),
        entry.prc_mp.spec_index(target).being_killed(),
        !entry.prc_mp.spec_index(target).view().zombie,
        entry.prc_mp.spec_index(target).view().pagetable == pagetable,
        entry.prc_mp.spec_index(target).view().iommu_table == iommu_table,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, KillStage::Reclaim { flushed: false }),
        scope matches KillScope::Container { container } ==> entry.ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> entry.prc_mp.spec_index(target).view_rodata().view().owning_container == entry.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> entry.prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && entry.ctn_mp.spec_index(container).view().uppertree_seq.view().contains(entry.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        forall|k: int| #![trigger hidden[k]] 0 <= k < hidden.len() ==> {
            &&& steps[before.len() + k] == (KernelStep { old_u: kernel_k_to_kernel_u(hidden[k].1), new_u: kernel_k_to_kernel_u(hidden[k].2) })
            &&& process_pagetable_wf(hidden[k].1.prc_mp, hidden[k].1.pt_mp)
            &&& hide_user_l4_entry_eof_transition_framing(hidden[k].1, hidden[k].2, pagetable, hidden[k].0)
            &&& hidden[k].1.pt_mp.dom().contains(pagetable)
            &&& typed_lock_maps_aligned(&hidden[k].1, &lctx)
            &&& held_cpus_unchanged(entry.cpu_arr, hidden[k].1.cpu_arr, &lctx) && held_containers_unchanged(entry.ctn_mp, hidden[k].1.ctn_mp, &lctx)
            &&& held_processes_unchanged(entry.prc_mp, hidden[k].1.prc_mp, &lctx) && held_threads_unchanged(entry.thrd_mp, hidden[k].1.thrd_mp, &lctx)
        },
    ensures kill_partial_trace(steps.subrange(start, before.len() + count), pre, cpu_id, ctx),
    decreases count,
{
    if count == 0 { assert(steps.subrange(start, before.len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        hidden_root_steps_implies_kill_trace(steps, before, start, pre, cpu_id, ctx, entry, lctx, prc_ptr, thrd_ptr, target, scope, pagetable, iommu_table, hidden, count - 1);
        let h = hidden[count - 1];
        kill_step_pre_from_k(&h.1, &lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: false }, scope);
        kill_reclaim_pre_from_k(&h.1, &lctx, cpu_id, thrd_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table);
        process_pagetable_wf_process_at(h.1.prc_mp, h.1.pt_mp, target);
        hide_user_l4_entries_hide_step_from_k(&h.1, &h.2, pagetable, h.0);
        kill_table_hidden_step_from_u(kernel_k_to_kernel_u(h.1), kernel_k_to_kernel_u(h.2), cpu_id, target, h.0);
        reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace);
        assert(steps.subrange(start, before.len() + count) =~= steps.subrange(start, before.len() + count - 1).push(steps[before.len() + count - 1]));
    }
}

/// Refund steps, recorded after the partial trace that starts at `start` while the killer's cpu and the lock modes and
/// kill marks of the killer's process and the target keep their projection at `entry` and the killer keeps its lock
/// mode and its progress at `stage`, after the flush is recorded or while retiring, in `scope`, each growing the 4K, 2M, or 1G
/// quota of the target's container `ctn_ptr`, the container of the killer's cpu, extend it.
pub(crate) proof fn kill_trace_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, ctn_ptr: RwLockContainerPtr, scope: KillScope,
)
    requires
        stage == (KillStage::Reclaim { flushed: true }) || stage is Retire,
        0 <= start <= before.len() <= steps.view().len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        kill_process_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        entry.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        entry.process_map[target].owning_container == ctn_ptr,
        entry.cpu_array[cpu_id as int].owning_container == ctn_ptr,
        kill_target(entry, cpu_id) == target,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, ctn_ptr) || kernel_u_container_quota_2m_increased(old_u, steps.view()[j].new_u, ctn_ptr)
                || kernel_u_container_quota_1g_increased(old_u, steps.view()[j].new_u, ctn_ptr)
            &&& old_u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(scope, target, stage)
            &&& scope matches KillScope::Container { container } ==> old_u.container_map.dom().contains(container) && old_u.container_map[container].lock_state is WriteLocked
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].lock_state == entry.process_map[prc_ptr].lock_state
            &&& old_u.process_map.dom().contains(target)
            &&& old_u.process_map[target].lock_state == entry.process_map[target].lock_state
            &&& old_u.process_map[target].killed == entry.process_map[target].killed
            &&& old_u.process_map[target].owning_container == entry.process_map[target].owning_container
        },
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace); reveal(kill_process_step_pre);
    assert forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len()
        implies kill_process_refund_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id) by { kill_refund_step_from_u(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id); };
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int) + steps.view().subrange(before.len() as int, steps.view().len() as int));
}

/// One step pushed after the partial trace that starts at `start`, from the projection of `krnl` while the kill holds its
/// cpu, process, thread, and target at `stage`, after the flush is recorded or while retiring, in `scope`, that grows the 4K, 2M,
/// or 1G quota of the target's container or of one of its ancestors, extends it.
pub(crate) proof fn kill_trace_from_scoped_credit(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post_u: KernelU, krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctx: KillTraceCtx,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, scope: KillScope,
)
    requires
        stage == (KillStage::Reclaim { flushed: true }) || stage is Retire,
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*krnl), new_u: post_u }),
        kernel_u_container_quota_4k_increased(kernel_k_to_kernel_u(*krnl), post_u, krnl.prc_mp.spec_index(target).view_rodata().view().owning_container)
            || kernel_u_container_quota_2m_increased(kernel_k_to_kernel_u(*krnl), post_u, krnl.prc_mp.spec_index(target).view_rodata().view().owning_container)
            || kernel_u_container_quota_1g_increased(kernel_k_to_kernel_u(*krnl), post_u, krnl.prc_mp.spec_index(target).view_rodata().view().owning_container),
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> krnl.ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && krnl.ctn_mp.spec_index(container).view().uppertree_seq.view().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    kill_step_pre_from_k(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, target, stage, scope); kill_refund_pre_from_k(krnl, target, krnl.prc_mp.spec_index(target).view_rodata().view().owning_container);
    kill_refund_step_from_u(kernel_k_to_kernel_u(*krnl), post_u, cpu_id); kill_trace_push(steps, before, start, pre, kernel_k_to_kernel_u(*krnl), post_u, cpu_id, ctx);
}

/// Growing the 4K, 2M, or 1G quota of the target's container or of one of its ancestors, and nothing else, after the flush is
/// recorded or while retiring, is a refund step.
pub(crate) proof fn kill_refund_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        kill_stage(pre, cpu_id) == (KillStage::Reclaim { flushed: true }) || kill_stage(pre, cpu_id) is Retire,
        kernel_u_container_quota_4k_increased(pre, post, pre.process_map[kill_target(pre, cpu_id)].owning_container)
            || kernel_u_container_quota_2m_increased(pre, post, pre.process_map[kill_target(pre, cpu_id)].owning_container)
            || kernel_u_container_quota_1g_increased(pre, post, pre.process_map[kill_target(pre, cpu_id)].owning_container),
    ensures kill_process_refund_step(pre, post, cpu_id),
{ reveal(kill_process_refund_step); }

/// The finish step pushed after the partial trace that starts at `start`, in which each retired target accounts for at most
/// `process_tables_step_bound()` table-phase steps, completes the trace of a kill.
pub(crate) proof fn kill_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, KillTraceCtx::Process { child_index }),
        kill_process_table_count(before.subrange(start, before.len() as int), cpu_id) <= process_tables_step_bound() * kill_process_retire_count(before.subrange(start, before.len() as int), cpu_id),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        kill_process_finish_step_pre(finish_pre, cpu_id),
        kill_process_finish_step(finish_pre, post, cpu_id),
    ensures kill_process_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, child_index, true),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_process_syscall_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: finish_pre, new_u: post }));
    assert(steps.view().subrange(start, steps.view().len() as int).drop_last() =~= before.subrange(start, before.len() as int));
}

/// A rejected call records no step.
pub(crate) proof fn kill_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, child_index: usize)
    requires trace.len() == 0,
    ensures kill_process_syscall_trace(trace, pre, pre, cpu_id, child_index, false),
{ reveal(kill_process_syscall_trace); }

/// A step pushed onto a nonempty trace adds one table-phase step exactly when it starts in the table phase.
pub(crate) proof fn trace_push_implies_kill_process_table_count_step_added(trace: Seq<KernelStep>, step: KernelStep, cpu_id: CpuId)
    requires 1 <= trace.len(),
    ensures kill_process_table_count(trace.push(step), cpu_id) == kill_process_table_count(trace, cpu_id) + if kill_process_table_phase_step(step, cpu_id) { 1nat } else { 0nat },
{ reveal(kill_process_table_count); assert(trace.push(step).drop_last() =~= trace); }

/// A step pushed onto a nonempty trace adds one retire step exactly when it retires a target.
pub(crate) proof fn trace_push_implies_kill_process_retire_count_step_added(trace: Seq<KernelStep>, step: KernelStep, cpu_id: CpuId)
    requires 1 <= trace.len(),
    ensures kill_process_retire_count(trace.push(step), cpu_id) == kill_process_retire_count(trace, cpu_id) + if kill_process_retire_step(step.old_u, step.new_u, cpu_id) { 1nat } else { 0nat },
{ reveal(kill_process_retire_count); assert(trace.push(step).drop_last() =~= trace); }

/// Extending `before` to `after` adds at most as many table-phase steps after `start` as it adds steps.
pub(crate) proof fn steps_extended_implies_kill_process_table_count_le_len_added(before: Seq<KernelStep>, after: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        kernel_steps_prefix_unchanged(before, after),
    ensures
        before.len() <= after.len(),
        kill_process_table_count(after.subrange(start, after.len() as int), cpu_id) <= kill_process_table_count(before.subrange(start, before.len() as int), cpu_id) + (after.len() - before.len()),
    decreases after.len() - before.len(),
{
    reveal(kernel_steps_prefix_unchanged);
    if after.len() == before.len() { assert(after.subrange(start, after.len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        let shorter = after.drop_last();
        steps_extended_implies_kill_process_table_count_le_len_added(before, shorter, start, cpu_id);
        reveal(kill_process_table_count);
        assert(after.subrange(start, after.len() as int).drop_last() =~= shorter.subrange(start, shorter.len() as int));
    }
}

/// Extending `before` to `after` with steps that all start outside the table phase keeps the table-phase count after `start`.
pub(crate) proof fn steps_extended_outside_table_phase_implies_kill_process_table_count_unchanged(before: Seq<KernelStep>, after: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        kernel_steps_prefix_unchanged(before, after),
        forall|j: int| #![trigger after[j]] before.len() <= j < after.len() ==> !kill_process_table_phase_step(after[j], cpu_id),
    ensures kill_process_table_count(after.subrange(start, after.len() as int), cpu_id) == kill_process_table_count(before.subrange(start, before.len() as int), cpu_id),
    decreases after.len() - before.len(),
{
    reveal(kernel_steps_prefix_unchanged);
    if after.len() == before.len() { assert(after.subrange(start, after.len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        let shorter = after.drop_last();
        assert(shorter.subrange(0, before.len() as int) =~= before);
        steps_extended_outside_table_phase_implies_kill_process_table_count_unchanged(before, shorter, start, cpu_id);
        reveal(kill_process_table_count);
        assert(after.subrange(start, after.len() as int).drop_last() =~= shorter.subrange(start, shorter.len() as int));
        assert(after.subrange(start, after.len() as int).last() == after[after.len() - 1]);
    }
}

/// Extending `before` to `after` never lowers the retire count after `start`.
pub(crate) proof fn steps_extended_implies_kill_process_retire_count_monotone(before: Seq<KernelStep>, after: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        kernel_steps_prefix_unchanged(before, after),
    ensures kill_process_retire_count(before.subrange(start, before.len() as int), cpu_id) <= kill_process_retire_count(after.subrange(start, after.len() as int), cpu_id),
    decreases after.len() - before.len(),
{
    reveal(kernel_steps_prefix_unchanged);
    if after.len() == before.len() { assert(after.subrange(start, after.len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        let shorter = after.drop_last();
        assert(shorter.subrange(0, before.len() as int) =~= before);
        steps_extended_implies_kill_process_retire_count_monotone(before, shorter, start, cpu_id);
        reveal(kill_process_retire_count);
        assert(after.subrange(start, after.len() as int).drop_last() =~= shorter.subrange(start, shorter.len() as int));
    }
}
} // verus!

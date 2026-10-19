use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_container::syscall_kill_container_spec::kill_container_partial_trace;

verus! {
/// The killer on `cpu_id` holds its cpu, its process `process_ptr`, and itself `thread_ptr`, and its progress records a
/// kill of the marked, write-locked `target` at `stage`.
pub(crate) proof fn kill_step_pre_from_u(u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage)
    requires
        index_valid(NUM_CPUS, cpu_id),
        u.cpu_array[cpu_id as int].lock_state is WriteLocked,
        u.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        u.process_map.dom().contains(process_ptr),
        u.process_map[process_ptr].lock_state is WriteLocked,
        u.thread_map.dom().contains(thread_ptr),
        u.thread_map[thread_ptr].lock_state is WriteLocked,
        u.thread_map[thread_ptr].syscall_progress == kill_progress(target, stage),
        u.process_map.dom().contains(target),
        u.process_map[target].lock_state is WriteLocked,
        u.process_map[target].killed,
    ensures
        kill_process_step_pre(u, cpu_id),
        kill_killer(u, cpu_id) == thread_ptr,
        kill_target(u, cpu_id) == target,
        kill_stage(u, cpu_id) == stage,
{ reveal(kill_process_step_pre); }

/// The killer on `cpu_id` write-holding its cpu, its process `process_ptr`, itself `thread_ptr`, and the marked `target`,
/// with its progress recording the kill of `target` at `stage`, satisfies the kill's step precondition on `krnl`.
pub(crate) proof fn kill_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_progress(target, stage),
    ensures
        kill_process_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kill_killer(kernel_k_to_kernel_u(*krnl), cpu_id) == thread_ptr,
        kill_target(kernel_k_to_kernel_u(*krnl), cpu_id) == target,
        kill_stage(kernel_k_to_kernel_u(*krnl), cpu_id) == stage,
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].syscall_progress == kill_progress(target, stage),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_write_held_context_projection(krnl, lctx, cpu_id, target, thread_ptr, None);
    kernel_cpu_projection_at(krnl, cpu_id); kernel_process_projection_at(krnl, target);
    kill_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, target, stage);
}

/// A cpu that is not running or is marked by a killer makes the kill return CpuIdle.
pub(crate) proof fn kill_idle_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        !(krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !krnl.cpu_arr.spec_index(cpu_id).view().being_killed()),
    ensures kill_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index) is CpuIdle,
{ kernel_cpu_projection_at(krnl, cpu_id); }

/// On a running unmarked cpu that runs `thread_ptr` of `process_ptr`, a marked process or thread, a child index past the
/// children, and a marked child each reject the kill.
pub(crate) proof fn kill_result_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
    ensures
        ({
            let process = krnl.prc_mp.spec_index(process_ptr);
            let children = process.view().children.view();
            let result = kill_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index);
            &&& process.being_killed() ==> result is ErrorProcessKilled
            &&& !process.being_killed() && krnl.thr_mp.spec_index(thread_ptr).being_killed() ==> result is ErrorThreadKilled
            &&& !process.being_killed() && !krnl.thr_mp.spec_index(thread_ptr).being_killed() && child_index >= children.len() ==> result is ErrorInvalidChild
            &&& !process.being_killed() && !krnl.thr_mp.spec_index(thread_ptr).being_killed() && child_index < children.len() && krnl.prc_mp.dom().contains(children[child_index as int])
                && krnl.prc_mp.spec_index(children[child_index as int]).being_killed() ==> result is ErrorProcessKilled
        }),
{
    let children = krnl.prc_mp.spec_index(process_ptr).view().children.view();
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_process_projection_at(krnl, process_ptr);
    if child_index < children.len() && krnl.prc_mp.dom().contains(children[child_index as int]) { kernel_process_projection_at(krnl, children[child_index as int]); }
}

/// The unlocked running unmarked cpu, process, and thread with no syscall in progress, whose live child at `child_index`
/// is `child_ptr`, are so on the projection, where the kill succeeds.
pub(crate) proof fn kill_enter_pre_from_k(krnl: &KernelK, cpu_id: CpuId, child_index: usize, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, child_ptr: RwLockProcessPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let process = krnl.prc_mp.spec_index(process_ptr);
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            &&& !cpu.locked()
            &&& cpu.view().view().state is Running
            &&& !cpu.being_killed()
            &&& cpu.view().view().current_process == Some(process_ptr)
            &&& cpu.view().view().current_thread == Some(thread_ptr)
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& !process.locked()
            &&& !process.being_killed()
            &&& krnl.thr_mp.dom().contains(thread_ptr)
            &&& !thread.locked()
            &&& !thread.being_killed()
            &&& thread.view().syscall_progress.view() is None
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == process_ptr
            &&& child_index < process.view().children.view().len()
            &&& process.view().children.view()[child_index as int] == child_ptr
            &&& krnl.prc_mp.dom().contains(child_ptr)
            &&& !krnl.prc_mp.spec_index(child_ptr).being_killed()
        }),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let cpu = u.cpu_array[cpu_id as int];
            let process = u.process_map[process_ptr];
            let thread = u.thread_map[thread_ptr];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& !cpu.killed
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& u.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& u.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& child_index < process.children.len()
            &&& process.children[child_index as int] == child_ptr
            &&& u.process_map.dom().contains(child_ptr)
            &&& !u.process_map[child_ptr].killed
        }),
        kill_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child_index) is Success,
{ kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_thread_projection_at(krnl, thread_ptr); kernel_process_projection_at(krnl, process_ptr); kernel_process_projection_at(krnl, child_ptr); }

/// The first child `child_ptr` of the target on `krnl` is its first child on the projection.
pub(crate) proof fn kill_mark_child_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.dom().contains(child_ptr),
        0 < krnl.prc_mp.spec_index(target).view().children.view().len(),
        krnl.prc_mp.spec_index(target).view().children.view()[0] == child_ptr,
    ensures
        0 < kernel_k_to_kernel_u(*krnl).process_map[target].children.len(),
        kernel_k_to_kernel_u(*krnl).process_map[target].children[0] == child_ptr,
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(child_ptr),
{ kernel_process_projection_at(krnl, target); kernel_process_projection_at(krnl, child_ptr); }

/// The unlocked first thread `victim_ptr` of the childless target on `krnl`, waiting for a reply, is so on the projection.
pub(crate) proof fn kill_dangling_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.thr_mp.dom().contains(victim_ptr),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        0 < krnl.prc_mp.spec_index(target).view().owned_threads.view().len(),
        krnl.prc_mp.spec_index(target).view().owned_threads.view()[0] == victim_ptr,
        krnl.thr_mp.spec_index(victim_ptr).view().state is WAITING_REPLY,
        !krnl.thr_mp.spec_index(victim_ptr).locked(),
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
        krnl.thr_mp.dom().contains(victim_ptr),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        0 < krnl.prc_mp.spec_index(target).view().owned_threads.view().len(),
        krnl.prc_mp.spec_index(target).view().owned_threads.view()[0] == victim_ptr,
        !krnl.thr_mp.spec_index(victim_ptr).view().state.is_reply_waiting(),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.process_map[target].children.len() == 0
            &&& 0 < u.process_map[target].owned_threads.len()
            &&& u.process_map[target].owned_threads[0] == victim_ptr
            &&& u.thread_map.dom().contains(victim_ptr)
            &&& !u.thread_map[victim_ptr].state.is_reply_waiting()
        }),
{ kernel_process_projection_at(krnl, target); kernel_thread_projection_at(krnl, victim_ptr); }

/// The marked victim `victim_ptr` that the killer on `cpu_id` write-holds with its cpu and the target, recorded by the
/// kill, in state `state`, owned by `container_ptr`, and waiting on `endpoint`, is the kill's write-locked marked victim
/// on the projection.
pub(crate) proof fn kill_victim_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, state: ThreadState, container_ptr: RwLockContainerPtr,
    endpoint: Option<RwLockEndpointPtr>,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), victim_ptr, TypedLockMode::Write),
        krnl.thr_mp.dom().contains(victim_ptr),
        krnl.thr_mp.spec_index(victim_ptr).being_killed(),
        krnl.thr_mp.spec_index(victim_ptr).view().state == state,
        krnl.thr_mp.spec_index(victim_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(victim_ptr).view().blocking_endpoint_ptr == endpoint,
        kill_stage(kernel_k_to_kernel_u(*krnl), cpu_id) == (KillStage::Thread { thread: victim_ptr }),
    ensures
        kill_process_victim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).thread_map[victim_ptr].state == state,
        kernel_k_to_kernel_u(*krnl).thread_map[victim_ptr].owning_container == container_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[victim_ptr].blocking_endpoint_ptr == endpoint,
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, target, victim_ptr, None); kernel_thread_projection_at(krnl, victim_ptr); }

/// The killer's write-held cpu, process, and thread, with its progress walking its own process, are so on the
/// projection.
pub(crate) proof fn kill_finish_pre_from_k(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_progress(process_ptr, KillStage::Walk),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& u.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& u.process_map.dom().contains(process_ptr)
            &&& u.process_map[process_ptr].lock_state is WriteLocked
            &&& u.thread_map.dom().contains(thread_ptr)
            &&& u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& u.thread_map[thread_ptr].syscall_progress == kill_progress(process_ptr, KillStage::Walk)
        }),
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, cpu_id); }

/// The target without children or threads on `krnl` has none on the projection.
pub(crate) proof fn kill_reassign_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
    ensures
        kernel_k_to_kernel_u(*krnl).process_map[target].children.len() == 0,
        kernel_k_to_kernel_u(*krnl).process_map[target].owned_threads.len() == 0,
{ kernel_process_projection_at(krnl, target); }

/// The empty live target owning no PCI function on `krnl` is so on the projection, with a page table.
pub(crate) proof fn kill_lock_table_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
    ensures
        ({
            let process = kernel_k_to_kernel_u(*krnl).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& !process.zombie
            &&& process.owned_pci_functions.is_empty()
            &&& process.pagetable is Some
        }),
{ kernel_process_projection_at(krnl, target); }

/// The empty zombie target owning no PCI function on `krnl` is so on the projection.
pub(crate) proof fn kill_zombie_retire_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
    ensures
        ({
            let process = kernel_k_to_kernel_u(*krnl).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& process.zombie
            &&& process.owned_pci_functions.is_empty()
        }),
{ kernel_process_projection_at(krnl, target); }

/// The empty zombie target owning no PCI function, a child of `parent_ptr`, on `krnl` is so on the projection.
pub(crate) proof fn kill_retire_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        krnl.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
    ensures
        ({
            let process = kernel_k_to_kernel_u(*krnl).process_map[target];
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& process.zombie
            &&& process.owned_pci_functions.is_empty()
            &&& process.parent == Some(parent_ptr)
        }),
{ kernel_process_projection_at(krnl, target); }

/// The live target on `krnl` is live on the projection.
pub(crate) proof fn kill_zombify_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
    ensures !kernel_k_to_kernel_u(*krnl).process_map[target].zombie,
{ kernel_process_projection_at(krnl, target); }

/// The live target's page table `pagetable` and IOMMU table `iommu_table`, write-held by the killer `thread_ptr` on
/// `cpu_id` that reclaims the target at `stage`, are write-locked on the projection, which shows the target's PCID.
pub(crate) proof fn kill_reclaim_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(target).view().iommu_table == iommu_table,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        iommu_table matches Some(t) ==> krnl.it_mp.dom().contains(t) && typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write),
        kill_target(kernel_k_to_kernel_u(*krnl), cpu_id) == target,
        kill_stage(kernel_k_to_kernel_u(*krnl), cpu_id) == stage,
    ensures
        kill_process_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, stage),
        (kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table is Some) == (iommu_table is Some),
        kernel_k_to_kernel_u(*krnl).process_map[target].pcid == krnl.prc_mp.spec_index(target).view_rodata().view().pcid,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, target, thread_ptr, None);
    if let Some(t) = iommu_table {
        kernel_iommu_table_mappings_projection_at(krnl, target); krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t);
    } else { kernel_process_projection_at(krnl, target); }
}

/// A user VA `va` at or above the kernel L4 end of a page table on `krnl` is at or above the projection's kernel L4 end.
pub(crate) proof fn kill_leaf_pre_from_k(krnl: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        krnl.inv(),
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
    ensures kernel_k_to_kernel_u(*krnl).kernel_l4_end <= spec_v2l4index(va),
{ kernel_l4_end_projection_at(krnl, pagetable); }

/// With no present user 4K leaf at or above the kernel L4 end of the live target's page table on `krnl`, the target's
/// projected page table has no user 4K mapping.
pub(crate) proof fn kill_user_4k_unmapped_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(target).view().pagetable),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(target).view().pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i
                && krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(target).view().pagetable).view().kernel_l4_end <= l4i
                && krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(target).view().pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(target).view().pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
    ensures
        kernel_k_to_kernel_u(*krnl).process_map[target].pagetable is Some,
        kill_process_user_4k_unmapped(kernel_k_to_kernel_u(*krnl), kernel_k_to_kernel_u(*krnl).process_map[target].pagetable->Some_0),
{ kernel_pagetable_user_4k_unmapped_projection_at(krnl, target); }

/// With no 4K leaf in the live target's IOMMU table on `krnl`, its projected IOMMU table has no 4K mapping.
pub(crate) proof fn kill_iommu_unmapped_pre_from_k(krnl: &KernelK, target: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.prc_mp.dom().contains(target),
        !krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view().iommu_table is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger krnl.it_mp.spec_index(krnl.prc_mp.spec_index(target).view().iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> !krnl.it_mp.spec_index(krnl.prc_mp.spec_index(target).view().iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    ensures
        kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table is Some,
        kill_process_iommu_4k_unmapped(kernel_k_to_kernel_u(*krnl).process_map[target].iommu_table->Some_0),
{ kernel_iommu_table_4k_unmapped_projection_at(krnl, target); }

/// The killer's cpu, owned by `container_ptr` on `krnl`, is owned by it on the projection.
pub(crate) proof fn kill_refund_pre_from_k(krnl: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
    ensures kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == container_ptr,
{ kernel_cpu_projection_at(krnl, cpu_id); }


/// Write-locking the cpu, the process, and the thread, marking and write-locking the live child at `child_index`, and
/// recording the walk of that child is the enter step on `pre`/`post`.
pub(crate) proof fn kill_enter_step_from_u(
    pre: KernelU, locked: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    child_ptr: RwLockProcessPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        process_ptr != child_ptr,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let process = pre.process_map[process_ptr];
            let thread = pre.thread_map[thread_ptr];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& child_index < process.children.len()
            &&& process.children[child_index as int] == child_ptr
            &&& pre.process_map.dom().contains(child_ptr)
            &&& !pre.process_map[child_ptr].killed
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
        marked == (KernelU { process_map: locked.process_map.insert(child_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..locked.process_map[child_ptr] }), ..locked }),
        post == (KernelU { thread_map: marked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(child_ptr, KillStage::Walk), ..marked.thread_map[thread_ptr] }), ..marked }),
    ensures
        kill_process_enter_step_pre(pre, cpu_id, child_index),
        kill_process_enter_step(pre, post, cpu_id, child_index),
{
    reveal(kill_process_enter_step_pre); reveal(kill_process_enter_step);
    assert(post.thread_map =~= pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: kill_progress(child_ptr, KillStage::Walk), ..pre.thread_map[thread_ptr] }));
}

/// Marking and write-locking the first child `child_ptr` of the target and recording its walk is a middle step.
pub(crate) proof fn kill_mark_child_step_from_u(pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        0 < pre.process_map[target].children.len(),
        pre.process_map[target].children[0] == child_ptr,
        pre.process_map.dom().contains(child_ptr),
        marked == (KernelU { process_map: pre.process_map.insert(child_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.process_map[child_ptr] }), ..pre }),
        post == (KernelU { thread_map: marked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(child_ptr, KillStage::Walk), ..marked.thread_map[thread_ptr] }), ..marked }),
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
    pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        0 < pre.process_map[target].owned_threads.len(),
        pre.process_map[target].owned_threads[0] == victim_ptr,
        pre.thread_map.dom().contains(victim_ptr),
        !pre.thread_map[victim_ptr].state.is_reply_waiting(),
        victim_ptr != thread_ptr,
        marked == (KernelU { thread_map: pre.thread_map.insert(victim_ptr, ThreadU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.thread_map[victim_ptr] }), ..pre }),
        post == (KernelU {
            thread_map: marked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Thread { thread: victim_ptr }), ..marked.thread_map[thread_ptr] }),
            ..marked
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_mark_thread_step); }

/// The recorded victim leaving shard `shard` of its container's scheduler and becoming killed is a middle step.
pub(crate) proof fn kill_dequeue_scheduled_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, shard: CpuId)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_step_pre(pre, cpu_id),
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state == (ThreadState::SCHEDULED { cpu_id: shard }),
        pre.thread_map[victim_ptr].owning_container == container_ptr,
        pre.container_map.dom().contains(container_ptr),
        ({
            let container = pre.container_map[container_ptr];
            post == (KernelU {
                container_map: pre.container_map.insert(container_ptr, ContainerU {
                    scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(victim_ptr)), ..container
                }),
                thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..pre.thread_map[victim_ptr] }),
                ..pre
            })
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_dequeue_scheduled_step); }

/// The recorded victim leaving the queue of the endpoint `endpoint_ptr` it waits on and becoming killed is a middle step.
pub(crate) proof fn kill_dequeue_endpoint_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_step_pre(pre, cpu_id),
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state.is_endpoint_waiting(),
        pre.thread_map[victim_ptr].blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.endpoint_map.dom().contains(endpoint_ptr),
        post == (KernelU {
            endpoint_map: pre.endpoint_map.insert(endpoint_ptr, EndpointU { queue: pre.endpoint_map[endpoint_ptr].queue.remove_value(victim_ptr), ..pre.endpoint_map[endpoint_ptr] }),
            thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..pre.thread_map[victim_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_dequeue_endpoint_step); }

/// Evicting the recorded victim from the remote cpu `remote` it runs on is a middle step.
pub(crate) proof fn kill_evict_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim_ptr: RwLockThreadPtr, remote: CpuId)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_step_pre(pre, cpu_id),
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state == (ThreadState::RUNNING { cpu_id: remote }),
        index_valid(NUM_CPUS, remote),
        remote != cpu_id,
        post == (KernelU {
            cpu_array: pre.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, current_process: None, current_thread: None, ..pre.cpu_array[remote as int] }),
            thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, ..pre.thread_map[victim_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_evict_step); }

/// The killed recorded victim leaving the target, which absorbs its quota, and the kill walking the target again is a
/// middle step.
pub(crate) proof fn kill_unlink_step_from_u(
    pre: KernelU, left: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_process_victim_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) == (KillStage::Thread { thread: victim_ptr }),
        pre.thread_map[victim_ptr].state is KILLED,
        thread_ptr != victim_ptr,
        ({
            let process = pre.process_map[target];
            let victim = pre.thread_map[victim_ptr];
            left == (KernelU {
                process_map: pre.process_map.insert(target, kill_process_absorb_thread(process, victim_ptr, victim)),
                thread_map: pre.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..victim }),
                ..pre
            })
        }),
        post == (KernelU { thread_map: left.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Walk), ..left.thread_map[thread_ptr] }), ..left }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_unlink_step); }

/// Clearing the progress of the killer, which walks its own process again, and unlocking it, its process, and its cpu is
/// the finish step on `pre`/`post`.
pub(crate) proof fn kill_finish_step_from_u(pre: KernelU, cleared: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_array[cpu_id as int].lock_state is WriteLocked,
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.process_map.dom().contains(process_ptr),
        pre.process_map[process_ptr].lock_state is WriteLocked,
        pre.thread_map.dom().contains(thread_ptr),
        pre.thread_map[thread_ptr].lock_state is WriteLocked,
        pre.thread_map[thread_ptr].syscall_progress == kill_progress(process_ptr, KillStage::Walk),
        cleared == (KernelU { thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: None, ..pre.thread_map[thread_ptr] }), ..pre }),
        post == (KernelU {
            cpu_array: cleared.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..cleared.cpu_array[cpu_id as int] }),
            process_map: cleared.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..cleared.process_map[process_ptr] }),
            thread_map: cleared.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..cleared.thread_map[thread_ptr] }),
            ..cleared
        }),
    ensures
        kill_process_finish_step_pre(pre, cpu_id),
        kill_process_finish_step(pre, post, cpu_id),
{
    reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step);
    assert(post.thread_map =~= pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map[thread_ptr] }));
}

/// Handing every PCI function of the empty target to the killer's process `process_ptr`, detached and with their IOTLB
/// domains emptied, is a middle step.
pub(crate) proof fn kill_reassign_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, target: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        post.iommu_tlb.dom() == pre.iommu_tlb.dom(),
        forall|bus: usize, device: usize, function: usize| #![trigger post.iommu_tlb[pci_bdf_did(bus, device, function)]]
            pci_bdf_valid(bus, device, function) ==> post.iommu_tlb[pci_bdf_did(bus, device, function)]
                == if kill_process_reassigns(pre.iommu_root_table, target, bus as int, device as int, function as int) { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } }
                else { pre.iommu_tlb[pci_bdf_did(bus, device, function)] },
        post == (KernelU {
            process_map: pre.process_map.insert(target, ProcessU { owned_pci_functions: Set::empty(), ..pre.process_map[target] })
                .insert(process_ptr, ProcessU { owned_pci_functions: pre.process_map[process_ptr].owned_pci_functions.union(pre.process_map[target].owned_pci_functions), ..pre.process_map[process_ptr] }),
            iommu_root_table: kill_process_reassigned_table(pre.iommu_root_table, target, process_ptr),
            iommu_tlb: post.iommu_tlb,
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_reassign_functions_step); }

/// Write-locking the page table and IOMMU table of the empty live target owning no PCI function, and recording that
/// nothing is flushed yet, is a middle step.
pub(crate) proof fn kill_lock_table_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        !pre.process_map[target].zombie,
        pre.process_map[target].owned_pci_functions.is_empty(),
        pre.process_map[target].pagetable is Some,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Reclaim { flushed: false }), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[target].pagetable->Some_0 }),
                iommu_table: match pre.process_map[target].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked, ..t }), None => None },
                ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_lock_table_step); }

/// Clearing the user 4K leaf `va` of the target's write-locked page table before the flush is a middle step.
pub(crate) proof fn kill_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, va: VAddr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, KillStage::Reclaim { flushed: false }),
        pre.process_map[target].pagetable->Some_0.mapping_4k.dom().contains(va),
        spec_va_4k_valid(va),
        pre.kernel_l4_end <= spec_v2l4index(va),
        post == (KernelU {
            process_map: pre.process_map.insert(target, ProcessU {
                pagetable: Some(PageTableU { mapping_4k: pre.process_map[target].pagetable->Some_0.mapping_4k.remove(va), ..pre.process_map[target].pagetable->Some_0 }),
                ..pre.process_map[target]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: pre.thread_map[thread_ptr].syscall_progress, ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    reveal(kill_process_leaf_step); reveal(kill_process_step_pre);
    let mapping = pre.process_map[target].pagetable->Some_0.mapping_4k;
    let kept = post.process_map[target].pagetable->Some_0.mapping_4k.dom();
    assert(pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: pre.thread_map[thread_ptr].syscall_progress, ..pre.thread_map[thread_ptr] }) =~= pre.thread_map);
    assert(mapping.dom().difference(kept) =~= set![va]);
    assert(mapping.remove(va) =~= mapping.restrict(kept));
}

/// Recording the flush of the target's PCID is a middle step.
pub(crate) proof fn kill_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_process_flush_step_pre(pre, cpu_id),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Reclaim { flushed: true }), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_flushed_step); }

/// Clearing the 4K leaf `iova` of the target's write-locked IOMMU table after the flush is a middle step.
pub(crate) proof fn kill_iommu_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, target: RwLockProcessPtr, iova: VAddr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, KillStage::Reclaim { flushed: true }),
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
    reveal(kill_process_iommu_leaf_step);
    let mapping = pre.process_map[target].iommu_table->Some_0.mapping_4k;
    let kept = post.process_map[target].iommu_table->Some_0.mapping_4k.dom();
    assert(mapping.dom().difference(kept) =~= set![iova]);
    assert(mapping.remove(iova) =~= mapping.restrict(kept));
}

/// Returning the target's whole `size` quota to its container and recording the return is a middle step.
pub(crate) proof fn kill_quota_step_from_u(pre: KernelU, returned: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, size: PageSize)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, kill_process_quota_stage_before(size)),
        pre.container_map.dom().contains(pre.process_map[target].owning_container),
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
            thread_map: returned.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Quota { returned: size }), ..returned.thread_map[thread_ptr] }),
            ..returned
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_quota_step); }

/// Unlocking the target's reclaimed page table and IOMMU table once every quota size is returned is a middle step.
pub(crate) proof fn kill_unlock_table_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_process_reclaim_step_pre(pre, cpu_id, KillStage::Quota { returned: PageSize::SZ1g }),
        kill_process_user_4k_unmapped(pre, pre.process_map[target].pagetable->Some_0),
        pre.process_map[target].iommu_table is Some ==> kill_process_iommu_4k_unmapped(pre.process_map[target].iommu_table->Some_0),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Zombie), ..pre.thread_map[thread_ptr] }),
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
pub(crate) proof fn kill_zombify_step_from_u(pre: KernelU, zombified: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Zombie,
        !pre.process_map[target].zombie,
        pre.container_map.dom().contains(pre.process_map[target].owning_container),
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
            thread_map: zombified.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Retire), ..zombified.thread_map[thread_ptr] }),
            ..zombified
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_zombify_step); }

/// An empty zombie target owning no PCI function going straight to retiring is a middle step.
pub(crate) proof fn kill_zombie_retire_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Walk,
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        pre.process_map[target].zombie,
        pre.process_map[target].owned_pci_functions.is_empty(),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(target, KillStage::Retire), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_zombie_retire_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(crate) proof fn kill_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        kill_process_enter_step_pre(pre, cpu_id, child_index),
        kill_process_enter_step(pre, post, cpu_id, child_index),
    ensures kill_partial_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, KillTraceCtx::Process { child_index }),
{ reveal(kill_partial_trace); reveal(kill_process_partial_trace); }

/// Retiring the empty zombie target, which raises its container's 4K quota to `quota`, and walking its parent again is a
/// middle step.
pub(crate) proof fn kill_retire_step_from_u(
    pre: KernelU, retired: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, quota: usize,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_target(pre, cpu_id) == target,
        kill_stage(pre, cpu_id) is Retire,
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        pre.process_map[target].zombie,
        pre.process_map[target].owned_pci_functions.is_empty(),
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
            thread_map: retired.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_progress(parent_ptr, KillStage::Walk), ..retired.thread_map[thread_ptr] }),
            ..retired
        }),
    ensures kill_process_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_retire_step); }

/// A middle step pushed after the partial trace that starts at `start` extends it.
pub(crate) proof fn kill_trace_push(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId, ctx: KillTraceCtx)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        steps.view() == before.push(KernelStep { old_u: step_pre, new_u: step_post }),
        kill_process_middle_step(KernelStep { old_u: step_pre, new_u: step_post }, cpu_id),
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: step_pre, new_u: step_post }));
}

/// Steps reclaiming killed threads, recorded after the partial trace that starts at `start` while the killer's cpu, the
/// killer, and the lock modes and kill marks of its held processes keep their projection at `entry`, extend it.
pub(crate) proof fn kill_trace_from_killed_thread_reclaim(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, process_ptr: RwLockProcessPtr,
    target: RwLockProcessPtr,
)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        kernel_steps_prefix_unchanged(before, steps.view()),
        kill_process_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kill_target(entry, cpu_id) == target,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let thread_ptr = entry.cpu_array[cpu_id as int].current_thread->Some_0;
            &&& kernel_u_killed_thread_reclaim_step(old_u, steps.view()[j].new_u, cpu_id)
            &&& old_u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry.process_map[process_ptr].lock_state
            &&& old_u.process_map.dom().contains(target)
            &&& old_u.process_map[target].lock_state == entry.process_map[target].lock_state
            &&& old_u.process_map[target].killed == entry.process_map[target].killed
        },
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace); reveal(kill_process_step_pre); reveal(kernel_steps_prefix_unchanged);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int) + steps.view().subrange(before.len() as int, steps.view().len() as int));
}

/// A flush step of the target's PCID `pcid`, recorded after the partial trace that starts at `start` once every user 4K
/// leaf of the target is cleared, extends it.
pub(crate) proof fn kill_trace_push_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, pcid: Pcid,
)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        steps.view() == record_user_view_change(before, step_pre, step_post),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> kernel_u_cpu_tlb_cleared(steps.view()[j].old_u, steps.view()[j].new_u, pcid),
        kill_process_step_pre(step_pre, cpu_id),
        kill_process_flush_step_pre(step_pre, cpu_id),
        step_pre.process_map[kill_target(step_pre, cpu_id)].pcid == pcid,
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace);
    if step_pre == step_post { assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        assert(steps.view()[before.len() as int] == KernelStep { old_u: step_pre, new_u: step_post });
        assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: step_pre, new_u: step_post }));
    }
}

/// Refund steps, recorded after the partial trace that starts at `start` while the killer's cpu and the lock modes and
/// kill marks of the killer's process and the target keep their projection at `entry` and the killer keeps its lock
/// mode and its progress at `stage`, each growing the 4K quota of the killer's container `container_ptr`, extend it.
pub(crate) proof fn kill_trace_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, ctx: KillTraceCtx, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, stage: KillStage, container_ptr: RwLockContainerPtr,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        kill_process_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        entry.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        entry.cpu_array[cpu_id as int].owning_container == container_ptr,
        kill_target(entry, cpu_id) == target,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, container_ptr)
            &&& old_u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].syscall_progress == kill_progress(target, stage)
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry.process_map[process_ptr].lock_state
            &&& old_u.process_map.dom().contains(target)
            &&& old_u.process_map[target].lock_state == entry.process_map[target].lock_state
            &&& old_u.process_map[target].killed == entry.process_map[target].killed
        },
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_container_partial_trace); reveal(kill_process_step_pre);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int) + steps.view().subrange(before.len() as int, steps.view().len() as int));
}

/// The finish step pushed after the partial trace that starts at `start` completes the trace of a kill.
pub(crate) proof fn kill_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize)
    requires
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, KillTraceCtx::Process { child_index }),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        kill_process_finish_step_pre(finish_pre, cpu_id),
        kill_process_finish_step(finish_pre, post, cpu_id),
    ensures kill_process_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, child_index, true),
{
    reveal(kill_partial_trace); reveal(kill_process_partial_trace); reveal(kill_process_syscall_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: finish_pre, new_u: post }));
}

/// A rejected call records no step.
pub(crate) proof fn kill_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, child_index: usize)
    requires trace.len() == 0,
    ensures kill_process_syscall_trace(trace, pre, pre, cpu_id, child_index, false),
{ reveal(kill_process_syscall_trace); }
} // verus!

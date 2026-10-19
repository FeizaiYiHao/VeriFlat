use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::kill_killer;

verus! {
/// The killer on `cpu_id` write-holding its cpu, its cpu's container, its process `process_ptr`, itself `thread_ptr`,
/// and the marked container `container_ptr` satisfies the container kill's step precondition on `krnl` with that
/// container at `stage`, and the container's children and processes project as they are.
pub(crate) proof fn kill_container_cpus_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, stage: ContainerKillStage,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, stage),
        krnl.ctn_mp.spec_index(container_ptr).being_killed(),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& kill_container_step_pre(u, cpu_id)
            &&& kill_killer(u, cpu_id) == thread_ptr
            &&& kill_container_target(u, cpu_id) == container_ptr
            &&& kill_container_stage(u, cpu_id) == stage
            &&& u.cpu_array[cpu_id as int].owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
            &&& u.container_map[container_ptr].children == krnl.ctn_mp.spec_index(container_ptr).view().children.view()
            &&& u.container_map[container_ptr].owned_processes == krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view()
        }),
{
    let owner = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, cpu_id);
    krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), owner); krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr);
    kernel_container_projection_at(krnl, owner); kernel_container_projection_at(krnl, container_ptr); kernel_u_domains_projection(krnl);
    reveal(kill_container_step_pre);
}

/// The unlocked cpu `moved`, which is not Running and belongs to `container_ptr`, projects so.
pub(crate) proof fn kill_container_move_cpu_pre_from_k(krnl: &KernelK, moved: CpuId, container_ptr: RwLockContainerPtr)
    requires
        index_valid(NUM_CPUS, moved),
        krnl.cpu_arr.spec_index(moved).view().locking_thread() is None,
        !(krnl.cpu_arr.spec_index(moved).view().view().view().state is Running),
        krnl.cpu_arr.spec_index(moved).view().view().view().owning_container == container_ptr,
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        ({
            let cpu = kernel_k_to_kernel_u(*krnl).cpu_array[moved as int];
            &&& cpu.owning_container == container_ptr
            &&& cpu.state is Idle || cpu.state is Off
            &&& cpu.lock_state is Unlocked
        }),
{ kernel_cpu_projection_at(krnl, moved); }

/// Marking and write-locking the cpu set of the marked target `container_ptr`, which has no child containers and no
/// processes, and moving the kill on to its cpus is a middle step of the container kill.
pub(crate) proof fn kill_container_cpus_step_from_u(pre: KernelU, marked: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_container_target(pre, cpu_id) == container_ptr,
        kill_container_stage(pre, cpu_id) is Walk,
        pre.container_map[container_ptr].children.len() == 0,
        pre.container_map[container_ptr].owned_processes.is_empty(),
        marked == (KernelU {
            container_map: pre.container_map.insert(container_ptr, ContainerU { cpu_set_lock: LockStateU::WriteLocked, cpu_set_killed: true, ..pre.container_map[container_ptr] }), ..pre
        }),
        post == (KernelU {
            thread_map: marked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_container_progress(container_ptr, ContainerKillStage::Cpus), ..marked.thread_map[thread_ptr] }),
            ..marked
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_container_cpus_step); }

/// Moving the unlocked Idle or Off cpu `moved` of the marked target `container_ptr` to the killer's container
/// `owner_ptr` and dropping the target's offline request for it is a middle step of the container kill.
pub(crate) proof fn kill_container_move_cpu_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, moved: CpuId)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_container_target(pre, cpu_id) == container_ptr,
        kill_container_stage(pre, cpu_id) is Cpus,
        pre.cpu_array[cpu_id as int].owning_container == owner_ptr,
        owner_ptr != container_ptr,
        index_valid(NUM_CPUS, moved),
        pre.cpu_array[moved as int].owning_container == container_ptr,
        pre.cpu_array[moved as int].state is Idle || pre.cpu_array[moved as int].state is Off,
        pre.cpu_array[moved as int].lock_state is Unlocked,
        ({
            let target = pre.container_map[container_ptr];
            &&& pre.cpu_array.len() == NUM_CPUS
            &&& target.cpu_offline_requests.len() == NUM_CPUS
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(moved as int, CpuU { owning_container: owner_ptr, ..pre.cpu_array[moved as int] }),
                container_map: pre.container_map.insert(container_ptr, ContainerU { cpu_offline_requests: target.cpu_offline_requests.update(moved as int, false), ..target }),
                ..pre
            })
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    let target = pre.container_map[container_ptr];
    let moved_set = Set::range(0usize, NUM_CPUS).filter(|i: CpuId| pre.cpu_array[i as int] != post.cpu_array[i as int]);
    assert(moved_set =~= set![moved]);
    assert(moved_set.len() == 1);
    assert_seqs_equal!(target.cpu_offline_requests.update(moved as int, false) == Seq::new(NUM_CPUS as nat, |i: int| target.cpu_offline_requests[i] && !moved_set.contains(i as CpuId)));
    reveal(kill_container_move_cpu_step);
}

/// The marked target `container_ptr` owning no cpu moving the kill on to its free pages is a middle step of the
/// container kill.
pub(crate) proof fn kill_container_pages_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_container_target(pre, cpu_id) == container_ptr,
        kill_container_stage(pre, cpu_id) is Cpus,
        forall|i: int| #![trigger pre.cpu_array[i]] 0 <= i < NUM_CPUS ==> pre.cpu_array[i].owning_container != container_ptr,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_container_progress(container_ptr, ContainerKillStage::Pages), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_container_pages_step); }
} // verus!

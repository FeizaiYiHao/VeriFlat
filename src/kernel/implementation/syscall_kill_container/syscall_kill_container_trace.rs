use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_walk_spec::{KillScope, kill_scope_progress};

verus! {
/// The killer's write-held cpu container and the marked container `ctn_ptr` below it on `krnl`, and the empty
/// zombie root `target` of `ctn_ptr`, which has no parent and owns no PCI function, are so on the projection.
pub(crate) proof fn kill_container_retire_root_pre_from_k(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, target: RwLockProcessPtr)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.container_lock_map(), krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container, TypedLockMode::Write),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        krnl.ctn_mp.spec_index(ctn_ptr).being_killed(),
        krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view().children.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        krnl.prc_mp.spec_index(target).view().zombie,
        krnl.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        krnl.prc_mp.spec_index(target).view_rodata().view().parent is None,
        krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let owner = u.cpu_array[cpu_id as int].owning_container;
            let process = u.process_map[target];
            &&& u.container_map.dom().contains(owner)
            &&& u.container_map[owner].lock_state is WriteLocked
            &&& u.container_map.dom().contains(ctn_ptr)
            &&& u.container_map[ctn_ptr].killed
            &&& u.container_map[ctn_ptr].uppertree_seq.contains(owner)
            &&& process.children.len() == 0
            &&& process.owned_threads.len() == 0
            &&& process.zombie
            &&& process.owned_pci_functions.is_empty()
            &&& process.parent is None
            &&& process.owning_container == ctn_ptr
        }),
{
    let owner = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    kernel_cpu_projection_at(krnl, cpu_id); krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), owner);
    kernel_container_projection_at(krnl, owner); kernel_container_projection_at(krnl, ctn_ptr); kernel_process_projection_at(krnl, target);
}

/// Retiring the empty zombie root `target` of the marked container `ctn_ptr`, which raises the container's 4K
/// quota to `quota`, and walking the container again is a middle step of the container kill.
pub(crate) proof fn kill_container_retire_root_step_from_u(
    pre: KernelU, retired: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, target: RwLockProcessPtr, quota: usize,
)
    requires
        kill_process_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thrd_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == kill_scope_progress(KillScope::Container { container: ctn_ptr }, target, KillStage::Retire),
        ({
            let owner_ptr = pre.cpu_array[cpu_id as int].owning_container;
            &&& pre.container_map.dom().contains(owner_ptr)
            &&& pre.container_map[owner_ptr].lock_state is WriteLocked
            &&& pre.container_map[ctn_ptr].killed
            &&& pre.container_map[ctn_ptr].uppertree_seq.contains(owner_ptr)
        }),
        pre.process_map[target].children.len() == 0,
        pre.process_map[target].owned_threads.len() == 0,
        pre.process_map[target].zombie,
        pre.process_map[target].owned_pci_functions.is_empty(),
        pre.process_map[target].parent is None,
        pre.process_map[target].owning_container == ctn_ptr,
        pre.container_map[ctn_ptr].quota_4k < quota,
        ({
            let container = pre.container_map[ctn_ptr];
            retired == (KernelU {
                container_map: pre.container_map.insert(ctn_ptr, ContainerU { zombie: false, owned_processes: container.owned_processes.remove(target), quota_4k: quota, ..container }),
                process_map: pre.process_map.remove(target),
                ..pre
            })
        }),
        post == (KernelU {
            thread_map: retired.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: kill_container_progress(ctn_ptr, ContainerKillStage::Walk), ..retired.thread_map[thrd_ptr] }),
            ..retired
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_process_step_pre); reveal(kill_container_step_pre); reveal(kill_container_retire_root_step); }

/// A container kill step pushed after the partial trace of the container kill that starts at `start` extends it.
pub(crate) proof fn kill_container_trace_push(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId, ctx: KillTraceCtx)
    requires
        ctx is Container,
        0 <= start <= before.len(),
        kill_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id, ctx),
        steps.view() == before.push(KernelStep { old_u: step_pre, new_u: step_post }),
        kill_container_middle_step(KernelStep { old_u: step_pre, new_u: step_post }, cpu_id),
    ensures kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
{
    reveal(kill_partial_trace); reveal(kill_container_partial_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: step_pre, new_u: step_post }));
}
} // verus!

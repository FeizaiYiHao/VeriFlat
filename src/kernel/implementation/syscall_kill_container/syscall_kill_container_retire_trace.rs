use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::kill_killer;

verus! {
/// The killer on `cpu_id` write-holding its cpu, its cpu's container, its process `process_ptr`, itself `thread_ptr`,
/// and the marked container `container_ptr` below its cpu's container it retires, which has a parent and owns no child
/// and no process, satisfies the container kill's step precondition on `krnl` with that container retiring.
pub(crate) proof fn kill_container_retire_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
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
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container != container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Retire),
        krnl.ctn_mp.spec_index(container_ptr).being_killed(),
        krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        krnl.ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
        krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().parent is Some,
        krnl.ctn_mp.dom().contains(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().parent->Some_0),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let target = u.container_map[container_ptr];
            &&& kill_container_step_pre(u, cpu_id)
            &&& kill_killer(u, cpu_id) == thread_ptr
            &&& kill_container_target(u, cpu_id) == container_ptr
            &&& kill_container_stage(u, cpu_id) is Retire
            &&& u.cpu_array[cpu_id as int].owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
            &&& target.children.len() == 0
            &&& target.owned_processes.is_empty()
            &&& target.parent == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().parent
            &&& u.container_map.dom().contains(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().parent->Some_0)
        }),
{
    let owner = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, cpu_id);
    krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), owner); krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr);
    kernel_container_projection_at(krnl, owner); kernel_container_projection_at(krnl, container_ptr); kernel_u_domains_projection(krnl);
    reveal(kill_container_step_pre);
}

/// Retiring the empty marked container `container_ptr` with parent `parent_ptr`, which gives its pages to the killer's
/// container and raises that container's 4K and 2M quota to `quota_4k` and `quota_2m`, and walking the parent again
/// is a middle step of the container kill.
pub(crate) proof fn kill_container_retire_step_from_u(
    pre: KernelU, retired: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr,
    owner_ptr: RwLockContainerPtr, quota_4k: usize, quota_2m: usize,
)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_container_target(pre, cpu_id) == container_ptr,
        kill_container_stage(pre, cpu_id) is Retire,
        pre.cpu_array[cpu_id as int].owning_container == owner_ptr,
        owner_ptr != container_ptr,
        pre.container_map[container_ptr].children.len() == 0,
        pre.container_map[container_ptr].owned_processes.is_empty(),
        pre.container_map[container_ptr].parent == Some(parent_ptr),
        pre.container_map.dom().contains(parent_ptr),
        pre.container_map[owner_ptr].quota_4k < quota_4k,
        pre.container_map[owner_ptr].quota_2m < quota_2m,
        ({
            let target = pre.container_map[container_ptr];
            retired == (KernelU {
                container_map: Map::new(pre.container_map.dom().remove(container_ptr), |c: RwLockContainerPtr| {
                    let container = pre.container_map[c];
                    ContainerU {
                        children: if c == parent_ptr { container.children.remove_value(container_ptr) } else { container.children },
                        subtree_set: if target.uppertree_seq.contains(c) { container.subtree_set.remove(container_ptr) } else { container.subtree_set },
                        owned_pages: if c == owner_ptr { container.owned_pages.union(target.owned_pages) } else { container.owned_pages },
                        quota_4k: if c == owner_ptr { quota_4k } else { container.quota_4k },
                        quota_2m: if c == owner_ptr { quota_2m } else { container.quota_2m },
                        ..container
                    }
                }),
                ..pre
            })
        }),
        post == (KernelU {
            thread_map: retired.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_container_progress(parent_ptr, ContainerKillStage::Walk), ..retired.thread_map[thread_ptr] }),
            ..retired
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    assert(post.container_map[owner_ptr].quota_4k == quota_4k && post.container_map[owner_ptr].quota_2m == quota_2m) by { reveal(kill_container_step_pre); };
    reveal(kill_container_retire_step);
}
} // verus!

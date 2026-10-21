use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::kill_killer;

verus! {
/// The killer on `cpu_id` write-holding its cpu, its cpu's container, its process `process_ptr`, itself `thread_ptr`,
/// and the marked container `container_ptr` below its cpu's container whose free pages it moves satisfies the container
/// kill's step precondition on `krnl` with that container at its pages.
pub(crate) proof fn kill_container_pages_pre_from_k(
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
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
        krnl.ctn_mp.spec_index(container_ptr).being_killed(),
        krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& kill_container_step_pre(u, cpu_id)
            &&& kill_killer(u, cpu_id) == thread_ptr
            &&& kill_container_target(u, cpu_id) == container_ptr
            &&& kill_container_stage(u, cpu_id) is Pages
            &&& u.cpu_array[cpu_id as int].owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
        }),
{
    let owner = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, cpu_id);
    krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), owner); krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr);
    kernel_container_projection_at(krnl, owner); kernel_container_projection_at(krnl, container_ptr); kernel_u_domains_projection(krnl);
    reveal(kill_container_step_pre);
}

/// Moving one free page of `size`, which spans the pages `moved` of the marked container `container_ptr`, together with
/// one page of `size` of quota to the killer's container `owner_ptr` is a middle step of the container kill.
pub(crate) proof fn kill_container_move_page_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, moved: Set<PagePtr>, size: PageSize,
)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_container_target(pre, cpu_id) == container_ptr,
        kill_container_stage(pre, cpu_id) is Pages,
        pre.cpu_array[cpu_id as int].owning_container == owner_ptr,
        owner_ptr != container_ptr,
        moved.subset_of(pre.container_map[container_ptr].owned_pages),
        moved.len() == match size { PageSize::SZ4k => 1nat, PageSize::SZ2m => 512nat, PageSize::SZ1g => 512 * 512nat },
        ({
            let target = pre.container_map[container_ptr];
            let owner = pre.container_map[owner_ptr];
            &&& 0 < match size { PageSize::SZ4k => target.quota_4k, PageSize::SZ2m => target.quota_2m, PageSize::SZ1g => target.quota_1g }
            &&& post == (KernelU {
                container_map: pre.container_map.insert(container_ptr, match size {
                    PageSize::SZ4k => ContainerU { owned_pages: target.owned_pages.difference(moved), quota_4k: (target.quota_4k - 1) as usize, ..target },
                    PageSize::SZ2m => ContainerU { owned_pages: target.owned_pages.difference(moved), quota_2m: (target.quota_2m - 1) as usize, ..target },
                    PageSize::SZ1g => ContainerU { owned_pages: target.owned_pages.difference(moved), quota_1g: (target.quota_1g - 1) as usize, ..target },
                }).insert(owner_ptr, match size {
                    PageSize::SZ4k => ContainerU { owned_pages: owner.owned_pages.union(moved), quota_4k: (owner.quota_4k + 1) as usize, ..owner },
                    PageSize::SZ2m => ContainerU { owned_pages: owner.owned_pages.union(moved), quota_2m: (owner.quota_2m + 1) as usize, ..owner },
                    PageSize::SZ1g => ContainerU { owned_pages: owner.owned_pages.union(moved), quota_1g: (owner.quota_1g + 1) as usize, ..owner },
                }),
                ..pre
            })
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    let owned = pre.container_map[container_ptr].owned_pages;
    assert(post.container_map[container_ptr].owned_pages == owned.difference(moved) && owned.difference(owned.difference(moved)) =~= moved) by { reveal(kill_container_step_pre); };
    reveal(kill_container_move_page_step);
}

/// The marked container `container_ptr` without quota of any size starting to retire is a middle step of the container
/// kill.
pub(crate) proof fn kill_container_retire_stage_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr)
    requires
        kill_container_step_pre(pre, cpu_id),
        kill_killer(pre, cpu_id) == thread_ptr,
        kill_container_target(pre, cpu_id) == container_ptr,
        kill_container_stage(pre, cpu_id) is Pages,
        pre.container_map[container_ptr].quota_4k == 0,
        pre.container_map[container_ptr].quota_2m == 0,
        pre.container_map[container_ptr].quota_1g == 0,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: kill_container_progress(container_ptr, ContainerKillStage::Retire), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures kill_container_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(kill_container_retire_stage_step); }
} // verus!

use vstd::prelude::*;
use crate::*;

verus! {
/// Sharing a leaf advances share progress to the next page of the recorded ranges.
pub open spec fn share_4k_progress_after_leaf(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Share4k { source_range, target_range, shared, origin }) => Some(SyscallProgress::Share4k { source_range, target_range, shared: (shared + 1) as usize, origin }),
        _ => progress,
    }
}

/// `progress_thread` records a share and the write-locked quota thread has quota for one directory page.
#[verifier::opaque]
pub open spec fn share_4k_directory_pre_at(old_u: KernelU, progress_thread: RwLockThreadPtr, quota_thread: RwLockThreadPtr) -> bool {
    &&& old_u.thread_map.dom().contains(progress_thread)
    &&& old_u.thread_map[progress_thread].syscall_progress is Some
    &&& old_u.thread_map[progress_thread].syscall_progress->Some_0 is Share4k
    &&& old_u.thread_map.dom().contains(quota_thread)
    &&& old_u.thread_map[quota_thread].lock_state is WriteLocked
    &&& old_u.thread_map[quota_thread].quota_4k > 0
}

/// Allocating one target directory consumes one quota-thread quota; a child container may receive its backing page.
#[verifier::opaque]
pub open spec fn share_4k_directory_at(
    pre: KernelU, post: KernelU, quota_thread: RwLockThreadPtr, target: RwLockContainerPtr, source: Option<RwLockContainerPtr>,
) -> bool {
    let containers = match source {
        None => pre.container_map,
        Some(parent) => pre.container_map.insert(parent, ContainerU { owned_pages: post.container_map[parent].owned_pages, ..pre.container_map[parent] })
            .insert(target, ContainerU { owned_pages: post.container_map[target].owned_pages, ..pre.container_map[target] }),
    };
    &&& source matches Some(parent) ==> {
        let moved = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
        &&& parent != target
        &&& pre.container_map.dom().contains(parent)
        &&& pre.container_map.dom().contains(target)
        &&& moved.len() == 1
        &&& post.container_map[parent].owned_pages.subset_of(pre.container_map[parent].owned_pages)
        &&& post.container_map[target].owned_pages == pre.container_map[target].owned_pages.union(moved)
    }
    &&& post == (KernelU {
        thread_map: pre.thread_map.insert(quota_thread, ThreadU { quota_4k: (pre.thread_map[quota_thread].quota_4k - 1) as usize, ..pre.thread_map[quota_thread] }),
        container_map: containers,
        ..pre
    })
}

/// The next recorded source page of `progress_thread`'s share is mapped and the next recorded target
/// address is free while both page tables are write-locked.
#[verifier::opaque]
pub open spec fn share_4k_leaf_pre_at(old_u: KernelU, progress_thread: RwLockThreadPtr, source: RwLockProcessPtr, target: RwLockProcessPtr) -> bool {
    let progress = old_u.thread_map[progress_thread].syscall_progress->Some_0;
    let shared = progress->Share4k_shared;
    let source_table = old_u.process_map[source].pagetable->Some_0;
    let target_table = old_u.process_map[target].pagetable->Some_0;
    &&& old_u.thread_map.dom().contains(progress_thread)
    &&& old_u.thread_map[progress_thread].syscall_progress is Some
    &&& progress is Share4k
    &&& shared < progress->Share4k_source_range.len
    &&& shared < progress->Share4k_target_range.len
    &&& source != target
    &&& old_u.process_map.dom().contains(source)
    &&& old_u.process_map.dom().contains(target)
    &&& old_u.process_map[source].pagetable is Some
    &&& old_u.process_map[target].pagetable is Some
    &&& source_table.lock_state is WriteLocked
    &&& target_table.lock_state is WriteLocked
    &&& source_table.mapping_4k.dom().contains(progress->Share4k_source_range.view()[shared as int])
    &&& !target_table.mapping_4k.dom().contains(progress->Share4k_target_range.view()[shared as int])
}

/// Copying the recorded source entry into the target mapping advances share progress.
#[verifier::opaque]
pub open spec fn share_4k_leaf_at(old_u: KernelU, new_u: KernelU, progress_thread: RwLockThreadPtr, source: RwLockProcessPtr, target: RwLockProcessPtr) -> bool {
    let thread = old_u.thread_map[progress_thread];
    let progress = thread.syscall_progress->Some_0;
    let shared = progress->Share4k_shared as int;
    let process = old_u.process_map[target];
    let target_table = process.pagetable->Some_0;
    let entry = old_u.process_map[source].pagetable->Some_0.mapping_4k[progress->Share4k_source_range.view()[shared]];
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(progress_thread, ThreadU { syscall_progress: share_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
        process_map: old_u.process_map.insert(target, ProcessU {
            pagetable: Some(PageTableU { mapping_4k: target_table.mapping_4k.insert(progress->Share4k_target_range.view()[shared], entry), ..target_table }), ..process
        }),
        ..old_u
    })
}

/// A directory step runs before the next recorded page is shared, while the target page table is
/// write-locked and the quota thread can pay for one target directory page. The target process belongs
/// to the target container. With a transfer source, the target container is a child of the source and
/// both are write-locked.
#[verifier::opaque]
pub open spec fn share_4k_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let caller = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let progress = old_u.thread_map[caller].syscall_progress->Some_0;
    let objects = share_4k_objects(old_u, cpu_id);
    &&& share_4k_locked(old_u, cpu_id)
    &&& progress->Share4k_shared < progress->Share4k_source_range.len
    &&& share_4k_directory_pre_at(old_u, caller, objects.quota_thread)
    &&& old_u.process_map.dom().contains(objects.target)
    &&& old_u.process_map[objects.target].pagetable is Some
    &&& old_u.process_map[objects.target].pagetable->Some_0.lock_state is WriteLocked
    &&& old_u.process_map[objects.target].owning_container == objects.target_container
    &&& objects.transfer_source matches Some(source) ==> {
        &&& old_u.container_map.dom().contains(source)
        &&& old_u.container_map[source].lock_state is WriteLocked
        &&& old_u.container_map.dom().contains(objects.target_container)
        &&& old_u.container_map[objects.target_container].lock_state is WriteLocked
        &&& old_u.container_map[objects.target_container].parent == Some(source)
    }
}

/// Allocating one target directory consumes one quota-thread quota; a child container may receive
/// its backing page.
#[verifier::opaque]
pub open spec fn share_4k_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let objects = share_4k_objects(old_u, cpu_id);
    share_4k_directory_at(old_u, new_u, objects.quota_thread, objects.target_container, objects.transfer_source)
}

/// A leaf step shares the next recorded source page into the next recorded target address of a
/// process of the target container. With a transfer source, the target container is its child.
#[verifier::opaque]
pub open spec fn share_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let caller = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let objects = share_4k_objects(old_u, cpu_id);
    &&& share_4k_locked(old_u, cpu_id)
    &&& share_4k_leaf_pre_at(old_u, caller, old_u.thread_map[objects.source_thread].owning_proc, objects.target)
    &&& old_u.process_map[objects.target].owning_container == objects.target_container
    &&& objects.transfer_source matches Some(source)
        ==> old_u.container_map.dom().contains(objects.target_container) && old_u.container_map[objects.target_container].parent == Some(source)
}

/// A leaf step copies the recorded source entry into the target mapping and advances share progress.
#[verifier::opaque]
pub open spec fn share_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let caller = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let objects = share_4k_objects(old_u, cpu_id);
    share_4k_leaf_at(old_u, new_u, caller, old_u.thread_map[objects.source_thread].owning_proc, objects.target)
}

/// A step inside a share range installs one target directory page or shares one leaf.
#[verifier::opaque]
pub open spec fn share_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    ||| share_4k_directory_step_pre(step.old_u, cpu_id) && share_4k_directory_step(step.old_u, step.new_u, cpu_id)
    ||| share_4k_leaf_step_pre(step.old_u, cpu_id) && share_4k_leaf_step(step.old_u, step.new_u, cpu_id)
}
}

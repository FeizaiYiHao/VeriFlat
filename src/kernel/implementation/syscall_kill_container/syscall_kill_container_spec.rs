use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::{kill_killer, kill_target, kill_stage, kill_process_empty_target_pre, kill_process_middle_step};

verus! {
/// The result of `syscall_kill_container` from the state at entry, in the implementation's check order: a killed
/// container, process, or thread, a child index past the container's children, and a child container already being
/// killed. A kill otherwise succeeds. A cpu no longer Running or marked by a killer returns CpuIdle first.
pub open spec fn kill_container_syscall_result(pre: KernelU, cpu_id: CpuId, child_index: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let container = pre.container_map[cpu.owning_container];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if container.killed { RetValueType::ErrorContainerKilled }
    else if pre.process_map[cpu.current_process->Some_0].killed { RetValueType::ErrorProcessKilled }
    else if pre.thread_map[cpu.current_thread->Some_0].killed { RetValueType::ErrorThreadKilled }
    else if child_index >= container.children.len() { RetValueType::ErrorInvalidChild }
    else if pre.container_map[container.children[child_index as int]].killed { RetValueType::ErrorContainerKilled }
    else { RetValueType::Success }
}

/// The marked container the container kill works on.
pub open spec fn kill_container_target(u: KernelU, cpu_id: CpuId) -> RwLockContainerPtr { u.thread_map[kill_killer(u, cpu_id)].syscall_progress->Some_0->KillContainer_container }

/// Where the container kill stands at its target.
pub open spec fn kill_container_stage(u: KernelU, cpu_id: CpuId) -> ContainerKillStage { u.thread_map[kill_killer(u, cpu_id)].syscall_progress->Some_0->KillContainer_stage }

/// The killer's progress after moving to `container` at `stage`.
pub open spec fn kill_container_progress(container: RwLockContainerPtr, stage: ContainerKillStage) -> Option<SyscallProgress> {
    Some(SyscallProgress::KillContainer { container, stage })
}

/// The killer's thread with its progress replaced by the container kill at `container` in `stage`.
pub open spec fn kill_container_killer_at(u: KernelU, cpu_id: CpuId, container: RwLockContainerPtr, stage: ContainerKillStage) -> ThreadU {
    ThreadU { syscall_progress: kill_container_progress(container, stage), ..u.thread_map[kill_killer(u, cpu_id)] }
}

/// The cpu runs a live thread of a live process in a live container, the thread has no syscall in progress, and the
/// container's child at `child_index` is live. The cpu, the container, the process, and the thread are unlocked.
#[verifier::opaque]
pub open spec fn kill_container_enter_step_pre(old_u: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map[cpu.owning_container];
    let process = old_u.process_map[cpu.current_process->Some_0];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& container.lock_state is Unlocked
    &&& !container.killed
    &&& old_u.process_map.dom().contains(cpu.current_process->Some_0)
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.owning_proc == cpu.current_process->Some_0
    &&& child_index < container.children.len()
    &&& old_u.container_map.dom().contains(container.children[child_index as int])
    &&& !old_u.container_map[container.children[child_index as int]].killed
}

/// Entering write-locks the cpu, its container, the process, and the thread, marks the child container at
/// `child_index` for the kill and write-locks it, and records that the kill walks the child.
#[verifier::opaque]
pub open spec fn kill_container_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let owner_ptr = cpu.owning_container;
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    let child_ptr = old_u.container_map[owner_ptr].children[child_index as int];
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..cpu }),
        container_map: old_u.container_map.insert(owner_ptr, ContainerU { lock_state: LockStateU::WriteLocked, ..old_u.container_map[owner_ptr] })
            .insert(child_ptr, ContainerU { lock_state: LockStateU::WriteLocked, killed: true, ..old_u.container_map[child_ptr] }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..old_u.process_map[process_ptr] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            lock_state: LockStateU::WriteLocked, syscall_progress: kill_container_progress(child_ptr, ContainerKillStage::Walk), ..old_u.thread_map[thread_ptr]
        }),
        ..old_u
    })
}

/// Every container kill step after entering runs while the killer holds its cpu, its cpu's container, its process,
/// and itself, records a container kill, and holds the marked target container of the kill, which lies below its cpu's
/// container.
#[verifier::opaque]
pub open spec fn kill_container_step_pre(u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = u.cpu_array[cpu_id as int];
    let killer = u.thread_map[kill_killer(u, cpu_id)];
    let target = u.container_map[kill_container_target(u, cpu_id)];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& u.container_map.dom().contains(cpu.owning_container)
    &&& u.container_map[cpu.owning_container].lock_state is WriteLocked
    &&& u.process_map.dom().contains(cpu.current_process->Some_0)
    &&& u.process_map[cpu.current_process->Some_0].lock_state is WriteLocked
    &&& u.thread_map.dom().contains(kill_killer(u, cpu_id))
    &&& killer.lock_state is WriteLocked
    &&& killer.syscall_progress is Some
    &&& killer.syscall_progress->Some_0 is KillContainer
    &&& u.container_map.dom().contains(kill_container_target(u, cpu_id))
    &&& target.lock_state is WriteLocked
    &&& target.killed
    &&& target.uppertree_seq.contains(cpu.owning_container)
}

/// The kill descends from its target into the target's first child container, which it marks and write-locks.
#[verifier::opaque]
pub open spec fn kill_container_mark_child_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let target = old_u.container_map[kill_container_target(old_u, cpu_id)];
    let child_ptr = target.children[0];
    &&& kill_container_stage(old_u, cpu_id) is Walk
    &&& 0 < target.children.len()
    &&& old_u.container_map.dom().contains(child_ptr)
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(child_ptr, ContainerU { lock_state: LockStateU::WriteLocked, killed: true, ..old_u.container_map[child_ptr] }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_container_killer_at(old_u, cpu_id, child_ptr, ContainerKillStage::Walk)),
        ..old_u
    })
}

/// The target without child containers but with processes marks and write-locks its root process, and the kill walks
/// that process.
#[verifier::opaque]
pub open spec fn kill_container_mark_root_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let target = old_u.container_map[container_ptr];
    let root_ptr = target.root_process;
    &&& kill_container_stage(old_u, cpu_id) is Walk
    &&& target.children.len() == 0
    &&& !target.owned_processes.is_empty()
    &&& old_u.process_map.dom().contains(root_ptr)
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(root_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..old_u.process_map[root_ptr] }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id),
            kill_container_killer_at(old_u, cpu_id, container_ptr, ContainerKillStage::Process { process: root_ptr, stage: KillStage::Walk })),
        ..old_u
    })
}

/// Retiring the target's empty zombie root process removes it from the process map and from the target's processes,
/// clears the target's zombie flag, raises the target's 4K quota by an amount left open, and the kill walks the target
/// again.
#[verifier::opaque]
pub open spec fn kill_container_retire_root_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let container = old_u.container_map[container_ptr];
    let process_ptr = kill_target(old_u, cpu_id);
    let root = old_u.process_map[process_ptr];
    let quota_4k = new_u.container_map[container_ptr].quota_4k;
    &&& kill_container_stage(old_u, cpu_id) is Process
    &&& kill_stage(old_u, cpu_id) is Retire
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& kill_process_empty_target_pre(old_u, cpu_id)
    &&& root.zombie
    &&& root.owned_pci_functions.is_empty()
    &&& root.parent is None
    &&& root.owning_container == container_ptr
    &&& container.quota_4k < quota_4k
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { zombie: false, owned_processes: container.owned_processes.remove(process_ptr), quota_4k, ..container }),
        process_map: old_u.process_map.remove(process_ptr),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_container_killer_at(old_u, cpu_id, container_ptr, ContainerKillStage::Walk)),
        ..old_u
    })
}

/// The target without child containers and processes marks and write-locks its cpu set and moves on to its cpus.
#[verifier::opaque]
pub open spec fn kill_container_cpus_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let target = old_u.container_map[container_ptr];
    &&& kill_container_stage(old_u, cpu_id) is Walk
    &&& target.children.len() == 0
    &&& target.owned_processes.is_empty()
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { cpu_set_lock: LockStateU::WriteLocked, cpu_set_killed: true, ..target }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_container_killer_at(old_u, cpu_id, container_ptr, ContainerKillStage::Cpus)),
        ..old_u
    })
}

/// One unlocked Idle or Off cpu of the target moves, in the same state, to the killer's container, and the target drops
/// its offline request for that cpu.
#[verifier::opaque]
pub open spec fn kill_container_move_cpu_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let target = old_u.container_map[container_ptr];
    let owner_ptr = old_u.cpu_array[cpu_id as int].owning_container;
    let moved = Set::range(0usize, NUM_CPUS).filter(|i: CpuId| old_u.cpu_array[i as int] != new_u.cpu_array[i as int]);
    &&& kill_container_stage(old_u, cpu_id) is Cpus
    &&& new_u.cpu_array.len() == old_u.cpu_array.len()
    &&& moved.len() == 1
    &&& forall|i: CpuId| #![trigger moved.contains(i)] moved.contains(i) ==> {
        let cpu = old_u.cpu_array[i as int];
        &&& cpu.owning_container == container_ptr
        &&& cpu.state is Idle || cpu.state is Off
        &&& cpu.lock_state is Unlocked
        &&& new_u.cpu_array[i as int] == (CpuU { owning_container: owner_ptr, ..cpu })
    }
    &&& new_u == (KernelU {
        cpu_array: new_u.cpu_array,
        container_map: old_u.container_map.insert(container_ptr, ContainerU {
            cpu_offline_requests: Seq::new(NUM_CPUS as nat, |i: int| target.cpu_offline_requests[i] && !moved.contains(i as CpuId)), ..target
        }),
        ..old_u
    })
}

/// The target owning no cpu moves on to its free pages.
#[verifier::opaque]
pub open spec fn kill_container_pages_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    &&& kill_container_stage(old_u, cpu_id) is Cpus
    &&& forall|i: int| #![trigger old_u.cpu_array[i]] 0 <= i < NUM_CPUS ==> old_u.cpu_array[i].owning_container != container_ptr
    &&& new_u == (KernelU { thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_container_killer_at(old_u, cpu_id, container_ptr, ContainerKillStage::Pages)), ..old_u })
}

/// One free page of `size` moves from the target to the killer's container: the target's owned pages lose the 4K pages
/// it spans and the killer's container gains them, and one page of `size` of quota moves with it.
#[verifier::opaque]
pub open spec fn kill_container_move_page_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, size: PageSize) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let target = old_u.container_map[container_ptr];
    let owner_ptr = old_u.cpu_array[cpu_id as int].owning_container;
    let owner = old_u.container_map[owner_ptr];
    let kept = new_u.container_map[container_ptr].owned_pages;
    let moved = target.owned_pages.difference(kept);
    &&& kill_container_stage(old_u, cpu_id) is Pages
    &&& owner_ptr != container_ptr
    &&& kept.subset_of(target.owned_pages)
    &&& moved.len() == match size { PageSize::SZ4k => 1nat, PageSize::SZ2m => 512nat, PageSize::SZ1g => 512 * 512nat }
    &&& 0 < match size { PageSize::SZ4k => target.quota_4k, PageSize::SZ2m => target.quota_2m, PageSize::SZ1g => target.quota_1g }
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, match size {
            PageSize::SZ4k => ContainerU { owned_pages: kept, quota_4k: (target.quota_4k - 1) as usize, ..target },
            PageSize::SZ2m => ContainerU { owned_pages: kept, quota_2m: (target.quota_2m - 1) as usize, ..target },
            PageSize::SZ1g => ContainerU { owned_pages: kept, quota_1g: (target.quota_1g - 1) as usize, ..target },
        }).insert(owner_ptr, match size {
            PageSize::SZ4k => ContainerU { owned_pages: owner.owned_pages.union(moved), quota_4k: (owner.quota_4k + 1) as usize, ..owner },
            PageSize::SZ2m => ContainerU { owned_pages: owner.owned_pages.union(moved), quota_2m: (owner.quota_2m + 1) as usize, ..owner },
            PageSize::SZ1g => ContainerU { owned_pages: owner.owned_pages.union(moved), quota_1g: (owner.quota_1g + 1) as usize, ..owner },
        }),
        ..old_u
    })
}

/// The target without free pages left starts retiring.
#[verifier::opaque]
pub open spec fn kill_container_retire_stage_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let target = old_u.container_map[container_ptr];
    &&& kill_container_stage(old_u, cpu_id) is Pages
    &&& target.quota_4k == 0
    &&& target.quota_2m == 0
    &&& target.quota_1g == 0
    &&& new_u == (KernelU { thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_container_killer_at(old_u, cpu_id, container_ptr, ContainerKillStage::Retire)), ..old_u })
}

/// Retiring the empty target removes it from the container map, from its parent's children, and from every
/// ancestor's subtree; the killer's container takes over every page the target owns and its 4K and 2M quota rise by
/// amounts left open, and the kill walks the parent again.
#[verifier::opaque]
pub open spec fn kill_container_retire_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let container_ptr = kill_container_target(old_u, cpu_id);
    let target = old_u.container_map[container_ptr];
    let parent_ptr = target.parent->Some_0;
    let owner_ptr = old_u.cpu_array[cpu_id as int].owning_container;
    let owner = old_u.container_map[owner_ptr];
    let quota_4k = new_u.container_map[owner_ptr].quota_4k;
    let quota_2m = new_u.container_map[owner_ptr].quota_2m;
    &&& kill_container_stage(old_u, cpu_id) is Retire
    &&& target.children.len() == 0
    &&& target.owned_processes.is_empty()
    &&& target.parent is Some
    &&& old_u.container_map.dom().contains(parent_ptr)
    &&& owner_ptr != container_ptr
    &&& owner.quota_4k < quota_4k
    &&& owner.quota_2m < quota_2m
    &&& new_u == (KernelU {
        container_map: Map::new(old_u.container_map.dom().remove(container_ptr), |c: RwLockContainerPtr| {
            let container = old_u.container_map[c];
            ContainerU {
                children: if c == parent_ptr { container.children.remove_value(container_ptr) } else { container.children },
                subtree_set: if target.uppertree_seq.contains(c) { container.subtree_set.remove(container_ptr) } else { container.subtree_set },
                owned_pages: if c == owner_ptr { container.owned_pages.union(target.owned_pages) } else { container.owned_pages },
                quota_4k: if c == owner_ptr { quota_4k } else { container.quota_4k },
                quota_2m: if c == owner_ptr { quota_2m } else { container.quota_2m },
                ..container
            }
        }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_container_killer_at(old_u, cpu_id, parent_ptr, ContainerKillStage::Walk)),
        ..old_u
    })
}

/// A step between entering and finishing: a step of a process kill inside a marked container, or, for the marked
/// target container, descending into a child container, marking its root process, retiring its root process, moving
/// on to its cpus with its cpu set marked, moving one cpu, moving on to its free pages, moving one free page, starting
/// to retire it, or retiring it.
pub open spec fn kill_container_middle_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let old_u = step.old_u;
    let new_u = step.new_u;
    ||| kill_process_middle_step(step, cpu_id)
    ||| {
        &&& kill_container_step_pre(old_u, cpu_id)
        &&& {
            ||| kill_container_mark_child_step(old_u, new_u, cpu_id)
            ||| kill_container_mark_root_step(old_u, new_u, cpu_id)
            ||| kill_container_retire_root_step(old_u, new_u, cpu_id)
            ||| kill_container_cpus_step(old_u, new_u, cpu_id)
            ||| kill_container_move_cpu_step(old_u, new_u, cpu_id)
            ||| kill_container_pages_step(old_u, new_u, cpu_id)
            ||| kill_container_move_page_step(old_u, new_u, cpu_id, PageSize::SZ4k)
            ||| kill_container_move_page_step(old_u, new_u, cpu_id, PageSize::SZ2m)
            ||| kill_container_move_page_step(old_u, new_u, cpu_id, PageSize::SZ1g)
            ||| kill_container_retire_stage_step(old_u, new_u, cpu_id)
            ||| kill_container_retire_step(old_u, new_u, cpu_id)
        }
    }
}

/// Finishing runs once the kill walks the killer's own container again: the killer holds its cpu, its cpu's container,
/// its process, and itself.
#[verifier::opaque]
pub open spec fn kill_container_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.container_map[cpu.owning_container].lock_state is WriteLocked
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.process_map[process_ptr].lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
    &&& old_u.thread_map[thread_ptr].syscall_progress == kill_container_progress(cpu.owning_container, ContainerKillStage::Walk)
}

/// Finishing clears the kill's progress and unlocks the killer's thread, process, container, and cpu.
#[verifier::opaque]
pub open spec fn kill_container_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let owner_ptr = cpu.owning_container;
    let process_ptr = cpu.current_process->Some_0;
    let thread_ptr = cpu.current_thread->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..cpu }),
        container_map: old_u.container_map.insert(owner_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[owner_ptr] }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map[process_ptr] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..old_u.thread_map[thread_ptr] }),
        ..old_u
    })
}

/// The partial trace of a container kill before finishing: one enter step from `pre` followed by middle steps, each a
/// step of a process kill it runs inside a marked container or a step of its own.
#[verifier::opaque]
pub open spec fn kill_container_partial_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    &&& 1 <= trace.len()
    &&& trace[0].old_u == pre
    &&& kill_container_enter_step_pre(pre, cpu_id, child_index)
    &&& kill_container_enter_step(pre, trace[0].new_u, cpu_id, child_index)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> kill_container_middle_step(trace[j], cpu_id)
}

/// Complete trace of the call: on a kill, the enter step, the middle steps, and the finish step; a stutter otherwise.
#[verifier::opaque]
pub open spec fn kill_container_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize, killed: bool) -> bool {
    if killed {
        &&& 2 <= trace.len()
        &&& trace[0].old_u == pre
        &&& kill_container_enter_step_pre(pre, cpu_id, child_index)
        &&& kill_container_enter_step(pre, trace[0].new_u, cpu_id, child_index)
        &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> kill_container_middle_step(trace[j], cpu_id)
        &&& trace.last().new_u == post
        &&& kill_container_finish_step_pre(trace.last().old_u, cpu_id)
        &&& kill_container_finish_step(trace.last().old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

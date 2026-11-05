use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_container::syscall_kill_container_spec::kill_container_partial_trace;

verus! {
/// The result of `syscall_kill_process` from the state at entry, in the implementation's check order: a killed process
/// or thread, a child index past the process's children, and a child already being killed. A kill otherwise succeeds.
/// A cpu no longer Running or marked by a killer returns CpuIdle first.
pub open spec fn kill_process_syscall_result(pre: KernelU, cpu_id: CpuId, child_index: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let process = pre.process_map[cpu.current_process->Some_0];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if pre.thread_map[cpu.current_thread->Some_0].killed { RetValueType::ErrorThreadKilled }
    else if child_index >= process.children.len() { RetValueType::ErrorInvalidChild }
    else if pre.process_map[process.children[child_index as int]].killed { RetValueType::ErrorProcessKilled }
    else { RetValueType::Success }
}

/// The killing thread: the thread running on `cpu_id`.
pub open spec fn kill_killer(u: KernelU, cpu_id: CpuId) -> RwLockThreadPtr { u.cpu_array[cpu_id as int].current_thread->Some_0 }

/// The marked process a process kill, or a container kill inside its marked container, works on, and where it stands.
pub open spec fn kill_process_record(u: KernelU, cpu_id: CpuId) -> (RwLockProcessPtr, KillStage) {
    match u.thread_map[kill_killer(u, cpu_id)].syscall_progress->Some_0 {
        SyscallProgress::KillProcess { process, stage } => (process, stage),
        SyscallProgress::KillContainer { stage: ContainerKillStage::Process { process, stage }, .. } => (process, stage),
        _ => arbitrary(),
    }
}

/// The marked process the kill works on.
pub open spec fn kill_target(u: KernelU, cpu_id: CpuId) -> RwLockProcessPtr { kill_process_record(u, cpu_id).0 }

/// Where the kill stands at its target.
pub open spec fn kill_stage(u: KernelU, cpu_id: CpuId) -> KillStage { kill_process_record(u, cpu_id).1 }

/// The killer's progress after moving to `process` at `stage`.
pub open spec fn kill_progress(process: RwLockProcessPtr, stage: KillStage) -> Option<SyscallProgress> { Some(SyscallProgress::KillProcess { process, stage }) }

/// The killer's progress after moving to `process` at `stage`, inside the marked container a container kill records.
pub open spec fn kill_progress_at(u: KernelU, cpu_id: CpuId, process: RwLockProcessPtr, stage: KillStage) -> Option<SyscallProgress> {
    match u.thread_map[kill_killer(u, cpu_id)].syscall_progress->Some_0 {
        SyscallProgress::KillContainer { container, .. } => Some(SyscallProgress::KillContainer { container, stage: ContainerKillStage::Process { process, stage } }),
        _ => kill_progress(process, stage),
    }
}

/// The killer's thread with its progress replaced by the kill at `process` in `stage`.
pub open spec fn kill_killer_at(u: KernelU, cpu_id: CpuId, process: RwLockProcessPtr, stage: KillStage) -> ThreadU {
    ThreadU { syscall_progress: kill_progress_at(u, cpu_id, process, stage), ..u.thread_map[kill_killer(u, cpu_id)] }
}

/// The live cpu runs a live thread of a live process that has no syscall in progress, and the process's child at
/// `child_index` is live. The cpu, the process, and the thread are unlocked.
#[verifier::opaque]
pub open spec fn kill_process_enter_step_pre(old_u: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map[cpu.current_process->Some_0];
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& old_u.thread_map[cpu.current_thread->Some_0].lock_state is Unlocked
    &&& child_index < process.children.len()
    &&& old_u.process_map.dom().contains(process.children[child_index as int])
    &&& !old_u.process_map[process.children[child_index as int]].killed
}

/// Entering write-locks the cpu, which enters its kernel step, the process, and the thread, marks the child at
/// `child_index` for the kill and write-locks it, and records that the kill walks the child.
#[verifier::opaque]
pub open spec fn kill_process_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    let child_ptr = old_u.process_map[prc_ptr].children[child_index as int];
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..old_u.process_map[prc_ptr] }) .insert(child_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, killed: true, ..old_u.process_map[child_ptr] }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: kill_progress(child_ptr, KillStage::Walk), ..old_u.thread_map[thrd_ptr]
        }),
        ..old_u
    })
}

/// Every step after entering runs while the killer holds its cpu, its process, and itself, records a process kill or a
/// container kill working on a process, and holds the marked target of the kill; inside a container kill it also holds
/// the container the kill records. The target lies in the killer's cpu's container or in a container below it.
#[verifier::opaque]
pub open spec fn kill_process_step_pre(u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = u.cpu_array[cpu_id as int];
    let killer = u.thread_map[kill_killer(u, cpu_id)];
    let progress = killer.syscall_progress->Some_0;
    let target = u.process_map[kill_target(u, cpu_id)];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& u.process_map.dom().contains(cpu.current_process->Some_0)
    &&& u.process_map[cpu.current_process->Some_0].lock_state is WriteLocked
    &&& u.thread_map.dom().contains(kill_killer(u, cpu_id))
    &&& killer.lock_state is WriteLocked
    &&& killer.syscall_progress is Some
    &&& progress is KillProcess || (progress is KillContainer && progress->KillContainer_stage is Process)
    &&& u.process_map.dom().contains(kill_target(u, cpu_id))
    &&& target.lock_state is WriteLocked
    &&& target.killed
    &&& target.owning_container == cpu.owning_container || u.container_map[target.owning_container].uppertree_seq.contains(cpu.owning_container)
    &&& progress is KillContainer ==> u.container_map.dom().contains(progress->KillContainer_container)
    &&& progress is KillContainer ==> u.container_map[progress->KillContainer_container].lock_state is WriteLocked
}

/// The kill descends from its target into the target's first child, which it marks and write-locks.
#[verifier::opaque]
pub open spec fn kill_process_mark_child_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    let child_ptr = target.children[0];
    &&& kill_stage(old_u, cpu_id) is Walk
    &&& 0 < target.children.len()
    &&& old_u.process_map.dom().contains(child_ptr)
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(child_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, killed: true, ..old_u.process_map[child_ptr] }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, child_ptr, KillStage::Walk)),
        ..old_u
    })
}

/// The target without children works on its first thread.
pub open spec fn kill_process_target_has_thread(old_u: KernelU, cpu_id: CpuId) -> bool {
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    &&& kill_stage(old_u, cpu_id) is Walk
    &&& target.children.len() == 0
    &&& 0 < target.owned_threads.len()
    &&& old_u.thread_map.dom().contains(target.owned_threads[0])
}

/// `target` with its thread `victim_ptr` removed and the quota of `victim` absorbed.
pub open spec fn kill_process_absorb_thread(target: ProcessU, victim_ptr: RwLockThreadPtr, victim: ThreadU) -> ProcessU {
    ProcessU {
        owned_threads: target.owned_threads.remove_value(victim_ptr), quota_4k: (target.quota_4k + victim.quota_4k) as usize,
        quota_2m: (target.quota_2m + victim.quota_2m) as usize, quota_1g: (target.quota_1g + victim.quota_1g) as usize, ..target
    }
}

/// The target's first thread, waiting for a reply, leaves the target as an unlocked dangling thread: the target absorbs its quota,
/// and the dangling thread keeps its descriptors, its caller, and its callee.
#[verifier::opaque]
pub open spec fn kill_process_dangling_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let victim_ptr = target.owned_threads[0];
    let victim = old_u.thread_map[victim_ptr];
    &&& kill_process_target_has_thread(old_u, cpu_id)
    &&& victim.state is WAITING_REPLY
    &&& victim.lock_state is Unlocked
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, kill_process_absorb_thread(target, victim_ptr, victim)),
        thread_map: old_u.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::DANGLING, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..victim }),
        ..old_u
    })
}

/// The target's first thread, not waiting for a reply, is marked for the kill and write-locked, and the kill records
/// it.
#[verifier::opaque]
pub open spec fn kill_process_mark_thread_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let victim_ptr = old_u.process_map[prc_ptr].owned_threads[0];
    let victim = old_u.thread_map[victim_ptr];
    &&& kill_process_target_has_thread(old_u, cpu_id)
    &&& !victim.state.is_reply_waiting()
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(victim_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, killed: true, ..victim }) .insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, prc_ptr, KillStage::Thread { thread: victim_ptr })),
        ..old_u
    })
}

/// The kill records a marked victim of its target that it write-holds.
pub open spec fn kill_process_victim_marked(old_u: KernelU, cpu_id: CpuId) -> bool {
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    &&& kill_stage(old_u, cpu_id) is Thread
    &&& old_u.thread_map.dom().contains(victim_ptr)
    &&& old_u.thread_map[victim_ptr].lock_state is WriteLocked
    &&& old_u.thread_map[victim_ptr].killed
    &&& old_u.process_map[kill_target(old_u, cpu_id)].owned_threads.contains(victim_ptr)
}

/// The marked victim scheduled on a shard leaves the shard and becomes killed.
#[verifier::opaque]
pub open spec fn kill_process_dequeue_scheduled_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    let victim = old_u.thread_map[victim_ptr];
    let shard = victim.state->SCHEDULED_cpu_id;
    let container = old_u.container_map[victim.owning_container];
    &&& kill_process_victim_marked(old_u, cpu_id)
    &&& victim.state is SCHEDULED
    &&& old_u.container_map.dom().contains(victim.owning_container)
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(victim.owning_container, ContainerU {
            scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(victim_ptr)), ..container
        }),
        thread_map: old_u.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..victim }),
        ..old_u
    })
}

/// The marked victim waiting in an endpoint's queue leaves the queue and becomes killed.
#[verifier::opaque]
pub open spec fn kill_process_dequeue_endpoint_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    let victim = old_u.thread_map[victim_ptr];
    let ep_ptr = victim.blocking_endpoint_ptr->Some_0;
    let endpoint = old_u.endpoint_map[ep_ptr];
    &&& kill_process_victim_marked(old_u, cpu_id)
    &&& victim.state.is_endpoint_waiting()
    &&& victim.blocking_endpoint_ptr is Some
    &&& old_u.endpoint_map.dom().contains(ep_ptr)
    &&& new_u == (KernelU {
        endpoint_map: old_u.endpoint_map.insert(ep_ptr, EndpointU { queue: endpoint.queue.remove_value(victim_ptr), ..endpoint }),
        thread_map: old_u.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..victim }),
        ..old_u
    })
}

/// Another cpu running the marked victim is forced from running to idle without a process or thread, and the victim
/// becomes killed.
#[verifier::opaque]
pub open spec fn kill_process_cpu_to_idle_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    let victim = old_u.thread_map[victim_ptr];
    let remote = victim.state->RUNNING_cpu_id;
    &&& kill_process_victim_marked(old_u, cpu_id)
    &&& victim.state is RUNNING
    &&& index_valid(NUM_CPUS, remote)
    &&& remote != cpu_id
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..old_u.cpu_array[remote as int] }),
        thread_map: old_u.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, ..victim }),
        ..old_u
    })
}

/// The killed victim leaves the target, which absorbs its quota, and the kill walks the target again.
#[verifier::opaque]
pub open spec fn kill_process_unlink_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    let victim = old_u.thread_map[victim_ptr];
    &&& kill_process_victim_marked(old_u, cpu_id)
    &&& victim.state is KILLED
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, kill_process_absorb_thread(target, victim_ptr, victim)),
        thread_map: old_u.thread_map.insert(victim_ptr, ThreadU { state: ThreadState::KILLED, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..victim }) .insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, prc_ptr, KillStage::Walk)),
        ..old_u
    })
}

/// The target has neither children nor threads.
pub open spec fn kill_process_target_empty(old_u: KernelU, cpu_id: CpuId) -> bool {
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    &&& target.children.len() == 0
    &&& target.owned_threads.len() == 0
}

/// `prc_ptr` owns the PCI function at `bus`/`device`/`function` of `table`, so the kill reassigns it.
pub open spec fn kill_process_reassigns(table: IommuRootTableU, prc_ptr: RwLockProcessPtr, bus: int, device: int, function: int) -> bool {
    table.owners[bus][device][function] == prc_ptr
}

/// The empty target hands every PCI function it owns, detached, to the killer's process; its IOMMU table, if any, loses its
/// DID, and the only IOTLB domain that changes is the emptied candidate domain of an attached function the target owned.
#[verifier::opaque]
pub open spec fn kill_process_reassign_functions_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let owner = old_u.cpu_array[cpu_id as int].current_process->Some_0;
    let table = old_u.iommu_root_table;
    let target = old_u.process_map[prc_ptr];
    &&& kill_stage(old_u, cpu_id) is Walk
    &&& kill_process_target_empty(old_u, cpu_id)
    &&& forall|bus: usize, device: usize, function: usize| #![trigger new_u.iommu_root_table.owners[bus as int][device as int][function as int]]
        #![trigger new_u.iommu_root_table.attached[bus as int][device as int][function as int]] pci_bdf_valid(bus, device, function) ==> {
        let reassigned = kill_process_reassigns(table, prc_ptr, bus as int, device as int, function as int);
        &&& new_u.iommu_root_table.owners[bus as int][device as int][function as int] == if reassigned { owner } else { table.owners[bus as int][device as int][function as int] }
        &&& new_u.iommu_root_table.attached[bus as int][device as int][function as int] == (table.attached[bus as int][device as int][function as int] && !reassigned)
    }
    &&& new_u.iommu_tlb.dom() == old_u.iommu_tlb.dom()
    &&& forall|did: VtdDomainId| #![trigger new_u.iommu_tlb[did]] new_u.iommu_tlb[did] != old_u.iommu_tlb[did] ==> {
        let anchor = pci_bdf_of_did(did);
        &&& pci_bdf_valid(anchor.0, anchor.1, anchor.2)
        &&& kill_process_reassigns(table, prc_ptr, anchor.0 as int, anchor.1 as int, anchor.2 as int)
        &&& table.attached[anchor.0 as int][anchor.1 as int][anchor.2 as int]
        &&& new_u.iommu_tlb[did].is_empty()
    }
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU {
            owned_pci_functions: Set::empty(), iommu_table: match target.iommu_table { Some(t) => Some(PageTableU { did: None, ..t }), None => None }, ..target
        }).insert(owner, ProcessU { owned_pci_functions: old_u.process_map[owner].owned_pci_functions.union(target.owned_pci_functions), ..old_u.process_map[owner] }),
        iommu_root_table: new_u.iommu_root_table,
        iommu_tlb: new_u.iommu_tlb,
        ..old_u
    })
}

/// The empty live target owning no PCI function write-locks its page table and IOMMU table to reclaim them.
#[verifier::opaque]
pub open spec fn kill_process_lock_table_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    &&& kill_stage(old_u, cpu_id) is Walk
    &&& kill_process_target_empty(old_u, cpu_id)
    &&& !target.zombie
    &&& target.owned_pci_functions.is_empty()
    &&& target.pagetable is Some
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..target.pagetable->Some_0 }),
            iommu_table: match target.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..t }), None => None },
            ..target
        }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, prc_ptr, KillStage::Reclaim { flushed: false })),
        ..old_u
    })
}

/// The target's page table, and its IOMMU table if any, are write-locked while the kill reclaims it at `stage`.
pub open spec fn kill_process_reclaim_step_pre(old_u: KernelU, cpu_id: CpuId, stage: KillStage) -> bool {
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    &&& kill_stage(old_u, cpu_id) == stage
    &&& target.pagetable is Some
    &&& target.pagetable->Some_0.lock_state is WriteLocked
    &&& target.iommu_table is Some ==> target.iommu_table->Some_0.lock_state is WriteLocked
}

/// Hiding a root entry of the target's write-locked page table before the flush drops from that table every 4K, 2M and 1G
/// mapping and every window lock under one root entry chosen by the kernel and keeps everything else.
#[verifier::opaque]
pub open spec fn kill_process_table_hidden_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    &&& kill_process_reclaim_step_pre(old_u, cpu_id, KillStage::Reclaim { flushed: false })
    &&& process_table_hidden_step(old_u, new_u, kill_target(old_u, cpu_id))
}

/// The flush runs once the hidden root entries left the target's page table without a user 4K mapping, a 2M or 1G
/// mapping, or a window lock, and before it is recorded.
pub open spec fn kill_process_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let pagetable = old_u.process_map[kill_target(old_u, cpu_id)].pagetable->Some_0;
    &&& kill_process_reclaim_step_pre(old_u, cpu_id, KillStage::Reclaim { flushed: false })
    &&& process_user_4k_unmapped(old_u, pagetable)
    &&& pagetable.mapping_2m.dom() == Set::<VAddr>::empty()
    &&& pagetable.mapping_1g.dom() == Set::<VAddr>::empty()
    &&& pagetable.pagetable_window_locks.dom() == Set::<WindowVa>::empty()
}

/// Recording the flush changes only the kill's stage.
#[verifier::opaque]
pub open spec fn kill_process_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, kill_target(old_u, cpu_id), KillStage::Reclaim { flushed: true })),
        ..old_u
    })
}

/// An IOMMU leaf step removes exactly one 4K mapping from the target's write-locked IOMMU table and keeps every other
/// entry; the kernel chooses the IOVA.
#[verifier::opaque]
pub open spec fn kill_process_iommu_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let iommu_table = target.iommu_table->Some_0;
    let kept = new_u.process_map[prc_ptr].iommu_table->Some_0.mapping_4k.dom();
    let removed = iommu_table.mapping_4k.dom().difference(kept);
    &&& kill_process_reclaim_step_pre(old_u, cpu_id, KillStage::Reclaim { flushed: true })
    &&& target.iommu_table is Some
    &&& kept.subset_of(iommu_table.mapping_4k.dom())
    &&& removed.len() == 1
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { iommu_table: Some(PageTableU { mapping_4k: iommu_table.mapping_4k.restrict(kept), ..iommu_table }), ..target }),
        ..old_u
    })
}

/// The stage after the target returns its next size of quota from `stage`: its 4K quota once the flush is recorded,
/// then its 2M quota, then its 1G quota. No quota is returned from any other stage.
pub open spec fn kill_process_quota_stage_after(stage: KillStage) -> Option<KillStage> {
    match stage {
        KillStage::Reclaim { flushed: true } => Some(KillStage::Quota { returned: PageSize::SZ4k }),
        KillStage::Quota { returned: PageSize::SZ4k } => Some(KillStage::Quota { returned: PageSize::SZ2m }),
        KillStage::Quota { returned: PageSize::SZ2m } => Some(KillStage::Quota { returned: PageSize::SZ1g }),
        _ => None,
    }
}

/// The target returns the next size of quota after the kill's stage: the target's whole quota of that size moves to its
/// container.
#[verifier::opaque]
pub open spec fn kill_process_quota_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let container = old_u.container_map[target.owning_container];
    let stage = kill_stage(old_u, cpu_id);
    let size = kill_process_quota_stage_after(stage)->Some_0->Quota_returned;
    &&& old_u.container_map.dom().contains(target.owning_container)
    &&& kill_process_quota_stage_after(stage) is Some
    &&& kill_process_reclaim_step_pre(old_u, cpu_id, stage)
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(target.owning_container, match size {
            PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + target.quota_4k) as usize, ..container },
            PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + target.quota_2m) as usize, ..container },
            PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + target.quota_1g) as usize, ..container },
        }),
        process_map: old_u.process_map.insert(prc_ptr, match size {
            PageSize::SZ4k => ProcessU { quota_4k: 0, ..target },
            PageSize::SZ2m => ProcessU { quota_2m: 0, ..target },
            PageSize::SZ1g => ProcessU { quota_1g: 0, ..target },
        }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, prc_ptr, KillStage::Quota { returned: size })),
        ..old_u
    })
}

/// Unlocking the target's reclaimed page table and IOMMU table, once every quota size is returned, the page table keeps
/// no user 4K mapping, 2M or 1G mapping, or window lock, and the IOMMU table no 4K mapping, readies the target to become
/// a zombie.
#[verifier::opaque]
pub open spec fn kill_process_unlock_table_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let pagetable = target.pagetable->Some_0;
    &&& kill_process_reclaim_step_pre(old_u, cpu_id, KillStage::Quota { returned: PageSize::SZ1g })
    &&& process_user_4k_unmapped(old_u, pagetable)
    &&& pagetable.mapping_2m.dom() == Set::<VAddr>::empty()
    &&& pagetable.mapping_1g.dom() == Set::<VAddr>::empty()
    &&& pagetable.pagetable_window_locks.dom() == Set::<WindowVa>::empty()
    &&& target.iommu_table is Some ==> process_iommu_4k_unmapped(target.iommu_table->Some_0)
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..target.pagetable->Some_0 }),
            iommu_table: match target.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
            ..target
        }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, prc_ptr, KillStage::Zombie)),
        ..old_u
    })
}

/// The reclaimed target becomes a zombie that hides its tables and releases its PCID to its container, and the kill
/// starts retiring it.
#[verifier::opaque]
pub open spec fn kill_process_zombify_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let container = old_u.container_map[target.owning_container];
    &&& kill_stage(old_u, cpu_id) is Zombie
    &&& !target.zombie
    &&& old_u.container_map.dom().contains(target.owning_container)
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(target.owning_container, ContainerU { free_pcids: container.free_pcids.insert(target.pcid), ..container }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..target }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, prc_ptr, KillStage::Retire)),
        ..old_u
    })
}

/// An empty target that was already a zombie and owns no PCI function goes straight to retiring.
#[verifier::opaque]
pub open spec fn kill_process_zombie_retire_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    &&& kill_stage(old_u, cpu_id) is Walk
    &&& kill_process_target_empty(old_u, cpu_id)
    &&& target.zombie
    &&& target.owned_pci_functions.is_empty()
    &&& new_u == (KernelU { thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, kill_target(old_u, cpu_id), KillStage::Retire)), ..old_u })
}

/// Retiring the empty zombie target removes it from the process map, from its parent's children, from every
/// ancestor's subtree, and from its container's processes, raises its container's 4K quota by an amount left open,
/// and the kill walks the parent again.
#[verifier::opaque]
pub open spec fn kill_process_retire_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let prc_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[prc_ptr];
    let parent_ptr = target.parent->Some_0;
    let container = old_u.container_map[target.owning_container];
    let quota_4k = new_u.container_map[target.owning_container].quota_4k;
    &&& kill_stage(old_u, cpu_id) is Retire
    &&& kill_process_target_empty(old_u, cpu_id)
    &&& target.zombie
    &&& target.owned_pci_functions.is_empty()
    &&& target.parent is Some
    &&& old_u.container_map.dom().contains(target.owning_container)
    &&& container.quota_4k < quota_4k
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(target.owning_container, ContainerU { owned_processes: container.owned_processes.remove(prc_ptr), quota_4k, ..container }),
        process_map: Map::new(old_u.process_map.dom().remove(prc_ptr), |p: RwLockProcessPtr| {
            let process = old_u.process_map[p];
            if target.uppertree_seq.contains(p) {
                ProcessU { children: if p == parent_ptr { process.children.remove_value(prc_ptr) } else { process.children }, subtree_set: process.subtree_set.remove(prc_ptr), ..process }
            } else { process }
        }),
        thread_map: old_u.thread_map.insert(kill_killer(old_u, cpu_id), kill_killer_at(old_u, cpu_id, parent_ptr, KillStage::Walk)),
        ..old_u
    })
}

/// A refund grows the 4K or 2M quota of the target's container or of one of its ancestors. Unlike thread_exit's refund it
/// carries no `flushed` stage and unlocks no window: the kill refunds only after every table it reclaims is unlocked.
#[verifier::opaque]
pub open spec fn kill_process_refund_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    kernel_u_container_quota_4k_increased(old_u, new_u, old_u.process_map[kill_target(old_u, cpu_id)].owning_container)
        || kernel_u_container_quota_2m_increased(old_u, new_u, old_u.process_map[kill_target(old_u, cpu_id)].owning_container)
}

/// A step between entering and finishing: descending into a child, turning a thread waiting for a reply into a dangling thread,
/// marking, dequeuing, or unlinking a thread, forcing the cpu running a thread to idle, reclaiming killed threads of the target's
/// container, and, for an empty target, reassigning its PCI functions, locking its tables, hiding one user root entry of its page
/// table, flushing one cpu's TLB for its PCID, recording the flush, removing one IOMMU 4K leaf, returning quota of freed pages to the
/// target's container chain, returning one size of its quota, unlocking its tables, making it a zombie, or retiring it.
pub open spec fn kill_process_middle_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let old_u = step.old_u;
    let new_u = step.new_u;
    &&& kill_process_step_pre(old_u, cpu_id)
    &&& {
        ||| kill_process_mark_child_step(old_u, new_u, cpu_id)
        ||| kill_process_dangling_step(old_u, new_u, cpu_id)
        ||| kill_process_mark_thread_step(old_u, new_u, cpu_id)
        ||| kill_process_dequeue_scheduled_step(old_u, new_u, cpu_id)
        ||| kill_process_dequeue_endpoint_step(old_u, new_u, cpu_id)
        ||| kill_process_cpu_to_idle_step(old_u, new_u, cpu_id)
        ||| kill_process_unlink_step(old_u, new_u, cpu_id)
        ||| killed_thread_reclaim_within_container(old_u, new_u, cpu_id, old_u.process_map[kill_target(old_u, cpu_id)].owning_container)
        ||| kill_process_reassign_functions_step(old_u, new_u, cpu_id)
        ||| kill_process_lock_table_step(old_u, new_u, cpu_id)
        ||| kill_process_table_hidden_step(old_u, new_u, cpu_id)
        ||| kill_process_flush_step_pre(old_u, cpu_id) && kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[kill_target(old_u, cpu_id)].pcid)
        ||| kill_process_flush_step_pre(old_u, cpu_id) && kill_process_flushed_step(old_u, new_u, cpu_id)
        ||| kill_process_iommu_leaf_step(old_u, new_u, cpu_id)
        ||| kill_process_refund_step(old_u, new_u, cpu_id)
        ||| kill_process_quota_step(old_u, new_u, cpu_id)
        ||| kill_process_unlock_table_step(old_u, new_u, cpu_id)
        ||| kill_process_zombify_step(old_u, new_u, cpu_id)
        ||| kill_process_zombie_retire_step(old_u, new_u, cpu_id)
        ||| kill_process_retire_step(old_u, new_u, cpu_id)
    }
}

/// Finishing runs once the kill walks the killer's own process again: the killer holds its cpu, its process, and
/// itself.
#[verifier::opaque]
pub open spec fn kill_process_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& old_u.process_map[prc_ptr].lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(thrd_ptr)
    &&& old_u.thread_map[thrd_ptr].lock_state is WriteLocked
    &&& old_u.thread_map[thrd_ptr].syscall_progress == kill_progress(prc_ptr, KillStage::Walk)
}

/// Finishing clears the kill's progress and unlocks the killer's thread, process, and cpu, which leaves its kernel step.
#[verifier::opaque]
pub open spec fn kill_process_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map[prc_ptr] }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..old_u.thread_map[thrd_ptr] }),
        ..old_u
    })
}

/// The partial trace before finishing: one enter step from `pre` followed by middle steps.
#[verifier::opaque]
pub open spec fn kill_process_partial_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    &&& 1 <= trace.len()
    &&& trace[0].old_u == pre
    &&& kill_process_enter_step_pre(pre, cpu_id, child_index)
    &&& kill_process_enter_step(pre, trace[0].new_u, cpu_id, child_index)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> kill_process_middle_step(trace[j], cpu_id)
}

/// The kill a partial trace belongs to: `syscall_kill_process` or `syscall_kill_container` of the child at
/// `child_index`.
pub ghost enum KillTraceCtx { Process { child_index: usize }, Container { child_index: usize } }

/// The partial trace before finishing of the kill `ctx`.
#[verifier::opaque]
pub open spec fn kill_partial_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, ctx: KillTraceCtx) -> bool {
    match ctx {
        KillTraceCtx::Process { child_index } => kill_process_partial_trace(trace, pre, cpu_id, child_index),
        KillTraceCtx::Container { child_index } => kill_container_partial_trace(trace, pre, cpu_id, child_index),
    }
}

/// Complete trace of the call: on a kill, the partial trace followed by the finish step; a stutter otherwise.
#[verifier::opaque]
pub open spec fn kill_process_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, child_index: usize, killed: bool) -> bool {
    if killed {
        // enter + middle steps + finish
        &&& 2 <= trace.len()
        &&& kill_process_partial_trace(trace.drop_last(), pre, cpu_id, child_index)
        &&& trace.last().new_u == post
        &&& kill_process_finish_step_pre(trace.last().old_u, cpu_id)
        &&& kill_process_finish_step(trace.last().old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

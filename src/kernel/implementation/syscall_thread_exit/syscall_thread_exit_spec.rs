use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_thread_exit` from the state at entry, in the implementation's check order: a killed
/// container, a container write-held by a live owner below the running process's depth, a killed process or thread,
/// and a killed caller waiting for the thread's reply. An exit otherwise leaves the cpu idle. A cpu no longer Running or
/// marked by a killer returns CpuIdle first.
pub open spec fn thread_exit_syscall_result(pre: KernelU, cpu_id: CpuId) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    let owner = pre.container_map[cpu.owning_container].lock_process_owner;
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if pre.container_map[cpu.owning_container].killed { RetValueType::ErrorContainerKilled }
    else if owner is Some && owner->Some_0 < LockOwnerId::Some(pre.process_map[cpu.current_process->Some_0].depth) { RetValueType::ErrorContainerLockOrderConflict }
    else if pre.process_map[cpu.current_process->Some_0].killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.caller is Some && pre.thread_map[thread.caller->Some_0].killed { RetValueType::ErrorIpcPeerKilled }
    else { RetValueType::CpuIdle }
}

/// The cpu runs a live thread of a live process inside its live container, and the thread has no syscall in progress. A
/// caller the thread serves is live and waits for its reply, or is the dangling thread of a killed caller. The cpu, the container,
/// the process, the thread, and its caller are unlocked.
#[verifier::opaque]
pub open spec fn thread_exit_enter_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let caller = old_u.thread_map.spec_index(thread.caller->Some_0);
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(ctn_ptr)
    &&& old_u.container_map.spec_index(ctn_ptr).lock_state is Unlocked
    &&& !old_u.container_map.spec_index(ctn_ptr).killed
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(prc_ptr).killed
    &&& thread.lock_state is Unlocked
    &&& thread.owning_container == ctn_ptr
    &&& thread.caller is Some ==> {
        &&& old_u.thread_map.dom().contains(thread.caller->Some_0)
        &&& caller.lock_state is Unlocked
        &&& !caller.killed
        &&& caller.state.is_reply_waiting()
    }
}

/// Entering write-locks the cpu, the container, the process, and the thread, wakes the caller the thread serves on
/// shard `cpu_id` of the caller's container with `ErrorIpcCalleeExited` or takes over the dangling thread of a killed caller as a
/// write-locked killed thread without a callee, drops the thread's caller, and records an exit that has released no
/// descriptor.
#[verifier::opaque]
pub open spec fn thread_exit_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    let locked = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
        container_map: old_u.container_map.insert(ctn_ptr, ContainerU {
            lock_state: LockStateU::WriteLocked { writer: cpu_id }, lock_process_owner: Some(LockOwnerId::Some(old_u.process_map.spec_index(prc_ptr).depth)), ..old_u.container_map.spec_index(ctn_ptr)
        }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..old_u.process_map.spec_index(prc_ptr) }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..old_u.thread_map.spec_index(thrd_ptr) }),
        ..old_u
    };
    let woken = match old_u.thread_map.spec_index(thrd_ptr).caller {
        Some(caller_ptr) => if locked.thread_map[caller_ptr].state is DANGLING {
            KernelU {
                thread_map: locked.thread_map.insert(thrd_ptr, ThreadU { caller: None, ..locked.thread_map[thrd_ptr] }).insert(caller_ptr, ThreadU {
                    state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..locked.thread_map[caller_ptr]
                }),
                ..locked
            }
        } else {
            let caller_container = locked.thread_map[caller_ptr].owning_container;
            let scheduler = locked.container_map[caller_container].scheduler;
            KernelU {
                container_map: locked.container_map.insert(caller_container, ContainerU {
                    scheduler: scheduler.update(cpu_id as int, scheduler[cpu_id as int].push(caller_ptr)), ..locked.container_map[caller_container]
                }),
                thread_map: locked.thread_map.insert(thrd_ptr, ThreadU { caller: None, ..locked.thread_map[thrd_ptr] }).insert(caller_ptr, ThreadU {
                    state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..locked.thread_map[caller_ptr]
                }),
                ..locked
            }
        },
        None => locked,
    };
    new_u == (KernelU { thread_map: woken.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExit { next: 0 }), ..woken.thread_map[thrd_ptr] }), ..woken })
}

/// Dropping a descriptor runs while the running thread records an exit and holds the cpu, its container, its process,
/// and itself.
#[verifier::opaque]
pub open spec fn thread_exit_drop_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(ctn_ptr)
    &&& old_u.container_map.spec_index(ctn_ptr).lock_state is WriteLocked
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is ThreadExit
}

/// The running thread releases its first descriptor at or after its recorded position: the descriptor is cleared, its
/// unlocked endpoint, still held elsewhere, drops the reference, and the thread records the position after it.
#[verifier::opaque]
pub open spec fn thread_exit_drop_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let next = thread.syscall_progress->Some_0->ThreadExit_next;
    let index = (new_u.thread_map.spec_index(thrd_ptr).syscall_progress->Some_0->ThreadExit_next - 1) as EndpointIdx;
    let ep_ptr = thread.endpoint_descriptors[index as int]->Some_0;
    let endpoint = old_u.endpoint_map.spec_index(ep_ptr);
    &&& next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS
    &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
    &&& thread.endpoint_descriptors[index as int] is Some
    &&& old_u.endpoint_map.dom().contains(ep_ptr)
    &&& endpoint.lock_state is Unlocked
    &&& endpoint.owning_threads.len() > 1
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            endpoint_descriptors: thread.endpoint_descriptors.update(index as int, None), syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..thread
        }),
        endpoint_map: old_u.endpoint_map.insert(ep_ptr, EndpointU { owning_threads: endpoint.owning_threads.remove((thrd_ptr, index)), ..endpoint }),
        ..old_u
    })
}

/// The running thread releases its first descriptor at or after its recorded position, which holds the last reference of
/// its unlocked endpoint: the descriptor is cleared, the endpoint is released, and the thread records the position after it.
#[verifier::opaque]
pub open spec fn thread_exit_release_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let next = thread.syscall_progress->Some_0->ThreadExit_next;
    let index = (new_u.thread_map.spec_index(thrd_ptr).syscall_progress->Some_0->ThreadExit_next - 1) as EndpointIdx;
    &&& next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS
    &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
    &&& kernel_u_endpoint_released(old_u, new_u, thrd_ptr, index as int)
    &&& new_u.thread_map == old_u.thread_map.insert(thrd_ptr, ThreadU {
        endpoint_descriptors: thread.endpoint_descriptors.update(index as int, None), syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..thread
    })
}

/// Reclaiming starts once the running thread, its process's last thread, has released every descriptor and has no
/// caller: the cpu, the container, the process, and the thread are write-locked and the process's page table and IOMMU
/// table are unlocked.
#[verifier::opaque]
pub open spec fn thread_exit_lock_table_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is ThreadExit
    &&& thread.caller is None
    &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> thread.endpoint_descriptors[j] is None
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& process.lock_state is WriteLocked
    &&& process.owned_threads.len() == 1
    &&& process.pagetable is Some
    &&& process.pagetable->Some_0.lock_state is Unlocked
    &&& process.iommu_table is Some ==> process.iommu_table->Some_0.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.container_map.spec_index(thread.owning_container).lock_state is WriteLocked
}

/// The attached flags after exit detaches every attached function that `prc_ptr` owns.
pub open spec fn thread_exit_detached_attached(table: IommuRootTableU, prc_ptr: RwLockProcessPtr) -> Seq3<bool> {
    Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| table.attached[bus][device][function] && table.owners[bus][device][function] != prc_ptr)))
}

/// Locking the process's page table starts reclaiming and the thread records that nothing is flushed yet. A process
/// with an IOMMU table write-locks it and detaches it: every attached function the process owns is detached, the
/// table drops its DID, and the IOTLB domain of that DID, if any, is emptied; owners stay.
#[verifier::opaque]
pub open spec fn thread_exit_lock_table_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let table = old_u.iommu_root_table;
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..process.pagetable->Some_0 }),
            iommu_table: match process.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, did: None, ..t }), None => None },
            ..process
        }),
        iommu_root_table: if process.iommu_table is Some { IommuRootTableU { attached: thread_exit_detached_attached(table, thread.owning_proc), ..table } } else { table },
        iommu_tlb: if process.iommu_table is Some && process.iommu_table->Some_0.did is Some {
            old_u.iommu_tlb.insert(process.iommu_table->Some_0.did->Some_0, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { old_u.iommu_tlb },
        ..old_u
    })
}

/// Reclaiming runs while the cpu, the container, the process with its page table, and the running thread are
/// write-locked and the thread records `progress`.
#[verifier::opaque]
pub open spec fn thread_exit_reclaim_step_pre(old_u: KernelU, cpu_id: CpuId, progress: SyscallProgress) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    &&& thread_pagetable_op_locked(old_u, cpu_id)
    &&& old_u.process_map.spec_index(thread.owning_proc).lock_state is WriteLocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.container_map.spec_index(thread.owning_container).lock_state is WriteLocked
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state is WriteLocked
    &&& thread.syscall_progress == Some(progress)
}

/// An IOMMU leaf step removes exactly one 4K mapping from the process's write-locked IOMMU table and keeps every other
/// entry; the kernel chooses the IOVA.
#[verifier::opaque]
pub open spec fn thread_exit_iommu_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let iommu_table = process.iommu_table->Some_0;
    let kept = new_u.process_map.spec_index(thread.owning_proc).iommu_table->Some_0.mapping_4k.dom();
    let removed = iommu_table.mapping_4k.dom().difference(kept);
    &&& process.iommu_table is Some
    &&& iommu_table.lock_state is WriteLocked
    &&& kept.subset_of(iommu_table.mapping_4k.dom())
    &&& removed.len() == 1
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { iommu_table: Some(PageTableU { mapping_4k: iommu_table.mapping_4k.restrict(kept), ..iommu_table }), ..process }),
        ..old_u
    })
}

/// The flush runs before it is recorded, once hiding every user root entry has left the process's page table without any
/// 4K, 2M or 1G mapping and without any window lock.
#[verifier::opaque]
pub open spec fn thread_exit_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let table = old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0;
    &&& thread_exit_reclaim_step_pre(old_u, cpu_id, SyscallProgress::ThreadExitReclaim { flushed: false })
    &&& table.mapping_4k == Map::<VAddr, MapEntry>::empty() && table.mapping_2m == Map::<VAddr, MapEntry>::empty() && table.mapping_1g == Map::<VAddr, MapEntry>::empty()
    &&& table.pagetable_window_locks == Map::<WindowVa, LockStateU>::empty()
}

/// A TLB flush step read-locks the cpu set of the thread's container, or keeps it read-locked, and clears at most one
/// TLB entry for the process's PCID.
#[verifier::opaque]
pub open spec fn thread_exit_tlb_flush_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let locked = KernelU {
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: old_u.container_map.spec_index(thread.owning_container).cpu_set_lock.with_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    };
    new_u == locked || kernel_u_cpu_tlb_cleared(locked, new_u, old_u.process_map.spec_index(thread.owning_proc).pcid)
}

/// Recording the flush changes the thread's progress and releases this cpu's read hold on the cpu set of the thread's
/// container.
#[verifier::opaque]
pub open spec fn thread_exit_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let ctn_ptr = old_u.thread_map.spec_index(thrd_ptr).owning_container;
    let cpu_set_lock = old_u.container_map.spec_index(ctn_ptr).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: true }), ..old_u.thread_map.spec_index(thrd_ptr) }),
        container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(ctn_ptr) }),
        ..old_u
    })
}

/// The progress a thread records after returning its next size of quota from `progress`: the 4K quota follows the
/// recorded flush, then the 2M and the 1G quota; nothing follows any other progress.
pub open spec fn thread_exit_quota_progress_after(progress: SyscallProgress) -> Option<SyscallProgress> {
    match progress {
        SyscallProgress::ThreadExitReclaim { flushed } => if flushed { Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ4k }) } else { None },
        SyscallProgress::ThreadExitQuota { returned } => match returned {
            PageSize::SZ4k => Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ2m }),
            PageSize::SZ2m => Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g }),
            PageSize::SZ1g => None,
        },
        _ => None,
    }
}

/// Returning one size of quota runs after the flush is recorded, while the reclaiming locks are held and some quota size
/// is left to return.
#[verifier::opaque]
pub open spec fn thread_exit_quota_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let progress = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0).syscall_progress->Some_0;
    &&& thread_exit_reclaim_step_pre(old_u, cpu_id, progress)
    &&& thread_exit_quota_progress_after(progress) is Some
}

/// The thread returns the next size of quota after its progress, named by its new progress: the whole quota of that size
/// of the thread and of its process moves to their container.
#[verifier::opaque]
pub open spec fn thread_exit_quota_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let container = old_u.container_map.spec_index(thread.owning_container);
    let progress = new_u.thread_map.spec_index(thrd_ptr).syscall_progress;
    let size = progress->Some_0->ThreadExitQuota_returned;
    &&& thread.syscall_progress is Some
    &&& progress is Some
    &&& progress == thread_exit_quota_progress_after(thread.syscall_progress->Some_0)
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(thread.owning_container, match size {
            PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
            PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
            PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, match size {
            PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
            PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
            PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, match size {
            PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
            PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
            PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
        }),
        ..old_u
    })
}

/// Reclaiming ends once every quota size is returned, the locked page table keeps no 4K, 2M or 1G mapping and no window
/// lock, and the locked IOMMU table keeps no 4K mapping.
#[verifier::opaque]
pub open spec fn thread_exit_unlock_table_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let table = process.pagetable->Some_0;
    &&& thread_exit_reclaim_step_pre(old_u, cpu_id, SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g })
    &&& table.mapping_4k == Map::<VAddr, MapEntry>::empty() && table.mapping_2m == Map::<VAddr, MapEntry>::empty() && table.mapping_1g == Map::<VAddr, MapEntry>::empty()
    &&& table.pagetable_window_locks == Map::<WindowVa, LockStateU>::empty()
    &&& process.iommu_table is Some ==> process_iommu_4k_unmapped(process.iommu_table->Some_0)
}

/// Unlocking the reclaimed page table and IOMMU table leaves the thread ready to make its process a zombie.
#[verifier::opaque]
pub open spec fn thread_exit_unlock_table_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitZombie), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.pagetable->Some_0 }),
            iommu_table: match process.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
            ..process
        }),
        ..old_u
    })
}

/// A refund grows the 4K or 2M quota of the running thread's container or of one of its ancestors and changes nothing else;
/// refunds happen after the flush, when the page table holds no window lock.
#[verifier::opaque]
pub open spec fn thread_exit_refund_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    kernel_u_container_quota_4k_increased(old_u, new_u, thread.owning_container) || kernel_u_container_quota_2m_increased(old_u, new_u, thread.owning_container)
}

/// A step between entering and finishing: reclaiming the dangling thread of a killed caller and the killed callers it takes over,
/// changing or removing only threads of the exiting thread's container, releasing a descriptor, releasing an endpoint with
/// its last descriptor, or, for a process's last thread, locking the process's tables, hiding one root entry of the page
/// table, flushing one cpu's TLB for the process's PCID, recording the flush, removing one IOMMU 4K leaf, refunding 4K quota
/// to the thread's container chain, returning one size of quota, or unlocking the tables.
pub open spec fn thread_exit_middle_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let old_u = step.old_u;
    let new_u = step.new_u;
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let flushed = SyscallProgress::ThreadExitReclaim { flushed: true };
    ||| thread_exit_drop_step_pre(old_u, cpu_id) && killed_thread_reclaim_within_container(old_u, new_u, cpu_id, thread.owning_container)
    ||| thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_drop_step(old_u, new_u, cpu_id)
    ||| thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_release_step(old_u, new_u, cpu_id)
    ||| thread_exit_lock_table_step_pre(old_u, cpu_id) && thread_exit_lock_table_step(old_u, new_u, cpu_id)
    ||| thread_exit_reclaim_step_pre(old_u, cpu_id, SyscallProgress::ThreadExitReclaim { flushed: false }) && process_table_hidden_step(old_u, new_u, thread.owning_proc)
    ||| thread_exit_flush_step_pre(old_u, cpu_id) && thread_exit_tlb_flush_step(old_u, new_u, cpu_id)
    ||| thread_exit_flush_step_pre(old_u, cpu_id) && thread_exit_flushed_step(old_u, new_u, cpu_id)
    ||| thread_exit_reclaim_step_pre(old_u, cpu_id, flushed) && thread_exit_iommu_leaf_step(old_u, new_u, cpu_id)
    ||| thread_exit_reclaim_step_pre(old_u, cpu_id, flushed) && thread_exit_refund_step(old_u, new_u, cpu_id)
    ||| thread_exit_quota_step_pre(old_u, cpu_id) && thread_exit_quota_step(old_u, new_u, cpu_id)
    ||| thread_exit_unlock_table_step_pre(old_u, cpu_id) && thread_exit_unlock_table_step(old_u, new_u, cpu_id)
}

/// Finishing runs while the running thread records an exit with every descriptor released and no caller, and holds the
/// cpu, its container, its process, and itself. A thread with siblings finishes right after its descriptors; a
/// process's last thread finishes after reclaiming, when neither it nor its process keeps any quota.
#[verifier::opaque]
pub open spec fn thread_exit_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let process = old_u.process_map.spec_index(prc_ptr);
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.container_map.dom().contains(ctn_ptr)
    &&& old_u.container_map.spec_index(ctn_ptr).lock_state is WriteLocked
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& process.lock_state is WriteLocked
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.caller is None
    &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> thread.endpoint_descriptors[j] is None
    &&& if process.owned_threads.len() == 1 {
        &&& thread.syscall_progress->Some_0 == SyscallProgress::ThreadExitZombie
        &&& process.quota_4k == 0
        &&& process.quota_2m == 0
        &&& process.quota_1g == 0
        &&& thread.quota_4k == 0
        &&& thread.quota_2m == 0
        &&& thread.quota_1g == 0
    } else { thread.syscall_progress->Some_0 is ThreadExit }
}

/// The running thread leaves the kernel and its cpu goes idle: its process absorbs its quota and becomes a zombie
/// without threads, a zombie root process makes its container a zombie, the container owning the thread's page regains
/// one 4K quota, at most the cpu's kernel TLB entry is flushed, and the cpu, the container, and the process are
/// released.
#[verifier::opaque]
pub open spec fn thread_exit_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let ctn_ptr = cpu.owning_container;
    let prc_ptr = cpu.current_process->Some_0;
    let unlocked = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..cpu }),
        container_map: old_u.container_map.insert(ctn_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map.spec_index(ctn_ptr) }),
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map.spec_index(prc_ptr) }),
        ..old_u
    };
    ||| kernel_u_thread_exit_changed(unlocked, new_u, cpu_id, cpu.current_thread->Some_0, false)
    ||| kernel_u_thread_exit_changed(unlocked, new_u, cpu_id, cpu.current_thread->Some_0, true)
}

/// The partial trace before finishing: one enter step from `pre` followed by middle steps.
#[verifier::opaque]
pub open spec fn thread_exit_partial_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId) -> bool {
    // the enter step, then any middle steps
    &&& 1 <= trace.len()
    &&& trace[0].old_u == pre
    &&& thread_exit_enter_step_pre(pre, cpu_id)
    &&& thread_exit_enter_step(pre, trace[0].new_u, cpu_id)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> thread_exit_middle_step(trace[j], cpu_id)
}

/// Complete trace of the call: on an exit, the partial trace followed by the finish step; a stutter otherwise.
#[verifier::opaque]
pub open spec fn thread_exit_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, exited: bool) -> bool {
    if exited {
        // the enter step, any middle steps, and the finish step
        &&& 2 <= trace.len()
        &&& thread_exit_partial_trace(trace.drop_last(), pre, cpu_id)
        &&& trace.last().new_u == post
        &&& thread_exit_finish_step_pre(trace.last().old_u, cpu_id)
        &&& thread_exit_finish_step(trace.last().old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!

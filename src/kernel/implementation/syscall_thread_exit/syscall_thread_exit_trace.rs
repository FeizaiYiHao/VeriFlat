use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
verus! {
/// Acquiring the caller's context locks, waking the caller the thread serves, and recording the progress is the enter
/// step on `pre`/`post`.
pub(super) proof fn thread_exit_enter_step_from_u(
    pre: KernelU, locked: KernelU, woken: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let caller = pre.thread_map.spec_index(thread.caller->Some_0);
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& !pre.container_map.spec_index(container_ptr).killed
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& thread.caller is Some ==> {
                &&& pre.thread_map.dom().contains(thread.caller->Some_0)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state.is_reply_waiting()
            }
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::WriteLocked, ..pre.container_map[container_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
        woken == match pre.thread_map.spec_index(thread_ptr).caller {
            Some(caller_ptr) => if locked.thread_map[caller_ptr].state is DANGLING {
                KernelU {
                    thread_map: locked.thread_map.insert(thread_ptr, ThreadU { caller: None, ..locked.thread_map[thread_ptr] }).insert(caller_ptr, ThreadU {
                        state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..locked.thread_map[caller_ptr]
                    }),
                    ..locked
                }
            } else {
                let container = locked.thread_map[caller_ptr].owning_container;
                KernelU {
                    container_map: locked.container_map.insert(container, ContainerU {
                        scheduler: locked.container_map[container].scheduler.update(cpu_id as int, locked.container_map[container].scheduler[cpu_id as int].push(caller_ptr)),
                        ..locked.container_map[container]
                    }),
                    thread_map: locked.thread_map.insert(thread_ptr, ThreadU { caller: None, ..locked.thread_map[thread_ptr] }).insert(caller_ptr, ThreadU {
                        state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..locked.thread_map[caller_ptr]
                    }),
                    ..locked
                }
            },
            None => locked,
        },
        post == (KernelU { thread_map: woken.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExit { next: 0 }), ..woken.thread_map[thread_ptr] }), ..woken }),
    ensures
        thread_exit_enter_step_pre(pre, cpu_id),
        thread_exit_enter_step(pre, post, cpu_id),
{ reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); }

/// Releasing descriptor `index`, the first one at or after the recorded position `next`, is the drop step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_drop_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, next: EndpointIdx, index: EndpointIdx,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is WriteLocked
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::ThreadExit { next })
            &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
            &&& thread.endpoint_descriptors[index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& pre.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
        },
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(index as int, None),
                syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..pre.thread_map[thread_ptr]
            }),
            endpoint_map: pre.endpoint_map.insert(endpoint_ptr, EndpointU {
                owning_threads: pre.endpoint_map[endpoint_ptr].owning_threads.remove((thread_ptr, index)), ..pre.endpoint_map[endpoint_ptr]
            }),
            ..pre
        }),
    ensures
        thread_exit_drop_step_pre(pre, cpu_id),
        thread_exit_drop_step(pre, post, cpu_id),
{ reveal(thread_exit_drop_step_pre); reveal(thread_exit_drop_step); }

/// Removing the exiting thread while releasing its cpu, container, and process is the finish step on `pre`/`post`.
pub(super) proof fn thread_exit_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    flushed_default_pcid: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let process = pre.process_map.spec_index(process_ptr);
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is WriteLocked
            &&& pre.thread_map.dom().contains(thread_ptr)
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
        },
        kernel_u_thread_exit_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..pre.container_map[container_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
            ..pre
        }, post, cpu_id, thread_ptr, flushed_default_pcid),
    ensures
        thread_exit_finish_step_pre(pre, cpu_id),
        thread_exit_finish_step(pre, post, cpu_id),
{ reveal(thread_exit_finish_step_pre); reveal(thread_exit_finish_step); }

/// Write-locking the page table of the process of the running last thread, while recording reclaim progress, is the
/// lock-table step on `pre`/`post`.
pub(super) proof fn thread_exit_lock_table_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let process = pre.process_map.spec_index(process_ptr);
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& thread.syscall_progress->Some_0 is ThreadExit
            &&& thread.caller is None
            &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> thread.endpoint_descriptors[j] is None
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is WriteLocked
            &&& process.owned_threads.len() == 1
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is Unlocked
            &&& process.iommu_table is Some ==> process.iommu_table->Some_0.lock_state is Unlocked
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
        },
        post.iommu_tlb.dom() == pre.iommu_tlb.dom(),
        forall|bus: usize, device: usize, function: usize| #![trigger post.iommu_tlb[pci_bdf_did(bus, device, function)]]
            pci_bdf_valid(bus, device, function) ==> post.iommu_tlb[pci_bdf_did(bus, device, function)]
                == if thread_exit_detaches(pre.iommu_root_table, process_ptr, bus as int, device as int, function as int) { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } }
                else { pre.iommu_tlb[pci_bdf_did(bus, device, function)] },
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr].pagetable->Some_0 }),
                iommu_table: match pre.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked, ..t }), None => None },
                ..pre.process_map[process_ptr]
            }),
            iommu_root_table: IommuRootTableU { attached: thread_exit_detached_attached(pre.iommu_root_table, process_ptr), ..pre.iommu_root_table },
            iommu_tlb: post.iommu_tlb,
            ..pre
        }),
    ensures
        thread_exit_lock_table_step_pre(pre, cpu_id),
        thread_exit_lock_table_step(pre, post, cpu_id),
{ reveal(thread_exit_lock_table_step_pre); reveal(thread_exit_lock_table_step); }

/// Clearing the user 4K leaf `va` of the locked page table before the flush is a leaf step on `pre`/`post`.
pub(super) proof fn thread_exit_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr)
    requires
        unmap_4k_locked(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].owning_proc == process_ptr,
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        pre.process_map[process_ptr].pagetable->Some_0.mapping_4k.dom().contains(va),
        spec_va_4k_valid(va),
        pre.kernel_l4_end <= spec_v2l4index(va),
        post == (KernelU {
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { mapping_4k: pre.process_map[process_ptr].pagetable->Some_0.mapping_4k.remove(va), ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: pre.thread_map[thread_ptr].syscall_progress, ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures
        thread_exit_reclaim_step_pre(pre, cpu_id, false),
        thread_exit_leaf_step(pre, post, cpu_id),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_leaf_step);
    let mapping = pre.process_map[process_ptr].pagetable->Some_0.mapping_4k;
    let kept = post.process_map[process_ptr].pagetable->Some_0.mapping_4k.dom();
    assert(pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: pre.thread_map[thread_ptr].syscall_progress, ..pre.thread_map[thread_ptr] }) =~= pre.thread_map);
    assert(kept =~= mapping.dom().remove(va));
    assert(mapping.dom().difference(kept) =~= set![va]);
    assert(mapping.remove(va) =~= mapping.restrict(kept));
}

/// Clearing the 4K leaf `iova` of the locked IOMMU table after the flush is an IOMMU leaf step on `pre`/`post`.
pub(super) proof fn thread_exit_iommu_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, iova: VAddr)
    requires
        unmap_4k_locked(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].owning_proc == process_ptr,
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        pre.process_map[process_ptr].iommu_table is Some,
        pre.process_map[process_ptr].iommu_table->Some_0.lock_state is WriteLocked,
        pre.process_map[process_ptr].iommu_table->Some_0.mapping_4k.dom().contains(iova),
        post == (KernelU {
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                iommu_table: Some(PageTableU { mapping_4k: pre.process_map[process_ptr].iommu_table->Some_0.mapping_4k.remove(iova), ..pre.process_map[process_ptr].iommu_table->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            ..pre
        }),
    ensures
        thread_exit_reclaim_step_pre(pre, cpu_id, true),
        thread_exit_iommu_leaf_step(pre, post, cpu_id),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_iommu_leaf_step);
    let mapping = pre.process_map[process_ptr].iommu_table->Some_0.mapping_4k;
    let kept = post.process_map[process_ptr].iommu_table->Some_0.mapping_4k.dom();
    assert(kept =~= mapping.dom().remove(iova));
    assert(mapping.dom().difference(kept) =~= set![iova]);
    assert(mapping.remove(iova) =~= mapping.restrict(kept));
}

/// The running last thread may flush once every user 4K mapping of its locked page table is cleared.
pub(super) proof fn thread_exit_flush_step_pre_from_u(u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        unmap_4k_locked(u, cpu_id),
        u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        u.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        thread_exit_user_4k_unmapped(u, u.process_map[u.thread_map[thread_ptr].owning_proc].pagetable->Some_0),
    ensures
        thread_exit_flush_step_pre(u, cpu_id),
{ reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); }

/// Recording the flush is the flushed step on `pre`/`post`.
pub(super) proof fn thread_exit_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map.dom().contains(thread_ptr),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: true }), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures
        thread_exit_flushed_step(pre, post, cpu_id),
{ reveal(thread_exit_flushed_step); }

/// Returning the `size` quota of the running last thread and of its process to their container is the quota step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_quota_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires
        unmap_4k_locked(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(thread_exit_quota_progress_before(size)),
        ({
            let thread = pre.thread_map[thread_ptr];
            let process = pre.process_map[thread.owning_proc];
            let container = pre.container_map[thread.owning_container];
            let progress = Some(SyscallProgress::ThreadExitQuota { returned: size });
            post == (KernelU {
                container_map: pre.container_map.insert(thread.owning_container, match size {
                    PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
                    PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
                    PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
                }),
                process_map: pre.process_map.insert(thread.owning_proc, match size {
                    PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                    PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                    PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
                }),
                thread_map: pre.thread_map.insert(thread_ptr, match size {
                    PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
                    PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
                    PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
                }),
                ..pre
            })
        }),
    ensures
        thread_exit_quota_step_pre(pre, cpu_id),
        thread_exit_quota_step(pre, post, cpu_id),
{ reveal(thread_exit_quota_step_pre); reveal(thread_exit_quota_step); }

/// Unlocking the reclaimed page table and IOMMU table once every quota size is returned is the unlock-table step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_unlock_table_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        unmap_4k_locked(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g }),
        thread_exit_user_4k_unmapped(pre, pre.process_map[pre.thread_map[thread_ptr].owning_proc].pagetable->Some_0),
        pre.process_map[pre.thread_map[thread_ptr].owning_proc].iommu_table is Some
            ==> thread_exit_iommu_4k_unmapped(pre.process_map[pre.thread_map[thread_ptr].owning_proc].iommu_table->Some_0),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitZombie), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(pre.thread_map[thread_ptr].owning_proc, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[pre.thread_map[thread_ptr].owning_proc].pagetable->Some_0 }),
                iommu_table: match pre.process_map[pre.thread_map[thread_ptr].owning_proc].iommu_table {
                    Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }),
                    None => None,
                },
                ..pre.process_map[pre.thread_map[thread_ptr].owning_proc]
            }),
            ..pre
        }),
    ensures
        thread_exit_unlock_table_step_pre(pre, cpu_id),
        thread_exit_unlock_table_step(pre, post, cpu_id),
{ reveal(thread_exit_unlock_table_step_pre); reveal(thread_exit_unlock_table_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(super) proof fn thread_exit_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        thread_exit_enter_step_pre(pre, cpu_id),
        thread_exit_enter_step(pre, post, cpu_id),
    ensures
        thread_exit_partial_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id),
{ reveal(thread_exit_partial_trace); }

/// A middle step pushed after the partial trace that starts at `start` extends it.
pub(super) proof fn thread_exit_trace_push(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        steps.view() == before.push(KernelStep { old_u: step_pre, new_u: step_post }),
        thread_exit_middle_step(KernelStep { old_u: step_pre, new_u: step_post }, cpu_id),
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: step_pre, new_u: step_post }));
}

/// TLB flushes of the PCID of the running last thread's process, recorded after the partial trace that starts at
/// `start` while the thread's held objects keep their projection at `entry`, extend it.
pub(super) proof fn thread_exit_trace_from_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        thread_exit_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        entry.thread_map[thread_ptr].owning_proc == process_ptr,
        entry.thread_map[thread_ptr].owning_container == container_ptr,
        entry.process_map[process_ptr].pcid == pcid,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr] == (ProcessU { iommu_table: old_u.process_map[process_ptr].iommu_table, ..entry.process_map[process_ptr] })
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry.kernel_l4_end
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre);
    let trace = steps.view().subrange(start, steps.view().len() as int);
    let old_trace = before.subrange(start, before.len() as int);
    assert forall|j: int| #![trigger trace[j]] 0 < j < trace.len() implies thread_exit_middle_step(trace[j], cpu_id) by {
        if start + j < before.len() { assert(trace[j] == old_trace[j]); } else { assert(trace[j] == steps.view()[start + j]); }
    };
}

/// Quota refunds to the container chain of the running last thread after the flush is recorded, pushed after the partial
/// trace that starts at `start`, extend it.
pub(super) proof fn thread_exit_trace_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        0 <= start <= before.len() <= steps.view().len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, container_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == container_ptr
            &&& old_u.thread_map[thread_ptr].owning_proc == process_ptr
            &&& old_u.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: true })
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state is WriteLocked
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& old_u.process_map[process_ptr].pagetable->Some_0.lock_state is WriteLocked
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_reclaim_step_pre);
    let trace = steps.view().subrange(start, steps.view().len() as int);
    let old_trace = before.subrange(start, before.len() as int);
    assert forall|j: int| #![trigger trace[j]] 0 < j < trace.len() implies thread_exit_middle_step(trace[j], cpu_id) by {
        if start + j < before.len() { assert(trace[j] == old_trace[j]); } else { assert(trace[j] == steps.view()[start + j]); }
    };
}

/// The finish step pushed after the partial trace that starts at `start` completes the trace of an exit.
pub(super) proof fn thread_exit_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        thread_exit_finish_step_pre(finish_pre, cpu_id),
        thread_exit_finish_step(finish_pre, post, cpu_id),
    ensures
        thread_exit_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, true),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_syscall_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: finish_pre, new_u: post }));
}

/// A rejected call records no step.
pub(super) proof fn thread_exit_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId)
    requires
        trace.len() == 0,
    ensures
        thread_exit_syscall_trace(trace, pre, pre, cpu_id, false),
{ reveal(thread_exit_syscall_trace); }
} // verus!

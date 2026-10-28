use vstd::prelude::*;
use crate::*;

verus! {
/// The iova range of `range` 4K pages starting at `iova`.
pub open spec fn iommu_unmap_4k_iova_range(iova: VAddr, range: usize) -> VaRange4K {
    VaRange4K { start: iova, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(iova, i as usize))) }
}

/// The result of `syscall_iommu_unmap_4k` from the state at entry, in the implementation's check order: malformed
/// arguments, an idle or marked cpu, a killed container, a container write-held under a live process owner below the
/// caller's process depth, a zombie container, a killed process or caller, a process without an IOMMU table, and then a
/// range below the first user L4 index or with an iova that has no present 4K leaf.
pub open spec fn iommu_unmap_4k_syscall_result(pre: KernelU, cpu_id: CpuId, iova: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let process = pre.process_map[thread.owning_proc];
    let mapping = process.iommu_table->Some_0.mapping_4k;
    let owner = pre.container_map[thread.owning_container].lock_process_owner;
    let iova_range = iommu_unmap_4k_iova_range(iova, range);
    if range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(iova) || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if pre.container_map[thread.owning_container].killed { RetValueType::ErrorContainerKilled }
    else if owner is Some && owner->Some_0 < LockOwnerId::Some(process.depth) { RetValueType::ErrorContainerLockOrderConflict }
    else if pre.container_map[thread.owning_container].zombie { RetValueType::ErrorContainerZombie }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if process.iommu_table is None { RetValueType::ErrorPciNoIommuTable }
    else if user_va_range(pre, iova_range) && forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(iova_range.view()[j]) {
        RetValueType::Success
    } else { RetValueType::ErrorIommuIovaNotMapped }
}

/// The cpu, its running thread, and the thread's process and container are write-locked.
pub open spec fn iommu_unmap_4k_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(thread_ptr)
    &&& thread.lock_state is WriteLocked
    &&& u.process_map.dom().contains(thread.owning_proc)
    &&& u.process_map.spec_index(thread.owning_proc).lock_state is WriteLocked
    &&& u.container_map.dom().contains(thread.owning_container)
    &&& u.container_map.spec_index(thread.owning_container).lock_state is WriteLocked
}

/// The IOMMU-unmap locks are held and the process's IOMMU table is write-locked.
pub open spec fn iommu_unmap_4k_table_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let thread = u.thread_map.spec_index(u.cpu_array[cpu_id as int].current_thread->Some_0);
    let process = u.process_map.spec_index(thread.owning_proc);
    &&& iommu_unmap_4k_locked(u, cpu_id)
    &&& process.iommu_table is Some
    &&& process.iommu_table->Some_0.lock_state is WriteLocked
}

/// The cpu runs a live thread of a live process and container with no multi-step syscall in progress; the cpu, the
/// thread, its process, and container are unlocked; the process has an unlocked IOMMU table; and every iova of the
/// valid, non-empty user range is mapped in it.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, iova_range: VaRange4K) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let container = old_u.container_map.spec_index(thread.owning_container);
    let iommu_table = process.iommu_table->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& process.iommu_table is Some
    &&& iommu_table.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& container.lock_state is Unlocked
    &&& !container.killed
    &&& !container.zombie
    &&& iova_range.wf()
    &&& iova_range.len > 0
    &&& user_va_range(old_u, iova_range)
    &&& forall|i: int| #![trigger iommu_table.mapping_4k.dom().contains(iova_range.view()[i])] 0 <= i < iova_range.len ==> iommu_table.mapping_4k.dom().contains(iova_range.view()[i])
}

/// Entering write-locks the cpu, its running thread, the thread's process and container, recording the process depth as
/// the container's lock owner, and the process's IOMMU table, and starts progress at the first iova.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, iova_range: VaRange4K) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::IommuUnmap4k { iova_range, unmapped: 0, flushed: false };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU {
            lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(process.depth)), ..old_u.container_map.spec_index(thread.owning_container)
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::WriteLocked, iommu_table: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.iommu_table->Some_0 }), ..process
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        ..old_u
    })
}

/// A leaf step hides the next iova of the recorded range, which is still mapped, under the IOMMU-unmap locks.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = thread.syscall_progress->Some_0;
    &&& iommu_unmap_4k_table_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuUnmap4k
    &&& progress->IommuUnmap4k_unmapped < progress->IommuUnmap4k_iova_range.len
    &&& !progress->IommuUnmap4k_flushed
    &&& process.iommu_table->Some_0.mapping_4k.dom().contains(progress->IommuUnmap4k_iova_range.view()[progress->IommuUnmap4k_unmapped as int])
}

/// A leaf step removes the next iova from the IOMMU table's user view and advances the progress.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let iommu_table = process.iommu_table->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let iova_range = progress->IommuUnmap4k_iova_range;
    let unmapped = progress->IommuUnmap4k_unmapped;
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::IommuUnmap4k { iova_range, unmapped: (unmapped + 1) as usize, flushed: false }), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            iommu_table: Some(PageTableU { mapping_4k: iommu_table.mapping_4k.remove(iova_range.view()[unmapped as int]), ..iommu_table }), ..process
        }),
        ..old_u
    })
}

/// The flush step runs under the IOMMU-unmap locks after every iova of the recorded range has been hidden.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& iommu_unmap_4k_table_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuUnmap4k
    &&& progress->IommuUnmap4k_unmapped == progress->IommuUnmap4k_iova_range.len
    &&& !progress->IommuUnmap4k_flushed
}

/// The flush step invalidates only the IOTLB domain of the process's IOMMU table, which may hold at once only what that
/// domain may cache, keeping every other domain, or leaves the IOTLB unchanged when the table has no DID, and records the
/// flush.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_flush_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let did = old_u.process_map.spec_index(thread.owning_proc).iommu_table->Some_0.did;
    let progress = thread.syscall_progress->Some_0;
    let flushed = SyscallProgress::IommuUnmap4k { iova_range: progress->IommuUnmap4k_iova_range, unmapped: progress->IommuUnmap4k_unmapped, flushed: true };
    let iommu_tlb = match did { Some(d) => old_u.iommu_tlb.insert(d, new_u.iommu_tlb[d]), None => old_u.iommu_tlb };
    &&& new_u == (KernelU { iommu_tlb, thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(flushed), ..thread }), ..old_u })
    &&& did matches Some(d) ==> iommu_tlb_within_may_cache_u(new_u, d, new_u.iommu_tlb[d])
}

/// A refund step runs under the cpu, container, process, and thread locks after the flush has been recorded.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_refund_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& iommu_unmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuUnmap4k
    &&& progress->IommuUnmap4k_unmapped == progress->IommuUnmap4k_iova_range.len
    &&& progress->IommuUnmap4k_flushed
}

/// A step between entering and exiting hides one leaf, flushes the IOTLB, or refunds 4K quota to the thread's
/// container chain.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    ||| iommu_unmap_4k_leaf_step_pre(step.old_u, cpu_id) && iommu_unmap_4k_leaf_step(step.old_u, step.new_u, cpu_id)
    ||| iommu_unmap_4k_flush_step_pre(step.old_u, cpu_id) && iommu_unmap_4k_flush_step(step.old_u, step.new_u, cpu_id)
    ||| iommu_unmap_4k_refund_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_4k_increased(step.old_u, step.new_u, thread.owning_container)
}

/// Exiting happens under the IOMMU-unmap locks after every iova has been hidden and the flush has been recorded.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& iommu_unmap_4k_table_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuUnmap4k
    &&& progress->IommuUnmap4k_unmapped == progress->IommuUnmap4k_iova_range.len
    &&& progress->IommuUnmap4k_flushed
}

/// Exiting clears the progress and unlocks the cpu, its running thread, the thread's process and container, clearing the
/// container's lock owner, and the process's IOMMU table.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU {
            lock_state: LockStateU::Unlocked, op: cpu_op_after_step(old_u.cpu_array[cpu_id as int].state), ..old_u.cpu_array[cpu_id as int]
        }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU {
            lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map.spec_index(thread.owning_container)
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::Unlocked, iommu_table: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.iommu_table->Some_0 }), ..process
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after entering: the enter step followed by `trace.len() - 1` range steps.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_partial_trace(trace: Seq<KernelStep>, cpu_id: CpuId, iova_range: VaRange4K) -> bool {
    &&& 1 <= trace.len()
    &&& iommu_unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, iova_range)
    &&& iommu_unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, iova_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> iommu_unmap_4k_range_step(trace[j], cpu_id)
}

/// The full trace of a successful IOMMU unmap: one enter step; one step per hidden leaf; one flush step; at most one
/// refund step per container level plus the direct refund; and one exit step.
#[verifier::opaque]
pub open spec fn iommu_unmap_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, iova: VAddr, range: usize) -> bool {
    let iova_range = iommu_unmap_4k_iova_range(iova, range);
    &&& range + 3 <= trace.len() <= range + MAX_CONTAINER_TREE_DEPTH + 4
    &&& iommu_unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, iova_range)
    &&& iommu_unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, iova_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> iommu_unmap_4k_range_step(trace[j], cpu_id)
    &&& iommu_unmap_4k_exit_step_pre(trace.last().old_u, cpu_id)
    &&& iommu_unmap_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}
} // verus!

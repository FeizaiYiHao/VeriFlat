use vstd::prelude::*;
use crate::*;

verus! {
/// The page-aligned 4K sequence of `len` pages from `va` requested by `syscall_iommu_map_4k`.
pub open spec fn iommu_map_4k_syscall_range(va: VAddr, len: usize) -> VaRange4K {
    VaRange4K { start: va, len, view: Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize))) }
}

/// The result of `syscall_iommu_map_4k` from the state at entry, in the implementation's check order: malformed
/// arguments, a cpu no longer Running or marked by a killer, a killed process or caller, a process without an IOMMU table, less than
/// three 4K quota per page (one per IOMMU directory level that may be missing), a va range below the first user L4 index,
/// a va page not mapped in the page table, and an iova page already mapped in the IOMMU table.
pub open spec fn iommu_map_4k_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, iova: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let process = pre.process_map[thread.owning_proc];
    let va_range = iommu_map_4k_syscall_range(va, range);
    let iova_range = iommu_map_4k_syscall_range(iova, range);
    if range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) || !spec_va_4k_valid(iova)
        || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if process.iommu_table is None { RetValueType::ErrorPciNoIommuTable }
    else if thread.quota_4k < 3 * range { RetValueType::ErrorNoQuota }
    else if !user_va_range(pre, va_range) { RetValueType::Error }
    else if !(forall|i: int| #![trigger process.pagetable->Some_0.mapping_4k.dom().contains(va_range.view()[i])] 0 <= i < range ==> process.pagetable->Some_0.mapping_4k.dom().contains(va_range.view()[i])) {
        RetValueType::ErrorIommuVaNotMapped
    }
    else if !(forall|i: int| #![trigger process.iommu_table->Some_0.mapping_4k.dom().contains(iova_range.view()[i])] 0 <= i < range ==> !process.iommu_table->Some_0.mapping_4k.dom().contains(iova_range.view()[i])) {
        RetValueType::ErrorIommuIovaAlreadyMapped
    }
    else { RetValueType::Success }
}

/// The cpu, its running thread, and the thread's process are write-locked, and the process has a read-held page table and
/// a write-held IOMMU table.
pub open spec fn iommu_map_4k_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let process = u.process_map.spec_index(u.thread_map.spec_index(thread_ptr).owning_proc);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(thread_ptr)
    &&& u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
    &&& u.process_map.dom().contains(u.thread_map.spec_index(thread_ptr).owning_proc)
    &&& process.lock_state is WriteLocked
    &&& process.pagetable is Some
    &&& process.pagetable->Some_0.lock_state is ReadLocked
    &&& process.iommu_table is Some
    &&& process.iommu_table->Some_0.lock_state is WriteLocked
}

/// The cpu runs a live thread of a live process of an existing container with no multi-step syscall in progress; the cpu,
/// the thread, and its process are unlocked, the process's page table is not write-locked and its IOMMU table is unlocked; `va_range` and
/// `iova_range` are valid user ranges of equal non-zero length; every page of `va_range` is mapped in the page table and
/// no page of `iova_range` is mapped in the IOMMU table.
#[verifier::opaque]
pub open spec fn iommu_map_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, va_range: VaRange4K, iova_range: VaRange4K) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
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
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& process.pagetable is Some
    &&& !(process.pagetable->Some_0.lock_state is WriteLocked)
    &&& process.iommu_table is Some
    &&& process.iommu_table->Some_0.lock_state is Unlocked
    &&& va_range.wf()
    &&& iova_range.wf()
    &&& va_range.len > 0
    &&& iova_range.len == va_range.len
    &&& user_va_range(old_u, va_range)
    &&& forall|i: int| #![trigger process.pagetable->Some_0.mapping_4k.dom().contains(va_range.view()[i])] 0 <= i < va_range.len ==> process.pagetable->Some_0.mapping_4k.dom().contains(va_range.view()[i])
    &&& forall|i: int| #![trigger process.iommu_table->Some_0.mapping_4k.dom().contains(iova_range.view()[i])] 0 <= i < iova_range.len ==> !process.iommu_table->Some_0.mapping_4k.dom().contains(iova_range.view()[i])
}

/// Entering write-locks the cpu, its running thread, and its process, read-locks the page table and write-locks its existing
/// 2M windows of the va range, write-locks the IOMMU table, and starts progress at the first page with no directory installed.
#[verifier::opaque]
pub open spec fn iommu_map_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va_range: VaRange4K, iova_range: VaRange4K) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::IommuMap4k { va_range, iova_range, mapped: 0, directory: Mmap4kDirectory::None };
    let pagetable = process.pagetable->Some_0;
    let windows = pagetable_window_locks_after_locking_range(pagetable.pagetable_window_locks, va_range);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::WriteLocked, pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: windows, ..pagetable }),
            iommu_table: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.iommu_table->Some_0 }), ..process
        }),
        ..old_u
    })
}

/// A directory step starts under the IOMMU-map locks, before the recorded range is fully mapped, with quota for one
/// directory page.
#[verifier::opaque]
pub open spec fn iommu_map_4k_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& iommu_map_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuMap4k
    &&& progress->IommuMap4k_mapped < progress->IommuMap4k_iova_range.len
    &&& thread.quota_4k >= 1
}

/// An IOMMU directory page consumes one 4K quota and records a deeper level than the last recorded one; directory
/// topology is not visible in `PageTableU`.
#[verifier::opaque]
pub open spec fn iommu_map_4k_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let progress = thread.syscall_progress->Some_0;
    let new_progress = new_u.thread_map.spec_index(thread_ptr).syscall_progress->Some_0;
    &&& new_u.thread_map.spec_index(thread_ptr).syscall_progress is Some
    &&& new_progress is IommuMap4k
    &&& new_progress->IommuMap4k_va_range == progress->IommuMap4k_va_range
    &&& new_progress->IommuMap4k_iova_range == progress->IommuMap4k_iova_range
    &&& new_progress->IommuMap4k_mapped == progress->IommuMap4k_mapped
    &&& mmap_4k_directory_rank(progress->IommuMap4k_directory) < mmap_4k_directory_rank(new_progress->IommuMap4k_directory)
    &&& new_u == (KernelU { thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: Some(new_progress), ..thread }), ..old_u })
}

/// A leaf step maps the next iova of the recorded range under the IOMMU-map locks: its va is mapped in the page table and
/// the iova is not mapped in the IOMMU table.
#[verifier::opaque]
pub open spec fn iommu_map_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = thread.syscall_progress->Some_0;
    let va = progress->IommuMap4k_va_range.view()[progress->IommuMap4k_mapped as int];
    let iova = progress->IommuMap4k_iova_range.view()[progress->IommuMap4k_mapped as int];
    &&& iommu_map_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuMap4k
    &&& progress->IommuMap4k_mapped < progress->IommuMap4k_iova_range.len
    &&& progress->IommuMap4k_iova_range.len == progress->IommuMap4k_va_range.len
    &&& process.pagetable->Some_0.mapping_4k.dom().contains(va)
    &&& !process.iommu_table->Some_0.mapping_4k.dom().contains(iova)
}

/// A leaf step publishes the page table's entry for the next va at the next iova of the IOMMU table; the page table and
/// the IOTLB are unchanged.
#[verifier::opaque]
pub open spec fn iommu_map_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let iommu_table = process.iommu_table->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let va = progress->IommuMap4k_va_range.view()[progress->IommuMap4k_mapped as int];
    let iova = progress->IommuMap4k_iova_range.view()[progress->IommuMap4k_mapped as int];
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { syscall_progress: iommu_map_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            iommu_table: Some(PageTableU { mapping_4k: iommu_table.mapping_4k.insert(iova, process.pagetable->Some_0.mapping_4k.spec_index(va)), ..iommu_table }), ..process
        }),
        ..old_u
    })
}

/// Exiting happens under the IOMMU-map locks after every page of the recorded range has been mapped.
#[verifier::opaque]
pub open spec fn iommu_map_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& iommu_map_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is IommuMap4k
    &&& progress->IommuMap4k_mapped == progress->IommuMap4k_iova_range.len
    &&& progress->IommuMap4k_directory is None
}

/// Exiting clears progress, unlocks the cpu, its running thread, its process, the IOMMU table, and the page table's existing 2M
/// windows of the recorded va range, and drops the thread's read lock on its page table, which other readers may still hold.
#[verifier::opaque]
pub open spec fn iommu_map_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let table_lock = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state;
    let windows = pagetable_window_locks_after_unlocking_range(pagetable.pagetable_window_locks, thread.syscall_progress->Some_0->IommuMap4k_va_range);
    &&& table_lock is Unlocked || table_lock is ReadLocked
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU {
            lock_state: LockStateU::Unlocked, op: cpu_op_after_step(old_u.cpu_array[cpu_id as int].state), ..old_u.cpu_array[cpu_id as int]
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: table_lock, pagetable_window_locks: windows, ..pagetable }),
            iommu_table: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.iommu_table->Some_0 }), ..process
        }),
        ..old_u
    })
}

/// A step inside the IOMMU-map loop installs one IOMMU directory page or publishes one IOMMU leaf.
#[verifier::opaque]
pub open spec fn iommu_map_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    ||| iommu_map_4k_directory_step_pre(step.old_u, cpu_id) && iommu_map_4k_directory_step(step.old_u, step.new_u, cpu_id)
    ||| iommu_map_4k_leaf_step_pre(step.old_u, cpu_id) && iommu_map_4k_leaf_step(step.old_u, step.new_u, cpu_id)
}

/// The full trace of a successful IOMMU map: one enter step, at most three directory steps and one leaf step per page,
/// and one exit step.
#[verifier::opaque]
pub open spec fn iommu_map_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va_range: VaRange4K, iova_range: VaRange4K) -> bool {
    &&& va_range.len + 2 <= trace.len() <= 4 * va_range.len + 2
    &&& iommu_map_4k_enter_step_pre(trace[0].old_u, cpu_id, va_range, iova_range)
    &&& iommu_map_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va_range, iova_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> iommu_map_4k_range_step(trace[j], cpu_id)
    &&& iommu_map_4k_exit_step_pre(trace.last().old_u, cpu_id)
    &&& iommu_map_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}
} // verus!

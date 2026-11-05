use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_unmap_2m` from the state at entry, in the implementation's check order: malformed arguments, a
/// killed caller, and then a range below the first user L4 index or with a page that has no present 2M leaf.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn unmap_2m_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_2m;
    let va_range = spec_va_range_2m(va, range);
    if range == 0 || range > usize::MAX / 0x200000 || !spec_va_2m_valid(va) || va >= usize::MAX - range * 0x200000 || !spec_va_2m_range_valid(va, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if user_va_range(pre, va_range.covering_4k_range()) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(va_range.view()[j]) {
        RetValueType::Success
    } else { RetValueType::Error }
}

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu and the thread are unlocked; the thread's
/// process has a pagetable that no thread write-holds; the thread's container exists; and every page of the valid,
/// non-empty user range is mapped by a 2M leaf.
#[verifier::opaque]
pub open spec fn unmap_2m_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange2M) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& process.pagetable is Some
    &&& !(pagetable.lock_state is WriteLocked)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& range.wf()
    &&& range.len > 0
    &&& user_va_range(old_u, range.covering_4k_range())
    &&& forall|i: int| #![trigger pagetable.mapping_2m.dom().contains(range.view()[i])] 0 <= i < range.len ==> pagetable.mapping_2m.dom().contains(range.view()[i])
}

/// Entering write-locks the cpu, which enters its kernel step, and its running thread, read-locks the pagetable of the
/// thread's process, write-locks the 2M windows of the range, and starts progress at the first page.
#[verifier::opaque]
pub open spec fn unmap_2m_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange2M) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Unmap2m { range, unmapped: 0, flushed: false };
    let pagetable = process.pagetable->Some_0;
    let windows = pagetable_window_locks_after_locking_range(pagetable.pagetable_window_locks, range.covering_4k_range());
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: windows, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        ..old_u
    })
}

/// A leaf step runs while the range is not fully cleared and before the flush, and the next page of the range, the
/// `unmapped`-th, is still mapped.
#[verifier::opaque]
pub open spec fn unmap_2m_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap2m
    &&& progress->Unmap2m_unmapped < progress->Unmap2m_range.len
    &&& !progress->Unmap2m_flushed
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_2m.dom().contains(progress->Unmap2m_range.view()[progress->Unmap2m_unmapped as int])
}

/// A leaf step removes the next page of the range, the `unmapped`-th, from the process's 2M user mapping and advances
/// unmap progress.
#[verifier::opaque]
pub open spec fn unmap_2m_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Unmap2m_range.view()[progress->Unmap2m_unmapped as int];
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap2m { range: progress->Unmap2m_range, unmapped: (progress->Unmap2m_unmapped + 1) as usize, flushed: false }), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { mapping_2m: pagetable.mapping_2m.remove(va), ..pagetable }), ..process }),
        ..old_u
    })
}

/// A flush step runs after every recorded page has been cleared and before the flush is recorded, while the thread's
/// container exists.
#[verifier::opaque]
pub open spec fn unmap_2m_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is Unmap2m
    &&& progress->Unmap2m_unmapped == progress->Unmap2m_range.len
    &&& !progress->Unmap2m_flushed
}

/// Recording the flush changes unmap progress and releases this thread's read hold on the cpu set of the thread's
/// container, which no writer holds afterwards.
#[verifier::opaque]
pub open spec fn unmap_2m_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let cpu_set_lock = new_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& !(cpu_set_lock is WriteLocked)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap2m { range: progress->Unmap2m_range, unmapped: progress->Unmap2m_unmapped, flushed: true }), ..thread }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock, ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// A step inside the unmap range clears one 2M leaf, flushes the process's PCID on one cpu, records the flush, or refunds
/// 2M quota to the thread's container chain.
#[verifier::opaque]
pub open spec fn unmap_2m_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    ||| unmap_2m_leaf_step_pre(step.old_u, cpu_id) && unmap_2m_leaf_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_2m_flush_step_pre(step.old_u, cpu_id) && unmap_4k_tlb_flush_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_2m_flush_step_pre(step.old_u, cpu_id) && unmap_2m_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_2m_exit_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_2m_increased(step.old_u, step.new_u, thread.owning_container)
}

/// Refund steps and the exit step run after every page of the recorded range has been cleared and the flush has been
/// recorded.
#[verifier::opaque]
pub open spec fn unmap_2m_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap2m
    &&& progress->Unmap2m_unmapped == progress->Unmap2m_range.len
    &&& progress->Unmap2m_flushed
}

/// Exiting clears unmap progress, unlocks the cpu, which leaves its kernel step for its trap path, its running thread, and the
/// 2M windows of the recorded range, and drops the thread's read lock on the pagetable, which other readers may still hold.
#[verifier::opaque]
pub open spec fn unmap_2m_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let table_lock = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state;
    let windows = pagetable_window_locks_after_unlocking_range(pagetable.pagetable_window_locks, thread.syscall_progress->Some_0->Unmap2m_range.covering_4k_range());
    &&& table_lock is Unlocked || table_lock is ReadLocked
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: table_lock, pagetable_window_locks: windows, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after entering: the single enter step.
#[verifier::opaque]
pub open spec fn unmap_2m_trace_after_enter(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange2M) -> bool {
    &&& trace.len() == 1
    &&& unmap_2m_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_2m_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
}

/// The partial trace after unmapping the range: the enter step followed by one step per cleared leaf, flushed cpu TLB,
/// recorded flush, or quota refund.
#[verifier::opaque]
pub open spec fn unmap_2m_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange2M) -> bool {
    // enter + one leaf per page + up to NUM_CPUS TLB flushes + flushed + up to MAX_CONTAINER_TREE_DEPTH + 1 refunds
    &&& range.len + 2 <= trace.len() <= range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 3
    &&& unmap_2m_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_2m_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> unmap_2m_range_step(trace[j], cpu_id)
}

/// The full trace of a successful unmap: one enter step; one step per cleared leaf, flushed cpu TLB, recorded flush, or
/// quota refund; and one exit step.
#[verifier::opaque]
pub open spec fn unmap_2m_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let va_range = spec_va_range_2m(va, range);
    // enter + one leaf per page + up to NUM_CPUS TLB flushes + flushed + up to MAX_CONTAINER_TREE_DEPTH + 1 refunds + exit
    &&& range + 3 <= trace.len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4
    &&& unmap_2m_enter_step_pre(trace[0].old_u, cpu_id, va_range)
    &&& unmap_2m_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> unmap_2m_range_step(trace[j], cpu_id)
    &&& unmap_2m_exit_step_pre(trace.last().old_u, cpu_id)
    &&& unmap_2m_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}
} // verus!

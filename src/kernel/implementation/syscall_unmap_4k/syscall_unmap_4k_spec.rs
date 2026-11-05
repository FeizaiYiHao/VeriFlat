use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_unmap_4k` from the state at entry, in the implementation's check order: malformed arguments, a
/// killed caller, and then a range below the first user L4 index or with a page that has no 4K mapping.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn unmap_4k_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k;
    let va_range = spec_va_range_4k(va, range);
    if range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if user_va_range(pre, va_range) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(va_range.view()[j]) {
        RetValueType::Success
    } else { RetValueType::Error }
}

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu and the thread are unlocked; the thread's
/// process and container exist; no thread write-holds the process's pagetable; and every VA of the valid, non-empty user
/// range is mapped.
#[verifier::opaque]
pub open spec fn unmap_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
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
    &&& user_va_range(old_u, range)
    &&& forall|i: int| #![trigger pagetable.mapping_4k.dom().contains(range.view()[i])] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
}

/// Entering write-locks the cpu, which enters its kernel step, and its running thread, read-locks the pagetable of the
/// thread's process, write-locks the existing 2M windows of the range, and starts progress at the first page.
#[verifier::opaque]
pub open spec fn unmap_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Unmap4k { range, unmapped: 0, flushed: false };
    let pagetable = process.pagetable->Some_0;
    let windows = pagetable_window_locks_after_locking_range(pagetable.pagetable_window_locks, range, cpu_id);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: pagetable.lock_state.with_reader(cpu_id), pagetable_window_locks: windows, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(progress), ..thread }),
        ..old_u
    })
}

/// Exiting clears unmap progress, unlocks the cpu, which leaves its kernel step for its trap path, its running thread, and the
/// existing 2M windows of the recorded range, and releases this cpu's read hold on the pagetable, which it holds.
#[verifier::opaque]
pub open spec fn unmap_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let windows = pagetable_window_locks_after_unlocking_range(pagetable.pagetable_window_locks, thread.syscall_progress->Some_0->Unmap4k_range);
    &&& pagetable.lock_state.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: pagetable.lock_state.without_reader(cpu_id), pagetable_window_locks: windows, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after entering: the single enter step.
#[verifier::opaque]
pub open spec fn unmap_4k_trace_after_enter(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K) -> bool {
    &&& trace.len() == 1
    &&& unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
}

/// The partial trace after unmapping the range: the enter step followed by one step per cleared leaf,
/// flushed cpu TLB, recorded flush, or quota refund.
#[verifier::opaque]
pub open spec fn unmap_4k_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K) -> bool {
    // enter + one leaf per page + at most one TLB flush per cpu + the recorded flush + one refund per container of the
    // caller's chain, at most MAX_CONTAINER_TREE_DEPTH + 1
    &&& range.len + 2 <= trace.len() <= range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 3
    &&& unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> unmap_4k_range_step(trace[j], cpu_id)
}

/// The full trace of a successful unmap: one enter step; one step per cleared leaf, flushed cpu
/// TLB, recorded flush, or quota refund; and one exit step.
#[verifier::opaque]
pub open spec fn unmap_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let va_range = spec_va_range_4k(va, range);
    // the partial trace after unmapping the range + exit
    &&& range + 3 <= trace.len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4
    &&& unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, va_range)
    &&& unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> unmap_4k_range_step(trace[j], cpu_id)
    &&& unmap_4k_refund_step_pre(trace.last().old_u, cpu_id)
    &&& unmap_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}
} // verus!

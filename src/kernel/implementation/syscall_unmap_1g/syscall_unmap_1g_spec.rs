use vstd::prelude::*;
use crate::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::unmap_4k_spec::unmap_4k_tlb_flush_step;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::unmap_4k_spec::unmap_4k_tlb_flush_step;

verus! {
/// The result of `syscall_unmap_1g` from the state at entry, in the implementation's check order: malformed arguments, a killed caller, and then a range below the first user L4 index or with a page that has no present 1G leaf. A cpu no longer Running or marked by a killer returns CpuIdle
/// after the argument checks.
pub open spec fn unmap_1g_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_1g;
    let va_range = spec_va_range_1g(va, range);
    if range == 0 || range > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - range * 0x40000000 || !spec_va_1g_range_valid(va, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if user_va_range(pre, va_range.covering_4k_range()) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(va_range.view()[j]) {
        RetValueType::Success
    } else { RetValueType::Error }
}

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu, the thread, and the pagetable of the thread's process are unlocked; the thread's container exists; and every page of the valid, non-empty user range is mapped by a 1G leaf.
#[verifier::opaque]
pub open spec fn unmap_1g_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange1G) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& range.wf()
    &&& range.len > 0
    &&& user_va_range(old_u, range.covering_4k_range())
    &&& forall|i: int| #![trigger pagetable.mapping_1g.dom().contains(range.view()[i])] 0 <= i < range.len ==> pagetable.mapping_1g.dom().contains(range.view()[i])
}

/// Entering write-locks the cpu, which enters its kernel step, its running thread, and the pagetable of the thread's process, and starts progress at the first page.
#[verifier::opaque]
pub open spec fn unmap_1g_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange1G) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Unmap1g { range, unmapped: 0, flushed: false };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..process.pagetable->Some_0 }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(progress), ..thread }),
        ..old_u
    })
}

/// A leaf step runs while the range is not fully cleared and before the flush, and the next page of the range, the `unmapped`-th, is still mapped.
#[verifier::opaque]
pub open spec fn unmap_1g_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap1g
    &&& progress->Unmap1g_unmapped < progress->Unmap1g_range.len
    &&& !progress->Unmap1g_flushed
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_1g.dom().contains(progress->Unmap1g_range.view()[progress->Unmap1g_unmapped as int])
}

/// A leaf step removes the next page of the range, the `unmapped`-th, from the process's 1G user mapping and advances unmap progress.
#[verifier::opaque]
pub open spec fn unmap_1g_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Unmap1g_range.view()[progress->Unmap1g_unmapped as int];
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap1g { range: progress->Unmap1g_range, unmapped: (progress->Unmap1g_unmapped + 1) as usize, flushed: false }), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { mapping_1g: pagetable.mapping_1g.remove(va), ..pagetable }), ..process }),
        ..old_u
    })
}

/// A flush step runs after every recorded page has been cleared and before the flush is recorded, while the thread's container exists.
#[verifier::opaque]
pub open spec fn unmap_1g_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is Unmap1g
    &&& progress->Unmap1g_unmapped == progress->Unmap1g_range.len
    &&& !progress->Unmap1g_flushed
}

/// Recording the flush changes unmap progress and releases this cpu's read hold on the cpu set of the thread's container.
#[verifier::opaque]
pub open spec fn unmap_1g_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let cpu_set_lock = old_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap1g { range: progress->Unmap1g_range, unmapped: progress->Unmap1g_unmapped, flushed: true }), ..thread }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// A step inside the unmap range clears one 1G leaf, flushes the process's PCID on one cpu, records the flush, or refunds 1G quota to the thread's container chain.
#[verifier::opaque]
pub open spec fn unmap_1g_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    ||| unmap_1g_leaf_step_pre(step.old_u, cpu_id) && unmap_1g_leaf_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_1g_flush_step_pre(step.old_u, cpu_id) && unmap_4k_tlb_flush_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_1g_flush_step_pre(step.old_u, cpu_id) && unmap_1g_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_1g_exit_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_1g_increased(step.old_u, step.new_u, thread.owning_container)
}

/// Refund steps and the exit step run after every page of the recorded range has been cleared and the flush has been recorded.
#[verifier::opaque]
pub open spec fn unmap_1g_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap1g
    &&& progress->Unmap1g_unmapped == progress->Unmap1g_range.len
    &&& progress->Unmap1g_flushed
}

/// Exiting clears unmap progress and unlocks the cpu, which leaves its kernel step for its trap path, its running thread, and the pagetable of the thread's process, which it write-holds.
#[verifier::opaque]
pub open spec fn unmap_1g_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& pagetable.lock_state == (LockStateU::WriteLocked { writer: cpu_id })
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after entering: the single enter step.
#[verifier::opaque]
pub open spec fn unmap_1g_trace_after_enter(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange1G) -> bool {
    &&& trace.len() == 1
    &&& unmap_1g_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_1g_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
}

/// The partial trace after unmapping the range: the enter step followed by one step per cleared leaf, flushed cpu TLB, recorded flush, or quota refund.
#[verifier::opaque]
pub open spec fn unmap_1g_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange1G) -> bool {
    // enter + one leaf per page + up to NUM_CPUS TLB flushes + flushed + up to MAX_CONTAINER_TREE_DEPTH + 1 refunds
    &&& range.len + 2 <= trace.len() <= range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 3
    &&& unmap_1g_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_1g_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> unmap_1g_range_step(trace[j], cpu_id)
}

/// The full trace of a successful unmap: one enter step; one step per cleared leaf, flushed cpu TLB, recorded flush, or quota refund; and one exit step.
#[verifier::opaque]
pub open spec fn unmap_1g_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let va_range = spec_va_range_1g(va, range);
    // enter + one leaf per page + up to NUM_CPUS TLB flushes + flushed + up to MAX_CONTAINER_TREE_DEPTH + 1 refunds + exit
    &&& range + 3 <= trace.len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4
    &&& unmap_1g_enter_step_pre(trace[0].old_u, cpu_id, va_range)
    &&& unmap_1g_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> unmap_1g_range_step(trace[j], cpu_id)
    &&& unmap_1g_exit_step_pre(trace.last().old_u, cpu_id)
    &&& unmap_1g_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}
} // verus!

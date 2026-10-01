use vstd::prelude::*;
use crate::*;

verus! {
/// The cpu, its running thread, the thread's process and pagetable, and its container are
/// write-locked.
pub open spec fn unmap_4k_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(thread_ptr)
    &&& thread.lock_state is WriteLocked
    &&& u.process_map.dom().contains(thread.owning_proc)
    &&& u.process_map.spec_index(thread.owning_proc).pagetable is Some
    &&& u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state is WriteLocked
    &&& u.process_map.spec_index(thread.owning_proc).lock_state is WriteLocked
    &&& u.container_map.dom().contains(thread.owning_container)
    &&& u.container_map.spec_index(thread.owning_container).lock_state is WriteLocked
}

/// A leaf step clears the next recorded VA, which is still mapped, before the flush.
#[verifier::opaque]
pub open spec fn unmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Unmap4k_range.view()[progress->Unmap4k_unmapped as int];
    &&& unmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped < progress->Unmap4k_range.len
    &&& !progress->Unmap4k_flushed
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k.dom().contains(va)
}

/// A leaf step removes the VA from the process's user mapping and advances unmap progress.
#[verifier::opaque]
pub open spec fn unmap_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let range = progress->Unmap4k_range;
    let unmapped = progress->Unmap4k_unmapped;
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            syscall_progress: Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }), ..thread
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.remove(range.view()[unmapped as int]), ..pagetable }), ..process
        }),
        ..old_u
    })
}

/// A flush step runs after every recorded VA has been cleared and before the flush is recorded.
#[verifier::opaque]
pub open spec fn unmap_4k_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& unmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
    &&& !progress->Unmap4k_flushed
}

/// Recording the flush changes only unmap progress.
#[verifier::opaque]
pub open spec fn unmap_4k_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let progress = thread.syscall_progress->Some_0;
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            syscall_progress: Some(SyscallProgress::Unmap4k { range: progress->Unmap4k_range, unmapped: progress->Unmap4k_unmapped, flushed: true }), ..thread
        }),
        ..old_u
    })
}

/// A refund step runs after the flush has been recorded.
#[verifier::opaque]
pub open spec fn unmap_4k_refund_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& unmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
    &&& progress->Unmap4k_flushed
}

/// A step inside the unmap range clears one leaf, flushes the process's PCID on one cpu, records the
/// flush, or refunds 4K quota to the thread's container chain.
#[verifier::opaque]
pub open spec fn unmap_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    ||| unmap_4k_leaf_step_pre(step.old_u, cpu_id) && unmap_4k_leaf_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && kernel_u_cpu_tlb_cleared(step.old_u, step.new_u, step.old_u.process_map.spec_index(thread.owning_proc).pcid)
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && unmap_4k_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_refund_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_4k_increased(step.old_u, step.new_u, thread.owning_container)
}
} // verus!

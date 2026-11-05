use vstd::prelude::*;
use crate::*;

verus! {
/// A leaf step clears the next VA of the recorded range, which is still mapped, before the flush.
#[verifier::opaque]
pub open spec fn unmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped < progress->Unmap4k_range.len
    &&& !progress->Unmap4k_flushed
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k.dom().contains(progress->Unmap4k_range.view()[progress->Unmap4k_unmapped as int])
}

/// A leaf step removes the next VA of the recorded range from the process's user mapping and advances unmap progress.
#[verifier::opaque]
pub open spec fn unmap_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let range = progress->Unmap4k_range;
    let unmapped = progress->Unmap4k_unmapped;
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.remove(range.view()[unmapped as int]), ..pagetable }), ..process }),
        ..old_u
    })
}

/// A flush step runs after every recorded VA has been cleared and before the flush is recorded, while the thread's
/// container exists.
#[verifier::opaque]
pub open spec fn unmap_4k_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
    &&& !progress->Unmap4k_flushed
}

/// A TLB flush step takes or keeps this cpu's read hold on the cpu set of the thread's container and clears at most one
/// TLB entry for the process's PCID.
#[verifier::opaque]
pub open spec fn unmap_4k_tlb_flush_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let locked = KernelU {
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: old_u.container_map.spec_index(thread.owning_container).cpu_set_lock.with_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    };
    new_u == locked || kernel_u_cpu_tlb_cleared(locked, new_u, old_u.process_map.spec_index(thread.owning_proc).pcid)
}

/// Recording the flush changes unmap progress and releases this cpu's read hold on the cpu set of the thread's container.
#[verifier::opaque]
pub open spec fn unmap_4k_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let cpu_set_lock = old_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap4k { range: progress->Unmap4k_range, unmapped: progress->Unmap4k_unmapped, flushed: true }), ..thread }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// A refund step, and the exit step, run after every page of the recorded range has been cleared and the flush has been
/// recorded.
#[verifier::opaque]
pub open spec fn unmap_4k_refund_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
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
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && unmap_4k_tlb_flush_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && unmap_4k_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_refund_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_4k_increased(step.old_u, step.new_u, thread.owning_container)
}
} // verus!

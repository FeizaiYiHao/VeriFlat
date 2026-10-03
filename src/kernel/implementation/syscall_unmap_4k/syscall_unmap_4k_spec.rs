use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_unmap_4k` from the state at entry, in the implementation's check order:
/// malformed arguments, a killed container, process, or caller, and then a range below the first user
/// L4 index or with a page that has no present 4K leaf.
pub open spec fn unmap_4k_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k;
    let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
    if range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) { RetValueType::Error }
    else if pre.container_map[thread.owning_container].killed { RetValueType::ErrorContainerKilled }
    else if pre.process_map[thread.owning_proc].killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if user_va_range(pre, va_range) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(va_range.view()[j]) && mapping[va_range.view()[j]].present {
        RetValueType::Success
    } else { RetValueType::Error }
}

/// The cpu runs a live thread of a live process and container with no multi-step syscall in
/// progress; the cpu, the thread, its process, pagetable, and container are unlocked; and every VA
/// of the valid, non-empty user range is mapped.
#[verifier::opaque]
pub open spec fn unmap_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let container = old_u.container_map.spec_index(thread.owning_container);
    let pagetable = process.pagetable->Some_0;
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
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& container.lock_state is Unlocked
    &&& !container.killed
    &&& range.wf()
    &&& range.len > 0
    &&& user_va_range(old_u, range)
    &&& forall|i: int| #![trigger pagetable.mapping_4k.dom().contains(range.view()[i])] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
}

/// Entering write-locks the cpu, its running thread, and the thread's process, pagetable, and
/// container and starts progress at the first page.
#[verifier::opaque]
pub open spec fn unmap_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Unmap4k { range, unmapped: 0, flushed: false };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU {
            lock_state: LockStateU::WriteLocked, ..old_u.container_map.spec_index(thread.owning_container)
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::WriteLocked, pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.pagetable->Some_0 }), ..process
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        ..old_u
    })
}

/// Exiting happens after every page of the recorded range has been cleared and the flush has been
/// recorded.
#[verifier::opaque]
pub open spec fn unmap_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& unmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
    &&& progress->Unmap4k_flushed
}

/// Exiting clears unmap progress and unlocks the cpu, its running thread, and the thread's process,
/// pagetable, and container.
#[verifier::opaque]
pub open spec fn unmap_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU {
            lock_state: LockStateU::Unlocked, ..old_u.container_map.spec_index(thread.owning_container)
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.pagetable->Some_0 }), ..process
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
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
    &&& range.len + 2 <= trace.len() <= range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 3
    &&& unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> unmap_4k_range_step(trace[j], cpu_id)
}

/// The full trace of a successful unmap: one enter step; one step per cleared leaf, flushed cpu
/// TLB, recorded flush, or quota refund; and one exit step.
#[verifier::opaque]
pub open spec fn unmap_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
    &&& range + 3 <= trace.len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4
    &&& unmap_4k_enter_step_pre(trace[0].old_u, cpu_id, va_range)
    &&& unmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> unmap_4k_range_step(trace[j], cpu_id)
    &&& unmap_4k_exit_step_pre(trace.last().old_u, cpu_id)
    &&& unmap_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}
} // verus!

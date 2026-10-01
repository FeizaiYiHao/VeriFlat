use vstd::prelude::*;
use crate::*;

verus! {
/// User-visible and physical result of a successful anonymous 4K mmap.
pub open spec fn mmap_4k_syscall_range_mapped(pagetable: PageTable<PT_TYPE>, va: VAddr, len: usize) -> bool {
    forall|i: usize|
        #![trigger pagetable.mapping_4k().dom().contains(spec_va_add_range(va, i))]
        i < len ==> {
            let mapped_va = spec_va_add_range(va, i);
            &&& pagetable.mapping_4k().dom().contains(mapped_va)
            &&& pagetable.mapping_4k().spec_index(mapped_va).present
            &&& pagetable.mapping_4k().spec_index(mapped_va).write
            &&& !pagetable.mapping_4k().spec_index(mapped_va).execute_disable
        }
}

/// The page-aligned VA sequence requested by `syscall_mmap_4k`.
pub open spec fn mmap_4k_syscall_va_range(va: VAddr, len: usize) -> VaRange4K {
    VaRange4K { start: va, len, view: Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize))) }
}

/// Publishing a leaf moves mmap progress to the next page with no directory installed.
pub open spec fn mmap_4k_progress_after_leaf(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap4k { range, mapped, directory: _ }) => Some(SyscallProgress::Mmap4k { range, mapped: (mapped + 1) as usize, directory: Mmap4kDirectory::None }),
        _ => progress,
    }
}

/// The cpu runs a live thread of an existing container with no multi-step syscall in progress; the
/// cpu, the thread, and its process's pagetable are unlocked; and the thread has four 4K quota per
/// page of a valid, non-empty user range none of whose VAs is covered by a 4K, 2M, or 1G leaf.
#[verifier::opaque]
pub open spec fn mmap_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let pagetable = old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& range.wf()
    &&& range.len > 0
    &&& user_va_range(old_u, range)
    &&& thread.quota_4k >= 4 * range.len
    &&& forall|i: int| #![trigger pagetable.mapping_4k.dom().contains(range.view()[i])] 0 <= i < range.len ==> !pagetable.mapping_4k.dom().contains(range.view()[i])
    &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> {
        let idx = spec_va2index(range.view()[i]);
        &&& !pagetable.mapping_2m.dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
        &&& !pagetable.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
    }
}

/// Entering write-locks the cpu, its running thread, and the thread's pagetable and starts progress
/// at the first page.
#[verifier::opaque]
pub open spec fn mmap_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Mmap4k { range, mapped: 0, directory: Mmap4kDirectory::None };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.pagetable->Some_0 }),
            ..process
        }),
        ..old_u
    })
}

/// A leaf step maps the next unmapped VA of the recorded range under the three mmap locks.
#[verifier::opaque]
pub open spec fn mmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int];
    &&& mmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Mmap4k
    &&& progress->Mmap4k_mapped < progress->Mmap4k_range.len
    &&& thread.quota_4k >= 1
    &&& !old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k.dom().contains(va)
}

/// A leaf page consumes one 4K quota and publishes a present, writable, executable mapping.
#[verifier::opaque]
pub open spec fn mmap_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int];
    let entry = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k.spec_index(va);
    &&& entry.present
    &&& entry.write
    &&& !entry.execute_disable
    &&& entry.owning_container.view() == thread.owning_container
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable }),
            ..process
        }),
        ..old_u
    })
}

/// Exiting happens after every page of the recorded range has been mapped.
#[verifier::opaque]
pub open spec fn mmap_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& mmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Mmap4k
    &&& progress->Mmap4k_mapped == progress->Mmap4k_range.len
    &&& progress->Mmap4k_directory is None
}

/// Exiting clears mmap progress and unlocks the cpu, its running thread, and the thread's pagetable.
#[verifier::opaque]
pub open spec fn mmap_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.pagetable->Some_0 }),
            ..process
        }),
        ..old_u
    })
}

/// A step inside the mmap loop installs one directory page or publishes one leaf.
#[verifier::opaque]
pub open spec fn mmap_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    ||| mmap_4k_directory_step_pre(step.old_u, cpu_id) && mmap_4k_directory_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_4k_leaf_step_pre(step.old_u, cpu_id) && mmap_4k_leaf_step(step.old_u, step.new_u, cpu_id)
}

/// The partial trace after entering: the single enter step.
#[verifier::opaque]
pub open spec fn mmap_4k_trace_after_enter(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K) -> bool {
    &&& trace.len() == 1
    &&& mmap_4k_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& mmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
}

/// The partial trace after mapping the range: the enter step followed by one directory or leaf step
/// per recorded mutation.
#[verifier::opaque]
pub open spec fn mmap_4k_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K) -> bool {
    &&& range.len + 1 <= trace.len() <= 4 * range.len + 1
    &&& mmap_4k_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& mmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> mmap_4k_range_step(trace[j], cpu_id)
}

/// The full trace of a successful mmap: one enter step, one directory or leaf step per recorded
/// mutation, and one exit step.
#[verifier::opaque]
pub open spec fn mmap_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    &&& range + 2 <= trace.len() <= 4 * range + 2
    &&& mmap_4k_enter_step_pre(trace[0].old_u, cpu_id, mmap_4k_syscall_va_range(va, range))
    &&& mmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, mmap_4k_syscall_va_range(va, range))
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> mmap_4k_range_step(trace[j], cpu_id)
    &&& mmap_4k_exit_step_pre(trace.last().old_u, cpu_id)
    &&& mmap_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}

/// A successful mmap maps every page of the requested range in the current process's pagetable.
pub open spec fn mmap_4k_syscall_success_mapped(pre: &KernelK, post: &KernelK, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let process_ptr = pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
    let pagetable_ptr = pre.prc_mp.spec_index(process_ptr).view().pagetable;
    &&& range > 0
    &&& va_4k_valid(va)
    &&& post.pt_mp.dom().contains(pagetable_ptr)
    &&& mmap_4k_syscall_range_mapped(post.pt_mp.spec_index(pagetable_ptr).view(), va, range)
}
} // verus!

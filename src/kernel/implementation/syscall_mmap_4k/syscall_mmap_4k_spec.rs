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
        None => None,
    }
}

/// The cpu, the running thread, and its process's pagetable are all unlocked, and the thread has
/// no multi-step syscall in progress.
pub open spec fn mmap_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr) -> bool {
    let process_ptr = old_u.thread_map.spec_index(thread_ptr).owning_proc;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array[cpu_id as int].lock_state is Unlocked
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& old_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
    &&& old_u.thread_map.spec_index(thread_ptr).syscall_progress is None
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.process_map.spec_index(process_ptr).pagetable is Some
    &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.lock_state is Unlocked
}

/// Entering write-locks the cpu, thread, and pagetable and starts progress at the first page.
pub open spec fn mmap_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, range: VaRange4K) -> bool {
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
pub open spec fn mmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr) -> bool {
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int];
    &&& mmap_4k_locked(old_u, cpu_id, thread_ptr)
    &&& thread.syscall_progress is Some
    &&& progress->Mmap4k_mapped < progress->Mmap4k_range.len
    &&& thread.quota_4k >= 1
    &&& !old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k.dom().contains(va)
}

/// A leaf page consumes one 4K quota and publishes a present, writable, executable mapping.
pub open spec fn mmap_4k_leaf_step(old_u: KernelU, new_u: KernelU, thread_ptr: RwLockThreadPtr) -> bool {
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
pub open spec fn mmap_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr) -> bool {
    let progress = old_u.thread_map.spec_index(thread_ptr).syscall_progress->Some_0;
    &&& mmap_4k_locked(old_u, cpu_id, thread_ptr)
    &&& old_u.thread_map.spec_index(thread_ptr).syscall_progress is Some
    &&& progress->Mmap4k_mapped == progress->Mmap4k_range.len
    &&& progress->Mmap4k_directory is None
}

/// Exiting clears mmap progress and unlocks the cpu, thread, and pagetable.
pub open spec fn mmap_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr) -> bool {
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
pub open spec fn mmap_4k_range_step(step: KernelStep, cpu_id: CpuId, thread_ptr: RwLockThreadPtr) -> bool {
    ||| mmap_4k_directory_step_pre(step.old_u, cpu_id, thread_ptr) && mmap_4k_directory_step(step.old_u, step.new_u, thread_ptr)
    ||| mmap_4k_leaf_step_pre(step.old_u, cpu_id, thread_ptr) && mmap_4k_leaf_step(step.old_u, step.new_u, thread_ptr)
}

/// The full trace of a successful mmap: one enter step, one directory or leaf step per recorded
/// mutation, and one exit step.
pub open spec fn mmap_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, va: VAddr, range: usize) -> bool {
    &&& range + 2 <= trace.len() <= 4 * range + 2
    &&& mmap_4k_enter_step_pre(trace[0].old_u, cpu_id, thread_ptr)
    &&& mmap_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, thread_ptr, mmap_4k_syscall_va_range(va, range))
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> mmap_4k_range_step(trace[j], cpu_id, thread_ptr)
    &&& mmap_4k_exit_step_pre(trace.last().old_u, cpu_id, thread_ptr)
    &&& mmap_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id, thread_ptr)
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

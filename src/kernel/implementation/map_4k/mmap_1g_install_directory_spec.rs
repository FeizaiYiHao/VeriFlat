use vstd::prelude::*;
use crate::*;

verus! {
/// Installing the L3 directory page for the next 1G page records it in mmap progress and leaves other progress unchanged.
pub open spec fn mmap_1g_progress_after_directory(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap1g { range, mapped, directory: _, hidden, flushed }) => Some(SyscallProgress::Mmap1g { range, mapped, directory: true, hidden, flushed }),
        _ => progress,
    }
}

/// A directory step starts under the three mmap locks, before the recorded range is fully mapped and before the L3 page of the next 1G page is installed, with quota for one directory page.
#[verifier::opaque]
pub open spec fn mmap_1g_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped < progress->Mmap1g_range.len
    &&& !progress->Mmap1g_directory
    &&& thread.quota_4k >= 1
}

/// An L3 directory page consumes one 4K quota of the running thread and records the installed directory in its progress; it creates no window and changes no mapping.
#[verifier::opaque]
pub open spec fn mmap_1g_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_1g_progress_after_directory(thread.syscall_progress), ..thread }),
        ..old_u
    })
}
} // verus!

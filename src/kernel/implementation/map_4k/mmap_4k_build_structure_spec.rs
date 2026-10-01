use vstd::prelude::*;
use crate::*;
use super::mmap_4k_create_entry_install::MissingPageTableLevel;

verus! {
/// Directory levels are installed from L4 toward L2 for one 4K page.
pub open spec fn mmap_4k_directory_rank(directory: Mmap4kDirectory) -> nat {
    match directory {
        Mmap4kDirectory::None => 0,
        Mmap4kDirectory::L4 => 1,
        Mmap4kDirectory::L3 => 2,
        Mmap4kDirectory::L2 => 3,
    }
}

pub(super) open spec fn mmap_4k_installed_directory(level: MissingPageTableLevel) -> Mmap4kDirectory {
    match level {
        MissingPageTableLevel::L4 => Mmap4kDirectory::L4,
        MissingPageTableLevel::L3 => Mmap4kDirectory::L3,
        MissingPageTableLevel::L2 => Mmap4kDirectory::L2,
    }
}

/// Installing a directory records its level in mmap progress and leaves other progress unchanged.
pub(super) open spec fn mmap_4k_progress_after_directory(progress: Option<SyscallProgress>, level: MissingPageTableLevel) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap4k { range, mapped, directory: _ }) => Some(SyscallProgress::Mmap4k { range, mapped, directory: mmap_4k_installed_directory(level) }),
        _ => progress,
    }
}

/// The quota thread funds directory pages for its own container or for a
/// write-held direct child container that receives their ownership.
pub open spec fn mmap_4k_quota_thread_container_compatible(k: &KernelK, lctx: &LocalContext, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr) -> bool {
    let owner = k.thr_mp.spec_index(thread_ptr).view().owning_container;
    ||| owner == container_ptr
    ||| {
        &&& k.ctn_mp.dom().contains(container_ptr)
        &&& k.ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(owner)
        &&& typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write)
    }
}

/// The cpu's running thread, the cpu, and the pagetable of the thread's process are write-locked.
pub open spec fn mmap_4k_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let process_ptr = u.thread_map.spec_index(thread_ptr).owning_proc;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(thread_ptr)
    &&& u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
    &&& u.process_map.dom().contains(process_ptr)
    &&& u.process_map.spec_index(process_ptr).pagetable is Some
    &&& u.process_map.spec_index(process_ptr).pagetable->Some_0.lock_state is WriteLocked
}

/// A directory step starts under the three mmap locks, before the recorded range is fully mapped,
/// with quota for one directory page.
#[verifier::opaque]
pub open spec fn mmap_4k_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& mmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Mmap4k
    &&& progress->Mmap4k_mapped < progress->Mmap4k_range.len
    &&& thread.quota_4k >= 1
}

/// A directory page consumes one 4K quota and records a deeper installed level.
#[verifier::opaque]
pub open spec fn mmap_4k_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let progress = thread.syscall_progress->Some_0;
    let new_progress = new_u.thread_map.spec_index(thread_ptr).syscall_progress->Some_0;
    &&& new_u.thread_map.spec_index(thread_ptr).syscall_progress is Some
    &&& new_progress is Mmap4k
    &&& new_progress->Mmap4k_range == progress->Mmap4k_range
    &&& new_progress->Mmap4k_mapped == progress->Mmap4k_mapped
    &&& mmap_4k_directory_rank(progress->Mmap4k_directory) < mmap_4k_directory_rank(new_progress->Mmap4k_directory)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: Some(new_progress), ..thread }),
        ..old_u
    })
}
} // verus!

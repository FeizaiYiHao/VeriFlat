use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure::MissingPageTableLevel;

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

/// The directory level recorded in mmap or share progress once the page for `level`, the first absent entry of a 4K walk,
/// is installed.
pub open spec fn mmap_4k_installed_directory(level: MissingPageTableLevel) -> Mmap4kDirectory {
    match level {
        MissingPageTableLevel::L4 => Mmap4kDirectory::L4,
        MissingPageTableLevel::L3 => Mmap4kDirectory::L3,
        MissingPageTableLevel::L2 => Mmap4kDirectory::L2,
    }
}

/// Installing a directory records its level in mmap progress and leaves other progress unchanged.
pub open spec fn mmap_4k_progress_after_directory(progress: Option<SyscallProgress>, level: MissingPageTableLevel) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap4k { range, mapped, directory: _, phase }) => Some(SyscallProgress::Mmap4k { range, mapped, directory: mmap_4k_installed_directory(level), phase }),
        _ => progress,
    }
}

/// The quota thread funds directory pages for its own container or for a
/// write-held direct child container that receives their ownership.
pub open spec fn mmap_4k_quota_thread_container_compatible(k: &KernelK, lctx: &LocalContext, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr) -> bool {
    let owner = k.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    ||| owner == ctn_ptr
    ||| {
        &&& k.ctn_mp.dom().contains(ctn_ptr)
        &&& k.ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent == Some(owner)
        &&& typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write)
    }
}

/// A directory step starts under the three mmap locks, before the recorded range is fully mapped,
/// with quota for one directory page.
#[verifier::opaque]
pub open spec fn mmap_4k_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Mmap4k
    &&& progress->Mmap4k_mapped < progress->Mmap4k_range.len
    &&& thread.quota_4k >= 1
}

/// A directory page consumes one 4K quota and records its level in the same phase: an L4 or L3 directory
/// while filling, and a deeper level than the last recorded one otherwise. A new L2 page adds its windows to
/// the table, those of the recorded range held.
#[verifier::opaque]
pub open spec fn mmap_4k_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let dir = new_u.thread_map.spec_index(thrd_ptr).syscall_progress->Some_0->Mmap4k_directory;
    let new_progress = SyscallProgress::Mmap4k { range: progress->Mmap4k_range, mapped: progress->Mmap4k_mapped, directory: dir, phase: progress->Mmap4k_phase };
    let process = old_u.process_map[thread.owning_proc];
    let table = process.pagetable->Some_0;
    let old_windows = table.pagetable_window_locks;
    let new_windows = new_u.process_map[thread.owning_proc].pagetable->Some_0.pagetable_window_locks;
    &&& progress->Mmap4k_phase is Fill ==> dir is L4 || dir is L3
    &&& !(progress->Mmap4k_phase is Fill) ==> mmap_4k_directory_rank(progress->Mmap4k_directory) < mmap_4k_directory_rank(dir)
    &&& dir is L3 ==> !new_windows.dom().subset_of(old_windows.dom())
    &&& dir is L3 ==> forall|w: WindowVa| #![trigger new_windows.dom().contains(w)] new_windows.dom().contains(w) && !old_windows.dom().contains(w)
        ==> new_windows == pagetable_window_locks_after_new_l2_page(old_windows, spec_v2l4index(w.va), spec_v2l3index(w.va), progress->Mmap4k_range, cpu_id)
    &&& !(dir is L3) ==> new_windows == old_windows
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: Some(new_progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: new_windows, ..table }), ..process }),
        ..old_u
    })
}

/// Installing an L4 or L3 directory for a 2M page records that level in mmap progress and leaves other progress unchanged.
pub open spec fn mmap_2m_progress_after_directory(progress: Option<SyscallProgress>, level: MissingPageTableLevel) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap2m { range, mapped, directory: _, phase, flushed }) => Some(SyscallProgress::Mmap2m { range, mapped, directory: if level is L4 { Mmap2mDirectory::L4 } else { Mmap2mDirectory::L3 }, phase, flushed }),
        _ => progress,
    }
}

/// A directory step starts in the fill phase under the three mmap locks, before the recorded range is fully mapped, with
/// quota for one directory page.
#[verifier::opaque]
pub open spec fn mmap_2m_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Mmap2m
    &&& progress->Mmap2m_phase is Fill
    &&& progress->Mmap2m_mapped < progress->Mmap2m_range.len
    &&& thread.quota_4k >= 1
}

/// A directory page consumes one 4K quota and records an L4 or L3 directory in the same phase. A new L2 page adds its windows
/// to the table, those of the recorded range held.
#[verifier::opaque]
pub open spec fn mmap_2m_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let dir = new_u.thread_map.spec_index(thrd_ptr).syscall_progress->Some_0->Mmap2m_directory;
    let new_progress = SyscallProgress::Mmap2m { range: progress->Mmap2m_range, mapped: progress->Mmap2m_mapped, directory: dir, phase: progress->Mmap2m_phase, flushed: progress->Mmap2m_flushed };
    let process = old_u.process_map[thread.owning_proc];
    let table = process.pagetable->Some_0;
    let old_windows = table.pagetable_window_locks;
    let new_windows = new_u.process_map[thread.owning_proc].pagetable->Some_0.pagetable_window_locks;
    &&& dir is L4 || dir is L3
    &&& dir is L3 ==> !new_windows.dom().subset_of(old_windows.dom())
    &&& dir is L3 ==> forall|w: WindowVa| #![trigger new_windows.dom().contains(w)] new_windows.dom().contains(w) && !old_windows.dom().contains(w)
        ==> new_windows == pagetable_window_locks_after_new_l2_page(old_windows, spec_v2l4index(w.va), spec_v2l3index(w.va), progress->Mmap2m_range.covering_4k_range(), cpu_id)
    &&& !(dir is L3) ==> new_windows == old_windows
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: Some(new_progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: new_windows, ..table }), ..process }),
        ..old_u
    })
}

/// Holding write-locks the cpu and its running thread with the cpu inside its kernel step and changes
/// nothing else, when reading found a 2M window of the range missing and the call keeps both locks to
/// fill.
#[verifier::opaque]
pub open spec fn mmap_4k_hold_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..old_u.thread_map.spec_index(thrd_ptr) }),
        ..old_u
    })
}

/// Releasing happens with the cpu and its running thread write-locked and no mmap progress recorded.
#[verifier::opaque]
pub open spec fn mmap_4k_release_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is None
}

/// Releasing unlocks the cpu and its running thread, returns the cpu to its trap path, and changes
/// nothing else, when the fill section rejected the range.
#[verifier::opaque]
pub open spec fn mmap_4k_release_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thrd_ptr) }),
        ..old_u
    })
}
} // verus!

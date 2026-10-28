use vstd::prelude::*;
use crate::*;

verus! {
/// User-visible and physical result of a successful anonymous 4K mmap.
pub open spec fn mmap_4k_syscall_range_mapped(pagetable: PageTableC<PT_TYPE>, va: VAddr, len: usize) -> bool {
    forall|i: usize| #![trigger pagetable.mapping_4k().dom().contains(spec_va_add_range(va, i))] i < len ==> {
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

/// The result of `syscall_mmap_4k` from the state at entry, in the implementation's check order:
/// malformed arguments, a killed caller, less than four 4K quota per page, a range below the first user
/// L4 index, and then either a 4K leaf in the range's index interval or a range page covered by a 4K,
/// 2M, or 1G leaf.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn mmap_4k_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let pagetable = pre.process_map[thread.owning_proc].pagetable->Some_0;
    let va_range = mmap_4k_syscall_va_range(va, range);
    let start = spec_va2index(va);
    let end = spec_va2index(va_range.view()[range - 1]);
    if range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.quota_4k < 4 * range { RetValueType::ErrorNoQuota }
    else if !user_va_range(pre, va_range) { RetValueType::Error }
    else if (forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
        pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(start, (l4i, l3i, l2i, l1i)) && spec_l4_index_path_le((l4i, l3i, l2i, l1i), end)
        ==> !pagetable.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))) && (forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> {
            let idx = spec_va2index(va_range.view()[j]);
            &&& !pagetable.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            &&& !pagetable.mapping_2m.dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
            &&& !pagetable.mapping_4k.dom().contains(va_range.view()[j])
        }) { RetValueType::Success }
    else { RetValueType::ErrorVaInUse }
}

/// Publishing a leaf moves mmap progress to the next page with no directory installed.
pub open spec fn mmap_4k_progress_after_leaf(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap4k { range, mapped, directory: _, phase }) => Some(SyscallProgress::Mmap4k { range, mapped: (mapped + 1) as usize, directory: Mmap4kDirectory::None, phase }),
        _ => progress,
    }
}

/// The cpu runs a live thread of an existing container with no multi-step syscall in progress; to
/// read, the cpu and the thread are unlocked and its process's pagetable is not write-locked, and to
/// fill, the cpu and the thread are write-locked since the hold step and the pagetable is unlocked;
/// and the thread has four 4K quota per page of a valid, non-empty user range none of whose VAs is
/// covered by a 4K, 2M, or 1G leaf.
#[verifier::opaque]
pub open spec fn mmap_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K, phase: Mmap4kPhase) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let pagetable = old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable is Some
    &&& !(phase is Filled)
    &&& phase is Read ==> cpu.lock_state is Unlocked && thread.lock_state is Unlocked && !(pagetable.lock_state is WriteLocked)
    &&& phase is Fill ==> cpu.lock_state is WriteLocked && thread.lock_state is WriteLocked && pagetable.lock_state is Unlocked
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

/// Entering write-locks the cpu and its running thread, which entering to fill already holds, with
/// the cpu inside its kernel step, read-locks the thread's pagetable to read or write-locks it to
/// fill, and starts progress in that phase at the first page.
#[verifier::opaque]
pub open spec fn mmap_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, phase: Mmap4kPhase) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Mmap4k { range, mapped: 0, directory: Mmap4kDirectory::None, phase };
    let table_lock = if phase is Read { LockStateU::ReadLocked } else { LockStateU::WriteLocked };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: table_lock, ..process.pagetable->Some_0 }), ..process }),
        ..old_u
    })
}

/// The cpu runs a live thread of an existing container with no multi-step syscall in progress; the
/// cpu and the thread are unlocked, the thread's process has a pagetable, and the thread has four 4K
/// quota per page of a valid, non-empty user range.
#[verifier::opaque]
pub open spec fn mmap_4k_hold_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
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
    &&& range.wf()
    &&& range.len > 0
    &&& user_va_range(old_u, range)
    &&& thread.quota_4k >= 4 * range.len
}

/// Holding write-locks the cpu and its running thread with the cpu inside its kernel step and changes
/// nothing else, when reading found a 2M window of the range missing and the call keeps both locks to
/// fill.
#[verifier::opaque]
pub open spec fn mmap_4k_hold_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..old_u.thread_map.spec_index(thread_ptr) }),
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
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) }),
        ..old_u
    })
}

/// Downgrading happens in the fill phase under the mmap locks with the pagetable write-locked.
#[verifier::opaque]
pub open spec fn mmap_4k_downgrade_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& mmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Mmap4k
    &&& progress->Mmap4k_phase is Fill
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state is WriteLocked
}

/// Downgrading turns the pagetable's write lock into a read lock and moves progress to the filled
/// phase with no directory installed.
#[verifier::opaque]
pub open spec fn mmap_4k_downgrade_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = thread.syscall_progress->Some_0;
    let filled = SyscallProgress::Mmap4k { range: progress->Mmap4k_range, mapped: progress->Mmap4k_mapped, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Filled };
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(filled), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..process.pagetable->Some_0 }), ..process }),
        ..old_u
    })
}

/// A leaf step maps the next unmapped VA of the recorded range under the three mmap locks, outside
/// the fill phase.
#[verifier::opaque]
pub open spec fn mmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int];
    &&& mmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Mmap4k
    &&& !(progress->Mmap4k_phase is Fill)
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
    &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
        ==> old_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr != entry.addr
    &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].iommu_table->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].iommu_table is Some && old_u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
        ==> old_u.process_map[p].iommu_table->Some_0.mapping_4k[v].addr != entry.addr
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable }), ..process }),
        ..old_u
    })
}

/// Exiting happens outside the fill phase after every page of the recorded range has been mapped.
#[verifier::opaque]
pub open spec fn mmap_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& mmap_4k_locked(old_u, cpu_id)
    &&& thread.syscall_progress is Some
    &&& progress is Mmap4k
    &&& !(progress->Mmap4k_phase is Fill)
    &&& progress->Mmap4k_mapped == progress->Mmap4k_range.len
    &&& progress->Mmap4k_directory is None
}

/// Exiting clears mmap progress, unlocks the cpu and its running thread, returns the cpu to its trap
/// path, and drops the thread's read lock on its pagetable, which other readers may still hold.
#[verifier::opaque]
pub open spec fn mmap_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let table_lock = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state;
    &&& table_lock is Unlocked || table_lock is ReadLocked
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: table_lock, ..process.pagetable->Some_0 }), ..process }),
        ..old_u
    })
}

/// A step inside the mmap loop installs one directory page, downgrades the pagetable lock, or
/// publishes one leaf.
#[verifier::opaque]
pub open spec fn mmap_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    ||| mmap_4k_directory_step_pre(step.old_u, cpu_id) && mmap_4k_directory_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_4k_downgrade_step_pre(step.old_u, cpu_id) && mmap_4k_downgrade_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_4k_leaf_step_pre(step.old_u, cpu_id) && mmap_4k_leaf_step(step.old_u, step.new_u, cpu_id)
}

/// The partial trace after holding: the single hold step.
#[verifier::opaque]
pub open spec fn mmap_4k_trace_after_hold(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K) -> bool {
    &&& trace.len() == 1
    &&& mmap_4k_hold_step_pre(trace[0].old_u, cpu_id, range)
    &&& mmap_4k_hold_step(trace[0].old_u, trace[0].new_u, cpu_id)
}

/// The partial trace after entering in `phase`: the enter step, preceded by the hold step when
/// entering to fill.
#[verifier::opaque]
pub open spec fn mmap_4k_trace_after_enter(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K, phase: Mmap4kPhase) -> bool {
    let e: int = if phase is Fill { 1 } else { 0 };
    &&& trace.len() == e + 1
    &&& phase is Fill ==> mmap_4k_hold_step_pre(trace[0].old_u, cpu_id, range) && mmap_4k_hold_step(trace[0].old_u, trace[0].new_u, cpu_id)
    &&& mmap_4k_enter_step_pre(trace[e].old_u, cpu_id, range, phase)
    &&& mmap_4k_enter_step(trace[e].old_u, trace[e].new_u, cpu_id, range, phase)
}

/// The partial trace after mapping the range: the partial trace after entering in `phase` followed by
/// one directory, downgrade, or leaf step per recorded mutation.
#[verifier::opaque]
pub open spec fn mmap_4k_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K, phase: Mmap4kPhase) -> bool {
    let e: int = if phase is Fill { 1 } else { 0 };
    &&& e + range.len + 1 <= trace.len() <= e + 4 * range.len + 2
    &&& phase is Fill ==> mmap_4k_hold_step_pre(trace[0].old_u, cpu_id, range) && mmap_4k_hold_step(trace[0].old_u, trace[0].new_u, cpu_id)
    &&& mmap_4k_enter_step_pre(trace[e].old_u, cpu_id, range, phase)
    &&& mmap_4k_enter_step(trace[e].old_u, trace[e].new_u, cpu_id, range, phase)
    &&& forall|j: int| #![trigger trace[j]] e < j < trace.len() ==> mmap_4k_range_step(trace[j], cpu_id)
}

/// The full trace of a successful mmap entering in `phase`: one enter step to read, or a hold step and
/// an enter step to fill; one directory, downgrade, or leaf step per recorded mutation; and one exit step.
#[verifier::opaque]
pub open spec fn mmap_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize, phase: Mmap4kPhase) -> bool {
    let va_range = mmap_4k_syscall_va_range(va, range);
    let e: int = if phase is Fill { 1 } else { 0 };
    &&& e + range + 2 <= trace.len() <= e + 4 * range + 3
    &&& phase is Fill ==> mmap_4k_hold_step_pre(trace[0].old_u, cpu_id, va_range) && mmap_4k_hold_step(trace[0].old_u, trace[0].new_u, cpu_id)
    &&& mmap_4k_enter_step_pre(trace[e].old_u, cpu_id, va_range, phase)
    &&& mmap_4k_enter_step(trace[e].old_u, trace[e].new_u, cpu_id, va_range, phase)
    &&& forall|j: int| #![trigger trace[j]] e < j < trace.len() - 1 ==> mmap_4k_range_step(trace[j], cpu_id)
    &&& mmap_4k_exit_step_pre(trace.last().old_u, cpu_id)
    &&& mmap_4k_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}

/// The nonempty trace of a failed mmap: the hold step after reading found a 2M window of the range
/// missing, and the release step after the fill section rejected the range.
#[verifier::opaque]
pub open spec fn mmap_4k_syscall_failure_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    &&& trace.len() == 2
    &&& mmap_4k_hold_step_pre(trace[0].old_u, cpu_id, mmap_4k_syscall_va_range(va, range))
    &&& mmap_4k_hold_step(trace[0].old_u, trace[0].new_u, cpu_id)
    &&& mmap_4k_release_step_pre(trace[1].old_u, cpu_id)
    &&& mmap_4k_release_step(trace[1].old_u, trace[1].new_u, cpu_id)
}

/// A successful mmap maps every page of the requested range in the current process's pagetable.
pub open spec fn mmap_4k_syscall_success_mapped(post: &KernelK, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let process_ptr = post.cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
    let pagetable_ptr = post.prc_mp.spec_index(process_ptr).view().pagetable;
    &&& range > 0
    &&& va_4k_valid(va)
    &&& post.pt_mp.dom().contains(pagetable_ptr)
    &&& mmap_4k_syscall_range_mapped(pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr), va, range)
}
} // verus!

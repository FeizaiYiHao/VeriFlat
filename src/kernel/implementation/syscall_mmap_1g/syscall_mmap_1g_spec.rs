use vstd::prelude::*;
use crate::*;

verus! {
/// User-visible and physical result of a successful anonymous 1G mmap.
pub open spec fn mmap_1g_syscall_range_mapped(pagetable: WholePageTable<PT_TYPE>, va: VAddr, len: usize) -> bool {
    let range = mmap_1g_syscall_va_range(va, len);
    forall|j: int| #![trigger range.view()[j]] 0 <= j < len ==> {
        let mapped_va = range.view()[j];
        &&& pagetable.mapping_1g().dom().contains(mapped_va)
        &&& pagetable.mapping_1g().spec_index(mapped_va).present
        &&& pagetable.mapping_1g().spec_index(mapped_va).write
        &&& !pagetable.mapping_1g().spec_index(mapped_va).execute_disable
    }
}

/// The 1G-aligned VA sequence requested by `syscall_mmap_1g`.
pub open spec fn mmap_1g_syscall_va_range(va: VAddr, len: usize) -> VaRange1G { spec_va_range_1g(va, len) }

/// No 1G leaf maps the 1G slot at `va`, and no 2M or 4K leaf maps a VA inside it.
pub open spec fn mmap_1g_slot_unmapped(pagetable: PageTableU, va: VAddr) -> bool {
    let idx = spec_va2index(va);
    &&& !pagetable.mapping_1g.dom().contains(va)
    &&& forall|l2i: L2Index| #![trigger pagetable.mapping_2m.dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))] pei_valid(l2i)
        ==> !pagetable.mapping_2m.dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))
    &&& forall|l2i: L2Index, l1i: L1Index| #![trigger pagetable.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))] pei_valid(l2i) && pei_valid(l1i)
        ==> !pagetable.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))
}

/// The result of `syscall_mmap_1g` from the state at entry, in the implementation's check order: malformed arguments, a cpu no longer Running or marked by a killer, a killed caller, less than one 1G quota and one 4K quota per page, a range below the first user L4 index, and then a range
/// page whose 1G slot a 4K, 2M, or 1G leaf maps.
pub open spec fn mmap_1g_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let pagetable = pre.process_map[thread.owning_proc].pagetable->Some_0;
    let va_range = mmap_1g_syscall_va_range(va, range);
    if range == 0 || range > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - range * 0x40000000 || !spec_va_1g_range_valid(va, range) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.quota_1g < range || thread.quota_4k < range { RetValueType::ErrorNoQuota }
    else if !user_va_range(pre, va_range.covering_4k_range()) { RetValueType::Error }
    else if forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mmap_1g_slot_unmapped(pagetable, va_range.view()[j]) { RetValueType::Success }
    else { RetValueType::ErrorVaInUse }
}

/// Publishing a leaf moves mmap progress to the next page with no directory installed.
pub open spec fn mmap_1g_progress_after_leaf(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap1g { range, mapped, directory: _, hidden, flushed }) => Some(SyscallProgress::Mmap1g { range, mapped: (mapped + 1) as usize, directory: false, hidden, flushed }),
        _ => progress,
    }
}

/// The cpu runs a live thread of an existing container with no multi-step syscall in progress; the cpu, the thread, and the pagetable of the thread's process are unlocked; and the thread has one 1G quota and one 4K quota per page of a valid, non-empty user range none of whose 1G slots a
/// 4K, 2M, or 1G leaf maps.
#[verifier::opaque]
pub open spec fn mmap_1g_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange1G) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& process.pagetable is Some
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& pagetable.lock_state is Unlocked
    &&& range.wf()
    &&& range.len > 0
    &&& user_va_range(old_u, range.covering_4k_range())
    &&& thread.quota_1g >= range.len
    &&& thread.quota_4k >= range.len
    &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> mmap_1g_slot_unmapped(pagetable, range.view()[i])
}

/// Entering write-locks the cpu, with the cpu inside its kernel step, its running thread, and the thread's pagetable, and starts progress at the first page.
#[verifier::opaque]
pub open spec fn mmap_1g_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange1G) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let progress = SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: false, flushed: false };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..process.pagetable->Some_0 }), ..process
        }),
        ..old_u
    })
}

/// Hiding L3 entries of the range that link an L2 page happens under the three mmap locks before the first leaf and before the flush is recorded.
#[verifier::opaque]
pub open spec fn mmap_1g_hide_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped == 0
    &&& !progress->Mmap1g_flushed
}

/// Hiding drops windows under the range's 1G slots from the table's window locks, keeps every other window with its lock state, records the hide in progress, and changes nothing else.
#[verifier::opaque]
pub open spec fn mmap_1g_hide_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let table = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let range = progress->Mmap1g_range;
    let hidden = SyscallProgress::Mmap1g { range, mapped: progress->Mmap1g_mapped, directory: progress->Mmap1g_directory, hidden: true, flushed: progress->Mmap1g_flushed };
    let new_locks = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.pagetable_window_locks;
    &&& new_locks.dom().subset_of(table.pagetable_window_locks.dom())
    &&& forall|w: WindowVa| #![trigger table.pagetable_window_locks.dom().contains(w)] table.pagetable_window_locks.dom().contains(w)
        && !range.view().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), 0, 0))) ==> new_locks.dom().contains(w)
    &&& forall|w: WindowVa| #![trigger new_locks.dom().contains(w)] new_locks.dom().contains(w) ==> new_locks[w] == table.pagetable_window_locks[w]
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(hidden), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: new_locks, ..table }), ..process }),
        ..old_u
    })
}

/// Flushing the TLBs once after the hide and recording that flush happen under the three mmap locks before the first leaf and before the flush is recorded, in an existing container.
// The flush and its record share this pre: the steps differ by their bodies.
#[verifier::opaque]
pub open spec fn mmap_1g_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped == 0
    &&& progress->Mmap1g_hidden
    &&& !progress->Mmap1g_flushed
}

/// Recording the flush, while this cpu read-holds the cpu set of the thread's container, releases that read hold and marks the hidden L3 entries of the range flushed from every cpu, and changes nothing else.
#[verifier::opaque]
pub open spec fn mmap_1g_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let container = old_u.container_map.spec_index(thread.owning_container);
    let progress = thread.syscall_progress->Some_0;
    let flushed = SyscallProgress::Mmap1g { range: progress->Mmap1g_range, mapped: progress->Mmap1g_mapped, directory: progress->Mmap1g_directory, hidden: progress->Mmap1g_hidden, flushed: true };
    &&& container.cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(flushed), ..thread }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: container.cpu_set_lock.without_reader(cpu_id), ..container }),
        ..old_u
    })
}

/// Reclaiming an L1 or L2 page under a hidden L3 entry happens under the three mmap locks before the first leaf, after the flush was recorded, in an existing container.
#[verifier::opaque]
pub open spec fn mmap_1g_reclaim_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped == 0
    &&& progress->Mmap1g_flushed
}

/// A leaf step maps the next unmapped page of the recorded range, whose 1G slot no leaf maps, under the three mmap locks.
#[verifier::opaque]
pub open spec fn mmap_1g_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Mmap1g_range.view()[progress->Mmap1g_mapped as int];
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped < progress->Mmap1g_range.len
    &&& thread.quota_1g >= 1
    &&& mmap_1g_slot_unmapped(old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0, va)
}

/// A leaf page consumes one 1G quota and publishes a present, writable, executable 1G mapping of a frame that no other 1G mapping reaches and that contains no 2M, 4K, or IOMMU 4K frame.
#[verifier::opaque]
pub open spec fn mmap_1g_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let va = progress->Mmap1g_range.view()[progress->Mmap1g_mapped as int];
    let entry = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_1g.spec_index(va);
    &&& entry.present
    &&& entry.write
    &&& !entry.execute_disable
    &&& entry.owning_container.view() == thread.owning_container
    &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_1g[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
        ==> old_u.process_map[p].pagetable->Some_0.mapping_1g[v].addr != entry.addr
    &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_2m[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
        ==> !(entry.addr <= old_u.process_map[p].pagetable->Some_0.mapping_2m[v].addr < entry.addr + 0x40000000)
    &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
        ==> !(entry.addr <= old_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr < entry.addr + 0x40000000)
    &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].iommu_table->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].iommu_table is Some && old_u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
        ==> !(entry.addr <= old_u.process_map[p].iommu_table->Some_0.mapping_4k[v].addr < entry.addr + 0x40000000)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { quota_1g: (thread.quota_1g - 1) as usize, syscall_progress: mmap_1g_progress_after_leaf(thread.syscall_progress), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { mapping_1g: pagetable.mapping_1g.insert(va, entry), ..pagetable }), ..process }),
        ..old_u
    })
}

/// Exiting happens under the three mmap locks after every page of the recorded range has been mapped.
#[verifier::opaque]
pub open spec fn mmap_1g_exit_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.lock_state is WriteLocked
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped == progress->Mmap1g_range.len
    &&& !progress->Mmap1g_directory
}

/// Exiting clears mmap progress, unlocks the cpu, its running thread, and the thread's pagetable, and returns the cpu to its trap path.
#[verifier::opaque]
pub open spec fn mmap_1g_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.pagetable->Some_0 }), ..process
        }),
        ..old_u
    })
}

/// A step inside the mmap loop hides L3 entries of the range that link an L2 page, flushes the TLBs after the hides, records the flush, credits one reclaimed L1 or L2 page's 4K quota to a single container, the thread's container or one of its ancestors, installs one L3 directory page, or
/// publishes one leaf.
#[verifier::opaque]
pub open spec fn mmap_1g_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    ||| mmap_1g_hide_step_pre(step.old_u, cpu_id) && mmap_1g_hide_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_1g_flush_step_pre(step.old_u, cpu_id) && unmap_4k_tlb_flush_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_1g_flush_step_pre(step.old_u, cpu_id) && mmap_1g_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_1g_reclaim_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_4k_increased(step.old_u, step.new_u, thread.owning_container)
    ||| mmap_1g_directory_step_pre(step.old_u, cpu_id) && mmap_1g_directory_step(step.old_u, step.new_u, cpu_id)
    ||| mmap_1g_leaf_step_pre(step.old_u, cpu_id) && mmap_1g_leaf_step(step.old_u, step.new_u, cpu_id)
}

/// The partial trace after entering: the single enter step.
#[verifier::opaque]
pub open spec fn mmap_1g_trace_after_enter(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange1G) -> bool {
    &&& trace.len() == 1
    &&& mmap_1g_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& mmap_1g_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
}

/// The partial trace after mapping the range: the enter step followed by one range step per recorded mutation: one hide, 513 reclaimed table pages, and one directory page per page, one TLB flush per cpu and its record, and one leaf per page.
#[verifier::opaque]
pub open spec fn mmap_1g_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, range: VaRange1G) -> bool {
    &&& range.len + 1 <= trace.len() <= 516 * range.len + NUM_CPUS + 2
    &&& mmap_1g_enter_step_pre(trace[0].old_u, cpu_id, range)
    &&& mmap_1g_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> mmap_1g_range_step(trace[j], cpu_id)
}

/// The full trace of a successful mmap: one enter step, one range step per recorded mutation, and one exit step.
#[verifier::opaque]
pub open spec fn mmap_1g_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let va_range = mmap_1g_syscall_va_range(va, range);
    // The range-trace bound plus the exit step.
    &&& range + 2 <= trace.len() <= 516 * range + NUM_CPUS + 3
    &&& mmap_1g_enter_step_pre(trace[0].old_u, cpu_id, va_range)
    &&& mmap_1g_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va_range)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() - 1 ==> mmap_1g_range_step(trace[j], cpu_id)
    &&& mmap_1g_exit_step_pre(trace.last().old_u, cpu_id)
    &&& mmap_1g_exit_step(trace.last().old_u, trace.last().new_u, cpu_id)
}

/// A successful mmap maps every page of the requested range in the current process's pagetable.
pub open spec fn mmap_1g_syscall_success_mapped(post: &KernelK, cpu_id: CpuId, va: VAddr, range: usize) -> bool {
    let prc_ptr = post.cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
    let pagetable_ptr = post.prc_mp.spec_index(prc_ptr).view().pagetable;
    &&& range > 0
    &&& va_1g_valid(va)
    &&& post.pt_mp.dom().contains(pagetable_ptr)
    &&& mmap_1g_syscall_range_mapped(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr), va, range)
}
} // verus!

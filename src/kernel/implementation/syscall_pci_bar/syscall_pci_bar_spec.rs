use vstd::prelude::*;
use crate::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::{unmap_4k_spec::unmap_4k_tlb_flush_step, mmap_4k_build_structure_spec::
    {map_pci_bar_4k_directory_step_pre, map_pci_bar_4k_directory_step, map_pci_bar_2m_directory_step_pre, map_pci_bar_2m_directory_step}};
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::{unmap_4k_spec::unmap_4k_tlb_flush_step, mmap_4k_build_structure_spec::
    {map_pci_bar_4k_directory_step_pre, map_pci_bar_4k_directory_step, map_pci_bar_2m_directory_step_pre, map_pci_bar_2m_directory_step}};

verus! {
/// No 1G, 2M, or 4K leaf of `pagetable` covers the 4K page `va`.
pub open spec fn pci_bar_va_4k_unmapped(pagetable: PageTableU, va: VAddr) -> bool {
    let idx = spec_va2index(va);
    &&& !pagetable.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
    &&& !pagetable.mapping_2m.dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
    &&& !pagetable.mapping_4k.dom().contains(va)
}

/// The result of `syscall_map_pci_bar_4k` from the state at entry, in the implementation's check order: a malformed `va`, an idle or
/// killed cpu, a killed caller, a BAR slot or page index naming no 4K page, a BAR function the caller's process does not own, a
/// covered `va`, and less than mmap's four 4K quota for one page.
pub open spec fn map_pci_bar_4k_syscall_result(pre: KernelU, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let pagetable = pre.process_map[thread.owning_proc].pagetable->Some_0;
    if !spec_va_4k_valid(va) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if slot >= pre.pci_bars.len() || pre.pci_bars[slot as int].spec_page_4k(page_index) is None { RetValueType::ErrorPciBarSlotInvalid }
    else if !pagetable.pci_functions.dom().contains(pre.pci_bars[slot as int].bdf) { RetValueType::ErrorPciOwnerMismatch }
    else if !pci_bar_va_4k_unmapped(pagetable, va) { RetValueType::ErrorVaInUse }
    else if thread.quota_4k < 4 { RetValueType::ErrorNoQuota }
    else { RetValueType::Success }
}

/// No 1G or 2M leaf covers the 2M window at `va` and no 4K leaf maps a VA inside it.
pub open spec fn pci_bar_va_2m_unmapped(pagetable: PageTableU, va: VAddr) -> bool {
    let idx = spec_va2index(va);
    &&& !pagetable.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
    &&& !pagetable.mapping_2m.dom().contains(va)
    &&& forall|l1i: L1Index| #![trigger pagetable.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))] pei_valid(l1i)
        ==> !pagetable.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))
}

/// The result of `syscall_map_pci_bar_2m` from the state at entry, in the implementation's check order: a malformed `va`, an idle or
/// killed cpu, a killed caller, a BAR slot or chunk index naming no 2M chunk, a BAR function the caller's process does not own, a 2M
/// window of `va` a leaf maps into, and less than mmap's two 4K quota for one 2M page.
pub open spec fn map_pci_bar_2m_syscall_result(pre: KernelU, cpu_id: CpuId, slot: usize, index: usize, va: VAddr) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let pagetable = pre.process_map[thread.owning_proc].pagetable->Some_0;
    if !spec_va_2m_valid(va) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if slot >= pre.pci_bars.len() || pre.pci_bars[slot as int].spec_chunk_2m(index) is None { RetValueType::ErrorPciBarSlotInvalid }
    else if !pagetable.pci_functions.dom().contains(pre.pci_bars[slot as int].bdf) { RetValueType::ErrorPciOwnerMismatch }
    else if !pci_bar_va_2m_unmapped(pagetable, va) { RetValueType::ErrorVaInUse }
    else if thread.quota_4k < 2 { RetValueType::ErrorNoQuota }
    else { RetValueType::Success }
}

/// The 2M chunk `index` of BAR table slot `slot` in `pre`.
pub open spec fn map_pci_bar_2m_chunk(pre: KernelU, slot: usize, index: usize) -> PAddr { pre.pci_bars[slot as int].spec_chunk_2m(index)->0 }

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu, the thread, and the pagetable of the thread's process
/// are unlocked; the thread's container exists; BAR table slot `slot` has the 2M chunk `index`; the process owns the slot's function;
/// no leaf maps into the 2M window of `va`; and the thread has mmap's two 4K quota for one 2M page.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_enter_step_pre(old_u: KernelU, cpu_id: CpuId, slot: usize, index: usize, va: VAddr) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& spec_va_2m_valid(va)
    &&& slot < old_u.pci_bars.len()
    &&& old_u.pci_bars[slot as int].spec_chunk_2m(index) is Some
    &&& pagetable.pci_functions.dom().contains(old_u.pci_bars[slot as int].bdf)
    &&& pci_bar_va_2m_unmapped(pagetable, va)
    &&& thread.quota_4k >= 2
}

/// Entering write-locks the cpu, which enters its kernel step, its running thread, the pagetable of the thread's process, and the 2M
/// window of `va` when it exists, and starts the progress of mapping `va` with no directory installed and nothing flushed.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let locked = LockStateU::WriteLocked { writer: cpu_id };
    let windows = if pagetable.pagetable_window_locks.dom().contains(window_of(va)) { pagetable.pagetable_window_locks.insert(window_of(va), locked) } else { pagetable.pagetable_window_locks };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: locked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: locked, pagetable_window_locks: windows, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            lock_state: locked, syscall_progress: Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: false }), ..thread
        }),
        ..old_u
    })
}

/// The exit step runs under the map locks while mapping `va` is in progress.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_exit_step_pre(old_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let pagetable = old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& thread.syscall_progress->Some_0 is MapPciBar2m
    &&& thread.syscall_progress->Some_0->MapPciBar2m_va == va
}

/// Exiting maps the 2M page `va` to the IO leaf `entry`, raises the mapped-BAR-page count of the BAR's function `f`, clears the
/// progress, and unlocks the 2M window of `va`, the cpu, which leaves its kernel step for its trap path, its running thread, and the
/// pagetable of the thread's process, which it write-holds.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, f: PciBdf, entry: MapEntry) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& pagetable.lock_state == (LockStateU::WriteLocked { writer: cpu_id })
    &&& pagetable.pci_functions.dom().contains(f)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU {
                lock_state: LockStateU::Unlocked, mapping_2m: pagetable.mapping_2m.insert(va, entry), pci_functions: pagetable.pci_functions.insert(f, (pagetable.pci_functions[f] + 1) as nat),
                pagetable_window_locks: pagetable_window_locks_after_unlocking_range(pagetable.pagetable_window_locks, spec_va_range_4k(va, 1)), ..pagetable
            }),
            ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// A step of the empty-L1 path runs under the map locks while mapping a 2M page is in progress with the given `flushed` record,
/// while the thread's container exists.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_l1_step_pre(old_u: KernelU, cpu_id: CpuId, flushed: bool) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is MapPciBar2m
    &&& progress->MapPciBar2m_flushed == flushed
}

/// Recording the flush of the hidden L1 page releases this cpu's read hold on the cpu set of the thread's container and marks the
/// progress flushed.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let cpu_set_lock = old_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            syscall_progress: Some(SyscallProgress::MapPciBar2m { va: progress->MapPciBar2m_va, directory: progress->MapPciBar2m_directory, flushed: true }), ..thread
        }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// A step between entering and exiting a 2M BAR map installs one directory page; or, for the empty L1 page under the slot, flushes
/// the process's PCID on one cpu, records that flush, or credits the reclaimed L1 page's 4K quota to the thread's container.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    ||| map_pci_bar_2m_directory_step_pre(step.old_u, cpu_id) && map_pci_bar_2m_directory_step(step.old_u, step.new_u, cpu_id)
    ||| map_pci_bar_2m_l1_step_pre(step.old_u, cpu_id, false) && unmap_4k_tlb_flush_step(step.old_u, step.new_u, cpu_id)
    ||| map_pci_bar_2m_l1_step_pre(step.old_u, cpu_id, false) && map_pci_bar_2m_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| map_pci_bar_2m_l1_step_pre(step.old_u, cpu_id, true) && kernel_u_container_quota_4k_increased(step.old_u, step.new_u, thread.owning_container)
}

/// The partial trace before the exit: the enter step and the directory or empty-L1 steps.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_trace_after_range(trace: Seq<KernelStep>, cpu_id: CpuId, slot: usize, index: usize, va: VAddr) -> bool {
    &&& 1 <= trace.len() <= NUM_CPUS + 3
    &&& map_pci_bar_2m_enter_step_pre(trace[0].old_u, cpu_id, slot, index, va)
    &&& map_pci_bar_2m_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> map_pci_bar_2m_range_step(trace[j], cpu_id)
}

/// The full trace of a successful 2M BAR map: the enter step, the directory or empty-L1 steps, and the exit step, which maps the
/// slot's chunk for the thread's container and counts it for the slot's function.
#[verifier::opaque]
pub open spec fn map_pci_bar_2m_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, slot: usize, index: usize, va: VAddr) -> bool {
    let n = trace.len() as int;
    let pre = trace[0].old_u;
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let entry = map_pci_bar_io_entry(map_pci_bar_2m_chunk(pre, slot, index), thread.owning_container);
    &&& 2 <= n <= NUM_CPUS + 4
    &&& map_pci_bar_2m_trace_after_range(trace.take(n - 1), cpu_id, slot, index, va)
    &&& map_pci_bar_2m_exit_step_pre(trace[n - 1].old_u, cpu_id, va)
    &&& map_pci_bar_2m_exit_step(trace[n - 1].old_u, trace[n - 1].new_u, cpu_id, va, pre.pci_bars[slot as int].bdf, entry)
}

/// The 4K page `page_index` of BAR table slot `slot` in `pre`.
pub open spec fn map_pci_bar_4k_page(pre: KernelU, slot: usize, page_index: usize) -> PAddr { pre.pci_bars[slot as int].spec_page_4k(page_index)->0 }

/// The present, writable, non-executable IO leaf that maps the BAR page or chunk `addr` for container `ctn_ptr`.
pub open spec fn map_pci_bar_io_entry(addr: PAddr, ctn_ptr: RwLockContainerPtr) -> MapEntry {
    MapEntry { is_io: true, addr, write: true, execute_disable: true, present: true, owning_container: Ghost(ctn_ptr) }
}

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu, the thread, and the pagetable of the thread's process
/// are unlocked; the thread's container exists; BAR table slot `slot` has the 4K page `page_index`; the process owns the slot's
/// function; no leaf covers `va`; and the thread has mmap's four 4K quota for one page.
#[verifier::opaque]
pub open spec fn map_pci_bar_4k_enter_step_pre(old_u: KernelU, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& spec_va_4k_valid(va)
    &&& slot < old_u.pci_bars.len()
    &&& old_u.pci_bars[slot as int].spec_page_4k(page_index) is Some
    &&& pagetable.pci_functions.dom().contains(old_u.pci_bars[slot as int].bdf)
    &&& pci_bar_va_4k_unmapped(pagetable, va)
    &&& thread.quota_4k >= 4
}

/// Entering write-locks the cpu, which enters its kernel step, its running thread, the pagetable of the thread's process, and the 2M
/// window of `va` when it exists, and starts the progress of mapping `va` with no directory installed.
#[verifier::opaque]
pub open spec fn map_pci_bar_4k_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let locked = LockStateU::WriteLocked { writer: cpu_id };
    let windows = if pagetable.pagetable_window_locks.dom().contains(window_of(va)) { pagetable.pagetable_window_locks.insert(window_of(va), locked) } else { pagetable.pagetable_window_locks };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: locked, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { lock_state: locked, pagetable_window_locks: windows, ..pagetable }), ..process }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            lock_state: locked, syscall_progress: Some(SyscallProgress::MapPciBar4k { va, directory: Mmap4kDirectory::None }), ..thread
        }),
        ..old_u
    })
}

/// The exit step runs under the map locks while mapping `va` is in progress.
#[verifier::opaque]
pub open spec fn map_pci_bar_4k_exit_step_pre(old_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let pagetable = old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& thread.syscall_progress->Some_0 is MapPciBar4k
    &&& thread.syscall_progress->Some_0->MapPciBar4k_va == va
}

/// Exiting maps `va` to the IO leaf `entry`, raises the mapped-BAR-page count of the BAR's function `f`, clears the progress, and
/// unlocks the 2M window of `va`, the cpu, which leaves its kernel step for its trap path, its running thread, and the pagetable of
/// the thread's process, which it write-holds.
#[verifier::opaque]
pub open spec fn map_pci_bar_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, f: PciBdf, entry: MapEntry) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& pagetable.lock_state == (LockStateU::WriteLocked { writer: cpu_id })
    &&& pagetable.pci_functions.dom().contains(f)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU {
                lock_state: LockStateU::Unlocked, mapping_4k: pagetable.mapping_4k.insert(va, entry), pci_functions: pagetable.pci_functions.insert(f, (pagetable.pci_functions[f] + 1) as nat),
                pagetable_window_locks: pagetable_window_locks_after_unlocking_range(pagetable.pagetable_window_locks, spec_va_range_4k(va, 1)), ..pagetable
            }),
            ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after the directories: the enter step and at most one directory step per missing L4, L3, and L2 entry.
#[verifier::opaque]
pub open spec fn map_pci_bar_4k_trace_after_directories(trace: Seq<KernelStep>, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr) -> bool {
    &&& 1 <= trace.len() <= 4
    &&& map_pci_bar_4k_enter_step_pre(trace[0].old_u, cpu_id, slot, page_index, va)
    &&& map_pci_bar_4k_enter_step(trace[0].old_u, trace[0].new_u, cpu_id, va)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> map_pci_bar_4k_directory_step_pre(trace[j].old_u, cpu_id) && map_pci_bar_4k_directory_step(trace[j].old_u, trace[j].new_u, cpu_id)
}

/// The full trace of a successful BAR map: the enter step, at most one directory step per missing L4, L3, and L2 entry, and the exit
/// step, which maps the slot's page for the thread's container and counts it for the slot's function.
#[verifier::opaque]
pub open spec fn map_pci_bar_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr) -> bool {
    let n = trace.len() as int;
    let pre = trace[0].old_u;
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let entry = map_pci_bar_io_entry(map_pci_bar_4k_page(pre, slot, page_index), thread.owning_container);
    &&& 2 <= n <= 5
    &&& map_pci_bar_4k_enter_step_pre(pre, cpu_id, slot, page_index, va)
    &&& map_pci_bar_4k_enter_step(pre, trace[0].new_u, cpu_id, va)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < n - 1 ==> map_pci_bar_4k_directory_step_pre(trace[j].old_u, cpu_id) && map_pci_bar_4k_directory_step(trace[j].old_u, trace[j].new_u, cpu_id)
    &&& map_pci_bar_4k_exit_step_pre(trace[n - 1].old_u, cpu_id, va)
    &&& map_pci_bar_4k_exit_step(trace[n - 1].old_u, trace[n - 1].new_u, cpu_id, va, pre.pci_bars[slot as int].bdf, entry)
}

/// The result of `syscall_unmap_pci_bar_4k` from the state at entry, in the implementation's check order: a malformed `va`, an idle or
/// killed cpu, a killed caller, and then `va` not a 4K IO leaf of the caller's process.
pub open spec fn unmap_pci_bar_4k_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k;
    if !spec_va_4k_valid(va) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if mapping.dom().contains(va) && mapping[va].is_io { RetValueType::Success }
    else { RetValueType::ErrorPciBarNotMapped }
}

/// The PCI function owning the BAR page that the 4K leaf `va` of the running thread's process maps.
pub open spec fn unmap_pci_bar_4k_function(pre: KernelU, cpu_id: CpuId, va: VAddr) -> PciBdf {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    pci_bar_function_of_page(pre.pci_bars, pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k[va].addr)->0
}

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu, the thread, and the pagetable of the thread's process
/// are unlocked; the thread's container exists; and `va` is a 4K IO leaf of the process.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_hide_step_pre(old_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& spec_va_4k_valid(va)
    &&& pagetable.mapping_4k.dom().contains(va)
    &&& pagetable.mapping_4k[va].is_io
}

/// Hiding write-locks the cpu, which enters its kernel step, its running thread, and the pagetable of the thread's process, removes
/// `va` from the process's 4K user mapping, and records the hidden, not yet flushed leaf.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_hide_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, mapping_4k: pagetable.mapping_4k.remove(va), ..pagetable }), ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }), ..thread
        }),
        ..old_u
    })
}

/// A flush step runs under the unmap locks after the leaf is hidden and before the flush is recorded, while the thread's container
/// exists.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is UnmapPciBar4k
    &&& !progress->UnmapPciBar4k_flushed
}

/// Recording the flush releases this cpu's read hold on the cpu set of the thread's container and marks the progress flushed.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let cpu_set_lock = old_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            syscall_progress: Some(SyscallProgress::UnmapPciBar4k { va: thread.syscall_progress->Some_0->UnmapPciBar4k_va, flushed: true }), ..thread
        }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// The exit step runs under the unmap locks after the flush is recorded.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_flushed_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is UnmapPciBar4k
    &&& progress->UnmapPciBar4k_flushed
}

/// Exiting removes the flushed leaf, which lowers the mapped-BAR-page count of its function `f`, owned by the process with at least
/// one mapping, clears the progress, and unlocks the cpu, which leaves its kernel step for its trap path, its running thread, and the
/// pagetable of the thread's process, which it write-holds. The hidden leaf is already absent from the user mapping.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, f: PciBdf) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& pagetable.lock_state == (LockStateU::WriteLocked { writer: cpu_id })
    &&& pagetable.pci_functions.dom().contains(f)
    &&& pagetable.pci_functions[f] > 0
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, pci_functions: pagetable.pci_functions.insert(f, (pagetable.pci_functions[f] - 1) as nat), ..pagetable }), ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after hiding the leaf and flushing every cpu: the hide step followed by at most one TLB flush per cpu.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_trace_after_flush(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr) -> bool {
    &&& 1 <= trace.len() <= NUM_CPUS + 1
    &&& unmap_pci_bar_4k_hide_step_pre(trace[0].old_u, cpu_id, va)
    &&& unmap_pci_bar_4k_hide_step(trace[0].old_u, trace[0].new_u, cpu_id, va)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> unmap_pci_bar_4k_flush_step_pre(trace[j].old_u, cpu_id) && unmap_4k_tlb_flush_step(trace[j].old_u, trace[j].new_u, cpu_id)
}

/// The full trace of a successful BAR unmap: the hide step, at most one TLB flush step per cpu, the flushed step, and the exit step,
/// which removes the leaf of the function owning its BAR page.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_4k_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr) -> bool {
    let n = trace.len() as int;
    &&& 3 <= n <= NUM_CPUS + 3
    &&& unmap_pci_bar_4k_trace_after_flush(trace.take(n - 2), cpu_id, va)
    &&& unmap_pci_bar_4k_flush_step_pre(trace[n - 2].old_u, cpu_id)
    &&& unmap_pci_bar_4k_flushed_step(trace[n - 2].old_u, trace[n - 2].new_u, cpu_id)
    &&& unmap_pci_bar_4k_flushed_step_pre(trace[n - 1].old_u, cpu_id)
    &&& unmap_pci_bar_4k_exit_step(trace[n - 1].old_u, trace[n - 1].new_u, cpu_id, unmap_pci_bar_4k_function(trace[0].old_u, cpu_id, va))
}
/// The result of `syscall_unmap_pci_bar_2m` from the state at entry, in the implementation's check order: a malformed `va`, an idle or
/// killed cpu, a killed caller, and then `va` not a 2M IO leaf of the caller's process.
pub open spec fn unmap_pci_bar_2m_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_2m;
    if !spec_va_2m_valid(va) { RetValueType::Error }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if mapping.dom().contains(va) && mapping[va].is_io { RetValueType::Success }
    else { RetValueType::ErrorPciBarNotMapped }
}

/// The PCI function owning the BAR page that the 2M leaf `va` of the running thread's process maps.
pub open spec fn unmap_pci_bar_2m_function(pre: KernelU, cpu_id: CpuId, va: VAddr) -> PciBdf {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    pci_bar_function_of_page(pre.pci_bars, pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_2m[va].addr)->0
}

/// The cpu runs a live thread with no multi-step syscall in progress; the cpu, the thread, and the pagetable of the thread's process
/// are unlocked; the thread's container exists; and `va` is a 2M IO leaf of the process.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_hide_step_pre(old_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread->Some_0);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& spec_va_2m_valid(va)
    &&& pagetable.mapping_2m.dom().contains(va)
    &&& pagetable.mapping_2m[va].is_io
}

/// Hiding write-locks the cpu, which enters its kernel step, its running thread, and the pagetable of the thread's process, removes
/// `va` from the process's 2M user mapping, and records the hidden, not yet flushed leaf.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_hide_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, mapping_2m: pagetable.mapping_2m.remove(va), ..pagetable }), ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(SyscallProgress::UnmapPciBar2m { va, flushed: false }), ..thread
        }),
        ..old_u
    })
}

/// A flush step runs under the unmap locks after the leaf is hidden and before the flush is recorded, while the thread's container
/// exists.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is UnmapPciBar2m
    &&& !progress->UnmapPciBar2m_flushed
}

/// Recording the flush releases this cpu's read hold on the cpu set of the thread's container and marks the progress flushed.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let cpu_set_lock = old_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU {
            syscall_progress: Some(SyscallProgress::UnmapPciBar2m { va: thread.syscall_progress->Some_0->UnmapPciBar2m_va, flushed: true }), ..thread
        }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// The exit step runs under the unmap locks after the flush is recorded.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_flushed_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is UnmapPciBar2m
    &&& progress->UnmapPciBar2m_flushed
}

/// Exiting removes the flushed leaf, which lowers the mapped-BAR-page count of its function `f`, owned by the process with at least
/// one mapping, clears the progress, and unlocks the cpu, which leaves its kernel step for its trap path, its running thread, and the
/// pagetable of the thread's process, which it write-holds. The hidden leaf is already absent from the user mapping.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_exit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, f: PciBdf) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    &&& pagetable.lock_state == (LockStateU::WriteLocked { writer: cpu_id })
    &&& pagetable.pci_functions.dom().contains(f)
    &&& pagetable.pci_functions[f] > 0
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, pci_functions: pagetable.pci_functions.insert(f, (pagetable.pci_functions[f] - 1) as nat), ..pagetable }), ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
        ..old_u
    })
}

/// The partial trace after hiding the leaf and flushing every cpu: the hide step followed by at most one TLB flush per cpu.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_trace_after_flush(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr) -> bool {
    &&& 1 <= trace.len() <= NUM_CPUS + 1
    &&& unmap_pci_bar_2m_hide_step_pre(trace[0].old_u, cpu_id, va)
    &&& unmap_pci_bar_2m_hide_step(trace[0].old_u, trace[0].new_u, cpu_id, va)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> unmap_pci_bar_2m_flush_step_pre(trace[j].old_u, cpu_id) && unmap_4k_tlb_flush_step(trace[j].old_u, trace[j].new_u, cpu_id)
}

/// The full trace of a successful BAR unmap: the hide step, at most one TLB flush step per cpu, the flushed step, and the exit step,
/// which removes the leaf of the function owning its BAR page.
#[verifier::opaque]
pub open spec fn unmap_pci_bar_2m_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, va: VAddr) -> bool {
    let n = trace.len() as int;
    &&& 3 <= n <= NUM_CPUS + 3
    &&& unmap_pci_bar_2m_trace_after_flush(trace.take(n - 2), cpu_id, va)
    &&& unmap_pci_bar_2m_flush_step_pre(trace[n - 2].old_u, cpu_id)
    &&& unmap_pci_bar_2m_flushed_step(trace[n - 2].old_u, trace[n - 2].new_u, cpu_id)
    &&& unmap_pci_bar_2m_flushed_step_pre(trace[n - 1].old_u, cpu_id)
    &&& unmap_pci_bar_2m_exit_step(trace[n - 1].old_u, trace[n - 1].new_u, cpu_id, unmap_pci_bar_2m_function(trace[0].old_u, cpu_id, va))
}
} // verus!

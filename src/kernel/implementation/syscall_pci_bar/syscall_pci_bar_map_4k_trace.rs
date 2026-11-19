use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::mmap_4k_build_structure_spec::{map_pci_bar_4k_directory_step_pre, map_pci_bar_4k_directory_step};
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::mmap_4k_build_structure_spec::{map_pci_bar_4k_directory_step_pre, map_pci_bar_4k_directory_step};

verus! {
/// The entry state's K facts on the running thread's cpu, process, pagetable, and the BAR table decide the BAR map result `ret`.
pub(super) proof fn map_pci_bar_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        spec_va_4k_valid(va),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let bars = krnl.pci_bars.view();
            let idx = spec_va2index(va);
            let slot_ok = slot < bars.len() && bars[slot as int].spec_page_4k(page_index) is Some;
            let owned = table.higher.pci.view().dom().contains(bars[slot as int].bdf);
            let free = !table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0))) && !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
                && !table.mapping_4k().dom().contains(va);
            let checked = !(ret is CpuIdle) && !(ret is ErrorThreadKilled);
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& checked ==> !thread.being_killed() && !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& (ret is ErrorVaInUse || ret is ErrorNoQuota || ret is Success) ==> table.leaves_present()
            &&& ret is ErrorPciBarSlotInvalid ==> !slot_ok
            &&& ret is ErrorPciOwnerMismatch ==> slot_ok && !owned
            &&& ret is ErrorVaInUse ==> slot_ok && owned && !free
            &&& ret is ErrorNoQuota ==> slot_ok && owned && free && thread.view().quota_4k < 4
            &&& ret is Success ==> slot_ok && owned && free && thread.view().quota_4k >= 4
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorPciBarSlotInvalid || ret is ErrorPciOwnerMismatch || ret is ErrorVaInUse || ret is ErrorNoQuota
                || ret is Success
        }),
    ensures map_pci_bar_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, slot, page_index, va) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id); kernel_u_domains_projection(krnl);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None); kernel_thread_projection_at(krnl, c.current_thread->Some_0);
        if !(ret is ErrorThreadKilled) { kernel_process_projection_at(krnl, thread.owning_proc); }
    }
}

/// A rejection by `unmap_4k_lock_current_thread`, stated on the entry state, is the BAR map result `ret`.
pub(super) proof fn map_pci_bar_4k_lock_rejected_result_from_k(krnl: &KernelK, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        spec_va_4k_valid(va),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            &&& ret is CpuIdle || ret is ErrorThreadKilled
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
        }),
    ensures map_pci_bar_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, slot, page_index, va) == ret,
{ map_pci_bar_4k_result_from_k(krnl, cpu_id, slot, page_index, va, ret); }

/// Installing the IO leaf `entry` at `va` in its held 2M window with one more mapping of function `f` (`b`), then unlocking the window,
/// clearing the progress, and unlocking the caller's cpu, its running thread, and the write-held pagetable `pagetable_ptr` of its
/// process (`post`) is the exit step from `krnl`'s projection.
pub(super) proof fn map_pci_bar_4k_exit_step_from_u(
    krnl: &KernelK, b: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, f: PciBdf,
    entry: MapEntry,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let t = process.pagetable->Some_0;
            let locked = LockStateU::WriteLocked { writer: cpu_id };
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& t.lock_state == locked
            &&& thread.syscall_progress is Some && thread.syscall_progress->Some_0 is MapPciBar4k && thread.syscall_progress->Some_0->MapPciBar4k_va == va
            &&& t.pci_functions.dom().contains(f)
            &&& b == (KernelU {
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: t.mapping_4k.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t }), ..process
                }),
                ..pre
            })
            &&& post == (KernelU {
                cpu_array: b.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..b.cpu_array[cpu_id as int] }),
                thread_map: b.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..b.thread_map.spec_index(thrd_ptr) }),
                process_map: b.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU {
                        lock_state: LockStateU::Unlocked,
                        pagetable_window_locks: pagetable_window_locks_after_unlocking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
                            spec_va_range_4k(va, 1)),
                        ..b.process_map.spec_index(prc_ptr).pagetable->Some_0 }),
                    ..b.process_map.spec_index(prc_ptr)
                }),
                ..b
            })
        }),
    ensures
        map_pci_bar_4k_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, va),
        map_pci_bar_4k_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, va, f, entry),
{
    kernel_process_projection_at(krnl, prc_ptr); reveal(map_pci_bar_4k_exit_step_pre); reveal(map_pci_bar_4k_exit_step);
    let pre = kernel_k_to_kernel_u(*krnl);
    let t = pre.process_map[prc_ptr].pagetable->Some_0;
    assert(post.process_map =~= pre.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU {
            lock_state: LockStateU::Unlocked, mapping_4k: t.mapping_4k.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat),
            pagetable_window_locks: pagetable_window_locks_after_unlocking_range(t.pagetable_window_locks, spec_va_range_4k(va, 1)), ..t
        }),
        ..pre.process_map[prc_ptr]
    }));
}

/// Write-locking the caller's cpu, with the cpu inside its kernel step, its running thread, and the pagetable `pagetable_ptr` of its
/// process, and starting the progress of mapping `va`, is the enter step from `krnl`'s projection to `post` when the BAR map succeeds
/// there.
pub(super) proof fn map_pci_bar_4k_enter_step_from_u(
    krnl: &KernelK, post: KernelU, windows: Map<WindowVa, LockStateU>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    slot: usize, page_index: usize, va: VAddr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        spec_va_4k_valid(va),
        map_pci_bar_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, slot, page_index, va) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        krnl.ctn_mp.dom().contains(krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container),
        ({
            let old_windows = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks;
            windows == if old_windows.dom().contains(window_of(va)) { old_windows.insert(window_of(va), LockStateU::WriteLocked { writer: cpu_id }) } else { old_windows }
        }),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            let locked = LockStateU::WriteLocked { writer: cpu_id };
            &&& cpu.lock_state is Unlocked
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& thread.owning_proc == prc_ptr
            &&& pagetable.lock_state is Unlocked
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: locked, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: locked, syscall_progress: Some(SyscallProgress::MapPciBar4k { va, directory: Mmap4kDirectory::None }), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: locked, pagetable_window_locks: windows, ..pagetable }), ..process }),
                ..pre
            })
        }),
    ensures
        map_pci_bar_4k_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, slot, page_index, va),
        map_pci_bar_4k_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, va),
{
    kernel_u_domains_projection(krnl); kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thrd_ptr); kernel_process_projection_at(krnl, prc_ptr);
    reveal(map_pci_bar_4k_enter_step_pre); reveal(map_pci_bar_4k_enter_step);
}

/// The enter step pushed onto an empty trace is the partial trace after the directories, with no directory yet.
pub(super) proof fn map_pci_bar_4k_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        map_pci_bar_4k_enter_step_pre(pre, cpu_id, slot, page_index, va),
        map_pci_bar_4k_enter_step(pre, post, cpu_id, va),
    ensures
        map_pci_bar_4k_trace_after_directories(steps.view(), cpu_id, slot, page_index, va),
        steps.view()[0].old_u == pre,
{ reveal(map_pci_bar_4k_trace_after_directories); }

/// A directory step pushed after the partial trace after the directories, which holds at most two directory steps, keeps it.
pub(super) proof fn map_pci_bar_4k_trace_directory_step(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr)
    requires
        map_pci_bar_4k_trace_after_directories(before, cpu_id, slot, page_index, va),
        before.len() <= 3,
        steps.view() == before.push(steps.view().last()),
        map_pci_bar_4k_directory_step_pre(steps.view().last().old_u, cpu_id),
        map_pci_bar_4k_directory_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        map_pci_bar_4k_trace_after_directories(steps.view(), cpu_id, slot, page_index, va),
        steps.view()[0] == before[0],
{ reveal(map_pci_bar_4k_trace_after_directories); }

/// The exit step pushed after the partial trace after the directories, which starts at the projection of `entry_k`, completes the
/// syscall trace when it maps the slot's page `addr` for the thread's container `ctn_ptr` and counts it for the slot's function.
pub(super) proof fn map_pci_bar_4k_trace_exit_step(
    steps: &KernelSteps, before: Seq<KernelStep>, entry_k: &KernelK, pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    slot: usize, page_index: usize, va: VAddr, addr: PAddr, f: PciBdf, entry: MapEntry,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        map_pci_bar_4k_trace_after_directories(before, cpu_id, slot, page_index, va),
        before[0].old_u == kernel_k_to_kernel_u(*entry_k),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        map_pci_bar_4k_exit_step_pre(pre, cpu_id, va),
        map_pci_bar_4k_exit_step(pre, post, cpu_id, va, f, entry),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry_k.thrd_mp.dom().contains(thrd_ptr),
        entry_k.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        slot < entry_k.pci_bars.view().len(),
        entry_k.pci_bars.view()[slot as int].spec_page_4k(page_index) == Some(addr),
        f == entry_k.pci_bars.view()[slot as int].bdf,
        entry == (MapEntry { is_io: true, addr, write: true, execute_disable: true, present: true, owning_container: Ghost(ctn_ptr) }),
    ensures map_pci_bar_4k_syscall_trace(steps.view(), cpu_id, slot, page_index, va),
{
    kernel_u_domains_projection(entry_k); kernel_cpu_projection_at(entry_k, cpu_id); kernel_thread_projection_at(entry_k, thrd_ptr);
    reveal(map_pci_bar_4k_trace_after_directories); reveal(map_pci_bar_4k_syscall_trace);
}
} // verus!

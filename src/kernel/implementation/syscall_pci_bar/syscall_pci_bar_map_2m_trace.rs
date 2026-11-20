use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::{unmap_4k_spec::unmap_4k_tlb_flush_step, mmap_4k_build_structure_spec::{map_pci_bar_2m_directory_step_pre, map_pci_bar_2m_directory_step}};
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::{unmap_4k_spec::unmap_4k_tlb_flush_step, mmap_4k_build_structure_spec::{map_pci_bar_2m_directory_step_pre, map_pci_bar_2m_directory_step}};

verus! {
/// The entry state's K facts on the running thread's cpu, process, pagetable, and the BAR table decide the BAR map result `ret`.
pub(super) proof fn map_pci_bar_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, slot: usize, index: usize, va: VAddr, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        spec_va_2m_valid(va),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let bars = krnl.pci_bars.view();
            let idx = spec_va2index(va);
            let slot_ok = slot < bars.len() && bars[slot as int].spec_chunk_2m(index) is Some;
            let owned = table.higher.pci.view().dom().contains(bars[slot as int].bdf);
            let free = !table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0))) && !table.mapping_2m().dom().contains(va)
                && forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))] pei_valid(l1i)
                    ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)));
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
            &&& ret is ErrorNoQuota ==> slot_ok && owned && free && thread.view().quota_4k < 2
            &&& ret is Success ==> slot_ok && owned && free && thread.view().quota_4k >= 2
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorPciBarSlotInvalid || ret is ErrorPciOwnerMismatch || ret is ErrorVaInUse || ret is ErrorNoQuota
                || ret is Success
        }),
    ensures map_pci_bar_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, slot, index, va) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id); kernel_u_domains_projection(krnl);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None); kernel_thread_projection_at(krnl, c.current_thread->Some_0);
        if !(ret is ErrorThreadKilled) { kernel_process_projection_at(krnl, thread.owning_proc); }
        if ret is ErrorVaInUse || ret is ErrorNoQuota || ret is Success { kernel_pagetable_mappings_projection_at(krnl, thread.owning_proc); }
    }
}

/// A rejection by `unmap_4k_lock_current_thread`, stated on the entry state, is the BAR map result `ret`.
pub(super) proof fn map_pci_bar_2m_lock_rejected_result_from_k(krnl: &KernelK, cpu_id: CpuId, slot: usize, index: usize, va: VAddr, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        spec_va_2m_valid(va),
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
    ensures map_pci_bar_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, slot, index, va) == ret,
{ map_pci_bar_2m_result_from_k(krnl, cpu_id, slot, index, va, ret); }

/// Installing the IO leaf `entry` at `va` in its held 2M window with one more mapping of function `f` (`b`), then unlocking the window,
/// clearing the progress, and unlocking the caller's cpu, its running thread, and the write-held pagetable `pagetable_ptr` of its
/// process (`post`) is the exit step from `krnl`'s projection.
pub(super) proof fn map_pci_bar_2m_exit_step_from_u(
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
            &&& thread.syscall_progress is Some && thread.syscall_progress->Some_0 is MapPciBar2m && thread.syscall_progress->Some_0->MapPciBar2m_va == va
            &&& t.pci_functions.dom().contains(f)
            &&& b == (KernelU {
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_2m: t.mapping_2m.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t }), ..process
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
        map_pci_bar_2m_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, va),
        map_pci_bar_2m_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, va, f, entry),
{
    kernel_process_projection_at(krnl, prc_ptr); reveal(map_pci_bar_2m_exit_step_pre); reveal(map_pci_bar_2m_exit_step);
    let pre = kernel_k_to_kernel_u(*krnl);
    let t = pre.process_map[prc_ptr].pagetable->Some_0;
    assert(post.process_map =~= pre.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU {
            lock_state: LockStateU::Unlocked, mapping_2m: t.mapping_2m.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat),
            pagetable_window_locks: pagetable_window_locks_after_unlocking_range(t.pagetable_window_locks, spec_va_range_4k(va, 1)), ..t
        }),
        ..pre.process_map[prc_ptr]
    }));
}

/// Write-locking the caller's cpu, with the cpu inside its kernel step, its running thread, and the pagetable `pagetable_ptr` of its
/// process, and starting the progress of mapping `va`, is the enter step from `krnl`'s projection to `post` when the BAR map succeeds
/// there.
pub(super) proof fn map_pci_bar_2m_enter_step_from_u(
    krnl: &KernelK, post: KernelU, windows: Map<WindowVa, LockStateU>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    slot: usize, index: usize, va: VAddr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        spec_va_2m_valid(va),
        map_pci_bar_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, slot, index, va) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        ({
            let pagetable = kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable->Some_0;
            &&& kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable is Some
            &&& pagetable.pagetable_window_locks.dom().contains(window_of(va)) ==> pagetable.pagetable_window_locks[window_of(va)] is Unlocked
        }),
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
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: locked,
                    syscall_progress: Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: false }), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: locked, pagetable_window_locks: windows, ..pagetable }), ..process }),
                ..pre
            })
        }),
    ensures
        map_pci_bar_2m_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, slot, index, va),
        map_pci_bar_2m_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, va),
{
    kernel_u_domains_projection(krnl); kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thrd_ptr); kernel_process_projection_at(krnl, prc_ptr);
    reveal(map_pci_bar_2m_enter_step_pre); reveal(map_pci_bar_2m_enter_step);
}

/// The enter step pushed onto an empty trace is the partial trace before the exit, with no range step yet.
pub(super) proof fn map_pci_bar_2m_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, slot: usize, index: usize, va: VAddr)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        map_pci_bar_2m_enter_step_pre(pre, cpu_id, slot, index, va),
        map_pci_bar_2m_enter_step(pre, post, cpu_id, va),
    ensures
        map_pci_bar_2m_trace_after_range(steps.view(), cpu_id, slot, index, va),
        steps.view()[0].old_u == pre,
{ reveal(map_pci_bar_2m_trace_after_range); }

/// A directory step pushed after the partial trace before the exit, which holds at most one range step, keeps it.
pub(super) proof fn map_pci_bar_2m_trace_directory_step(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, slot: usize, index: usize, va: VAddr)
    requires
        map_pci_bar_2m_trace_after_range(before, cpu_id, slot, index, va),
        before.len() <= 2,
        steps.view() == before.push(steps.view().last()),
        map_pci_bar_2m_directory_step_pre(steps.view().last().old_u, cpu_id),
        map_pci_bar_2m_directory_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        map_pci_bar_2m_trace_after_range(steps.view(), cpu_id, slot, index, va),
        steps.view()[0] == before[0],
{ reveal(map_pci_bar_2m_trace_after_range); reveal(map_pci_bar_2m_range_step); }

/// The caller write-holding its cpu, its thread, and the pagetable of the thread's present process while a 2M BAR map with the given
/// `flushed` record is in progress and the thread's container exists satisfies the empty-L1 step precondition and projects its K
/// anchors.
pub(super) proof fn map_pci_bar_2m_l1_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    pcid: Pcid, va: VAddr, directory: Mmap2mDirectory, flushed: bool,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::MapPciBar2m { va, directory, flushed }),
    ensures
        map_pci_bar_2m_l1_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, flushed),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::MapPciBar2m { va, directory, flushed }),
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == pcid,
{
    reveal(map_pci_bar_2m_l1_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// TLB flushes of the caller's PCID recorded from `entry` after the partial trace `before`, while the caller write-holds its cpu, its
/// thread, and the pagetable of the thread's present process with the L1 page hidden and the thread's container exists, keep the
/// partial trace before the exit.
pub(super) proof fn map_pci_bar_2m_tlb_flush_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, slot: usize, index: usize, va: VAddr,
)
    requires
        map_pci_bar_2m_trace_after_range(before, cpu_id, slot, index, va),
        before.len() == 1,
        before.len() <= steps.view().len() <= before.len() + NUM_CPUS,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        typed_lock_maps_aligned(entry, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        entry.prc_mp.dom().contains(prc_ptr),
        entry.ctn_mp.dom().contains(ctn_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: false }),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr,
                ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(cpu_id), ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry_u.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[prc_ptr].pcid == entry_u.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
        },
    ensures
        map_pci_bar_2m_trace_after_range(steps.view(), cpu_id, slot, index, va),
        steps.view()[0] == before[0],
{
    map_pci_bar_2m_l1_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, va, Mmap2mDirectory::None, false);
    reveal(map_pci_bar_2m_trace_after_range); reveal(map_pci_bar_2m_range_step); reveal(map_pci_bar_2m_l1_step_pre); reveal(unmap_4k_tlb_flush_step);
}

/// Recording the flush in the progress and releasing this cpu's read hold on the cpu set of the thread's container, from the step's
/// start `snap` through `pre` to `post`, pushed after the partial trace `before`, keeps the partial trace before the exit.
pub(super) proof fn map_pci_bar_2m_flushed_step_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, snap: &KernelK, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, slot: usize, index: usize, va: VAddr,
)
    requires
        map_pci_bar_2m_trace_after_range(before, cpu_id, slot, index, va),
        before.len() <= NUM_CPUS + 1,
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*snap), new_u: kernel_k_to_kernel_u(*post) }),
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: false }),
        *pre == (KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, cpu_set_mp: pre.cpu_set_mp, ..*snap }),
        pre.pt_mp.dom() == snap.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(pt)] snap.pt_mp.dom().contains(pt) ==> {
            &&& pre.pt_mp.spec_index(pt).locking_thread() == snap.pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_1g()
            &&& pre.pt_mp.spec_index(pt).view().higher.pci.mapping_counts() == snap.pt_mp.spec_index(pt).view().higher.pci.mapping_counts()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).lower.pagetable_window_locks
        },
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.cpu_set_mp.unchanged_except(&snap.cpu_set_mp, pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
        pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed()
            == snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
        snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().read_held_by(cpu_id),
        pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u()
            == snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().without_reader(cpu_id),
        *post == (KernelK { thrd_mp: post.thrd_mp, ..*pre }),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: true }),
    ensures
        map_pci_bar_2m_trace_after_range(steps.view(), cpu_id, slot, index, va),
        steps.view()[0] == before[0],
{
    kernel_cpu_tlb_flushed_cpu_set_runlocked_and_progress_changed_implies_u_step(snap, pre, post, cpu_id, ctn_ptr, thrd_ptr);
    map_pci_bar_2m_l1_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, va, Mmap2mDirectory::None, false);
    reveal(map_pci_bar_2m_trace_after_range); reveal(map_pci_bar_2m_range_step); reveal(map_pci_bar_2m_l1_step_pre); reveal(map_pci_bar_2m_flushed_step);
}

/// The reclaim step recorded from `mid`, crediting the reclaimed L1 page's 4K quota to the thread's container `ctn_ptr` while the
/// caller write-holds its cpu, its thread, and the pagetable of the thread's present process after the flush, pushed after the
/// partial trace `before`, keeps the partial trace before the exit.
pub(super) proof fn map_pci_bar_2m_reclaim_step_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, mid: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, slot: usize, index: usize, va: VAddr,
)
    requires
        map_pci_bar_2m_trace_after_range(before, cpu_id, slot, index, va),
        before.len() <= NUM_CPUS + 2,
        steps.view().len() == before.len() + 1,
        steps.view().drop_last() == before,
        steps.view().last().old_u == kernel_k_to_kernel_u(*mid),
        kernel_u_container_quota_4k_increased(steps.view().last().old_u, steps.view().last().new_u, ctn_ptr),
        typed_lock_maps_aligned(mid, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        mid.prc_mp.dom().contains(prc_ptr),
        mid.ctn_mp.dom().contains(ctn_ptr),
        !mid.prc_mp.spec_index(prc_ptr).view().zombie,
        mid.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        mid.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        mid.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        mid.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        mid.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        mid.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: true }),
    ensures
        map_pci_bar_2m_trace_after_range(steps.view(), cpu_id, slot, index, va),
        steps.view()[0] == before[0],
{
    map_pci_bar_2m_l1_step_pre_from_k(mid, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, va, Mmap2mDirectory::None, true);
    reveal(map_pci_bar_2m_trace_after_range); reveal(map_pci_bar_2m_range_step);
    assert(steps.view() =~= before.push(steps.view().last()));
}

/// The exit step pushed after the partial trace before the exit, which starts at the projection of `entry_k`, completes the syscall
/// trace when it maps the slot's chunk `addr` for the thread's container `ctn_ptr` and counts it for the slot's function.
pub(super) proof fn map_pci_bar_2m_trace_exit_step(
    steps: &KernelSteps, before: Seq<KernelStep>, entry_k: &KernelK, pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    slot: usize, index: usize, va: VAddr, addr: PAddr, f: PciBdf, entry: MapEntry,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        map_pci_bar_2m_trace_after_range(before, cpu_id, slot, index, va),
        before[0].old_u == kernel_k_to_kernel_u(*entry_k),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        map_pci_bar_2m_exit_step_pre(pre, cpu_id, va),
        map_pci_bar_2m_exit_step(pre, post, cpu_id, va, f, entry),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry_k.thrd_mp.dom().contains(thrd_ptr),
        entry_k.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        slot < entry_k.pci_bars.view().len(),
        entry_k.pci_bars.view()[slot as int].spec_chunk_2m(index) == Some(addr),
        f == entry_k.pci_bars.view()[slot as int].bdf,
        entry == (MapEntry { is_io: true, addr, write: true, execute_disable: true, present: true, owning_container: Ghost(ctn_ptr) }),
    ensures map_pci_bar_2m_syscall_trace(steps.view(), cpu_id, slot, index, va),
{
    kernel_u_domains_projection(entry_k); kernel_cpu_projection_at(entry_k, cpu_id); kernel_thread_projection_at(entry_k, thrd_ptr);
    reveal(map_pci_bar_2m_trace_after_range); reveal(map_pci_bar_2m_syscall_trace);
}
} // verus!

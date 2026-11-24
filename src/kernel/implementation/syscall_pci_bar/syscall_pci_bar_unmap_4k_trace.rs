use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::unmap_4k_spec::unmap_4k_tlb_flush_step;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::unmap_4k_spec::unmap_4k_tlb_flush_step;

verus! {
/// The entry state's K facts on the running thread's cpu, process, and pagetable decide the BAR unmap result `ret`.
pub(super) proof fn unmap_pci_bar_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, ret: RetValueType)
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
            let mapped = table.mapping_4k().dom().contains(va) && table.mapping_4k()[va].present && table.mapping_4k()[va].is_io;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& (ret is Success || ret is ErrorPciBarNotMapped) ==> !thread.being_killed() && !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret is Success ==> mapped
            &&& ret is ErrorPciBarNotMapped ==> !mapped
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is Success || ret is ErrorPciBarNotMapped
        }),
    ensures unmap_pci_bar_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is ErrorPciBarNotMapped { kernel_process_projection_at(krnl, thread.owning_proc); }
    }
}

/// A rejection by `unmap_4k_lock_current_thread`, stated on the entry state, is the BAR unmap result `ret`.
pub(super) proof fn unmap_pci_bar_4k_lock_rejected_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, ret: RetValueType)
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
    ensures unmap_pci_bar_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va) == ret,
{ unmap_pci_bar_4k_result_from_k(krnl, cpu_id, va, ret); }

/// Write-locking the caller's cpu, with the cpu inside its kernel step, its running thread, and the unlocked pagetable `pagetable_ptr`
/// of its process (`b`), then hiding the IO leaf `va`, which maps `addr`, and recording the hidden leaf (`post`), is the hide step from
/// `krnl`'s projection when `krnl`'s K facts pass every check of the BAR unmap, and `addr`'s function is the function the trace names.
pub(super) proof fn unmap_pci_bar_4k_hide_step_from_k(
    krnl: &KernelK, b: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    va: VAddr, addr: PAddr,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        spec_va_4k_valid(va),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            &&& cpu.view().view().state is Running
            &&& !cpu.being_killed()
            &&& cpu.view().view().current_thread == Some(thrd_ptr)
            &&& cpu.view().view().current_process == Some(prc_ptr)
            &&& krnl.thrd_mp.dom().contains(thrd_ptr)
            &&& !thread.being_killed()
            &&& thread.view().owning_proc == prc_ptr
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.ctn_mp.dom().contains(thread.view().owning_container)
            &&& krnl.prc_mp.dom().contains(prc_ptr)
            &&& !krnl.prc_mp.spec_index(prc_ptr).view().zombie
            &&& krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr
            &&& krnl.pt_mp.dom().contains(pagetable_ptr)
            &&& table.mapping_4k().dom().contains(va) && table.mapping_4k()[va].present && table.mapping_4k()[va].is_io
            &&& table.mapping_4k()[va].addr == addr
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
            &&& b == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: locked, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: locked, ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: locked, ..pagetable }), ..process }),
                ..pre
            })
            &&& post == (KernelU {
                process_map: b.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: b.process_map[prc_ptr].pagetable->Some_0.mapping_4k.remove(va), ..b.process_map[prc_ptr].pagetable->Some_0 }),
                    ..b.process_map[prc_ptr]
                }),
                thread_map: b.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }), ..b.thread_map[thrd_ptr] }),
                ..b
            })
        }),
    ensures
        unmap_pci_bar_4k_hide_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, va),
        unmap_pci_bar_4k_hide_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, va),
        unmap_pci_bar_4k_function(kernel_k_to_kernel_u(*krnl), cpu_id, va) == pci_bar_function_of_page(krnl.pci_bars.view(), addr)->0,
{
    unmap_pci_bar_4k_result_from_k(krnl, cpu_id, va, RetValueType::Success);
    kernel_u_domains_projection(krnl); kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thrd_ptr); kernel_process_projection_at(krnl, prc_ptr);
    reveal(unmap_pci_bar_4k_hide_step_pre); reveal(unmap_pci_bar_4k_hide_step);
    let pre = kernel_k_to_kernel_u(*krnl);
    let t = pre.process_map[prc_ptr].pagetable->Some_0;
    let locked = LockStateU::WriteLocked { writer: cpu_id };
    assert_maps_equal!(post.process_map, pre.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU { lock_state: locked, mapping_4k: t.mapping_4k.remove(va), ..t }), ..pre.process_map[prc_ptr]
    }));
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU {
        lock_state: locked, syscall_progress: Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }), ..pre.thread_map[thrd_ptr]
    }));
}

/// The hide step pushed onto an empty trace is the partial trace after flushing, with no flush step yet.
pub(super) proof fn unmap_pci_bar_4k_trace_hide_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_pci_bar_4k_hide_step_pre(pre, cpu_id, va),
        unmap_pci_bar_4k_hide_step(pre, post, cpu_id, va),
    ensures
        unmap_pci_bar_4k_trace_after_flush(steps.view(), cpu_id, va),
        steps.view()[0].old_u == pre,
{ reveal(unmap_pci_bar_4k_trace_after_flush); }

/// The caller write-holding its cpu, its thread, and the pagetable of the thread's present process with the leaf hidden and before
/// recording the flush, while the thread's container exists, satisfies the flush precondition and projects its K anchors.
pub(super) proof fn unmap_pci_bar_4k_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    va: VAddr,
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
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }),
    ensures
        unmap_pci_bar_4k_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }),
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid,
{
    reveal(unmap_pci_bar_4k_flush_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// TLB flushes of the caller's PCID recorded from `entry` after the hide step, while the caller write-holds its cpu, its thread, and
/// the pagetable of the thread's present process with the leaf hidden and the thread's container exists, keep the partial trace after
/// flushing.
pub(super) proof fn unmap_pci_bar_4k_tlb_flush_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, va: VAddr,
)
    requires
        unmap_pci_bar_4k_trace_after_flush(before, cpu_id, va),
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
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr,
                ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(cpu_id), ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, pcid, Some(ctn_ptr))
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
        unmap_pci_bar_4k_trace_after_flush(steps.view(), cpu_id, va),
        steps.view()[0] == before[0],
{
    unmap_pci_bar_4k_flush_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, va);
    reveal(unmap_pci_bar_4k_trace_after_flush); reveal(unmap_pci_bar_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step);
}

/// Recording the flush in the progress and releasing this cpu's read hold on the cpu set of the thread's container, from the step's
/// start `snap` through `pre`, which extends `snap` by page-table ghost state and that released hold, to `post`, is the flushed step.
pub(super) proof fn unmap_pci_bar_4k_flushed_step_from_k(
    snap: &KernelK, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    pagetable: RwLockPageTableRoot, va: VAddr,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::UnmapPciBar4k { va, flushed: false }),
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
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::UnmapPciBar4k { va, flushed: true }),
    ensures
        unmap_pci_bar_4k_flush_step_pre(kernel_k_to_kernel_u(*snap), cpu_id),
        unmap_pci_bar_4k_flushed_step(kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id),
{
    kernel_cpu_tlb_flushed_cpu_set_runlocked_and_progress_changed_implies_u_step(snap, pre, post, cpu_id, ctn_ptr, thrd_ptr);
    unmap_pci_bar_4k_flush_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, va);
    reveal(unmap_pci_bar_4k_flush_step_pre); reveal(unmap_pci_bar_4k_flushed_step);
}

/// Removing the flushed leaf of function `f` (`b`, from `krnl`'s projection), then clearing the progress and unlocking the caller's
/// cpu, which leaves its kernel step for its trap path, its running thread, and the pagetable `pagetable_ptr` of its process, which it
/// write-holds through `lctx` (`post`), is the exit step.
pub(super) proof fn unmap_pci_bar_4k_exit_step_from_k(
    krnl: &KernelK, lctx: &LocalContext, b: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, va: VAddr, f: PciBdf,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == lctx.cpu_id(),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::UnmapPciBar4k { va, flushed: true }),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            let process = pre.process_map.spec_index(prc_ptr);
            let t = process.pagetable->Some_0;
            &&& t.pci_functions.dom().contains(f) && t.pci_functions[f] > 0
            &&& b == (KernelU {
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] - 1) as nat), ..t }), ..process }),
                ..pre
            })
            &&& post == (KernelU {
                cpu_array: b.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..b.cpu_array[cpu_id as int] }),
                thread_map: b.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..b.thread_map.spec_index(thrd_ptr) }),
                process_map: b.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..b.process_map.spec_index(prc_ptr).pagetable->Some_0 }), ..b.process_map.spec_index(prc_ptr)
                }),
                ..b
            })
        }),
    ensures
        unmap_pci_bar_4k_flushed_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        unmap_pci_bar_4k_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, f),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr); kernel_process_projection_at(krnl, prc_ptr);
    reveal(unmap_pci_bar_4k_flushed_step_pre); reveal(unmap_pci_bar_4k_exit_step);
    let pre = kernel_k_to_kernel_u(*krnl);
    let t = pre.process_map[prc_ptr].pagetable->Some_0;
    assert_maps_equal!(post.process_map, pre.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] - 1) as nat), ..t }), ..pre.process_map[prc_ptr]
    }));
}

/// The flushed and exit steps pushed after the partial trace after flushing complete the syscall trace when the exit step removes the
/// leaf of the function the trace names.
pub(super) proof fn unmap_pci_bar_4k_trace_exit_steps(
    steps: &KernelSteps, flushed: Seq<KernelStep>, before: Seq<KernelStep>, flushed_pre: KernelU, flushed_post: KernelU, pre: KernelU, post: KernelU,
    cpu_id: CpuId, va: VAddr, f: PciBdf,
)
    requires
        unmap_pci_bar_4k_trace_after_flush(flushed, cpu_id, va),
        before == flushed.push(KernelStep { old_u: flushed_pre, new_u: flushed_post }),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_pci_bar_4k_flush_step_pre(flushed_pre, cpu_id),
        unmap_pci_bar_4k_flushed_step(flushed_pre, flushed_post, cpu_id),
        unmap_pci_bar_4k_flushed_step_pre(pre, cpu_id),
        unmap_pci_bar_4k_exit_step(pre, post, cpu_id, f),
        f == unmap_pci_bar_4k_function(flushed[0].old_u, cpu_id, va),
    ensures unmap_pci_bar_4k_syscall_trace(steps.view(), cpu_id, va),
{
    reveal(unmap_pci_bar_4k_trace_after_flush); reveal(unmap_pci_bar_4k_syscall_trace);
}
} // verus!

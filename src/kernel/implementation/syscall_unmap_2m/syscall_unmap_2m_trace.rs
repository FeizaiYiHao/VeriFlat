use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_2m_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, process, and pagetable decide the unmap result `ret`.
pub(super) proof fn unmap_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 0x200000 || !spec_va_2m_valid(va) || va >= usize::MAX - range * 0x200000 || !spec_va_2m_range_valid(va, range)),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = spec_va_range_2m(va, range);
            let mapped = spec_v2l4index(va) >= table.kernel_l4_end() && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range
                ==> table.mapping_2m().dom().contains(va_range.view()[j]) && table.mapping_2m()[va_range.view()[j]].present;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& (ret is Success || ret is Error) ==> !thread.being_killed() && !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret is Success ==> mapped
            &&& ret is Error ==> !mapped
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is Success || ret is Error
        }),
    ensures
        unmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is Error {
            kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(thread.owning_proc).view().pagetable); kernel_process_projection_at(krnl, thread.owning_proc);
        }
    }
}

/// A rejection by `unmap_4k_lock_current_thread`, stated on the entry state, is the unmap result `ret`.
pub(super) proof fn unmap_2m_lock_rejected_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 0x200000 || !spec_va_2m_valid(va) || va >= usize::MAX - range * 0x200000 || !spec_va_2m_range_valid(va, range)),
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
    ensures
        unmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
{ unmap_2m_result_from_k(krnl, cpu_id, va, range, ret); }

/// Write-locking the caller's cpu, with the cpu inside its kernel step, and its running thread, read-locking the pagetable
/// `pagetable_ptr` of its process, setting the table's window locks to `windows`, those of `krnl` after locking the windows of
/// the range's covering 4K range, and recording the first page is the enter step from `krnl`'s projection to `post` when the
/// syscall succeeds there.
pub(super) proof fn unmap_2m_enter_step_from_u(
    krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize,
    range: VaRange2M, windows: Map<WindowVa, LockStateU>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        range == spec_va_range_2m(va, len),
        range.wf(),
        unmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        krnl.ctn_mp.dom().contains(krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container),
        windows == pagetable_window_locks_after_locking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range.covering_4k_range(), cpu_id),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            &&& cpu.lock_state is Unlocked
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& thread.owning_proc == prc_ptr
            &&& !(pagetable.lock_state is WriteLocked)
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(SyscallProgress::Unmap2m { range, unmapped: 0, flushed: false }), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: pagetable.lock_state.with_reader(cpu_id), pagetable_window_locks: windows, ..pagetable }), ..process }),
                ..pre
            })
        }),
    ensures
        unmap_2m_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range),
        unmap_2m_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range),
{
    kernel_u_domains_projection(krnl); kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thrd_ptr); kernel_process_projection_at(krnl, prc_ptr);
    reveal(unmap_2m_enter_step_pre); reveal(unmap_2m_enter_step);
}

/// Clearing the progress, unlocking the caller's cpu, which leaves its kernel step for its trap path, and its running thread,
/// and releasing this cpu's read hold on the pagetable `pagetable_ptr` of its process, which it holds, with `windows`, the
/// window locks of `krnl` after unlocking the windows of the range's covering 4K range, after the flushed range is the exit step
/// from `krnl`'s projection to `post`.
pub(super) proof fn unmap_2m_exit_step_from_u(
    krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    range: VaRange2M, windows: Map<WindowVa, LockStateU>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(cpu_id),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_unlocking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range.covering_4k_range()),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& !(process.pagetable->Some_0.lock_state is Unlocked)
            &&& process.pagetable->Some_0.lock_state == krnl.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& thread.syscall_progress is Some
            &&& progress is Unmap2m
            &&& progress->Unmap2m_range == range
            &&& progress->Unmap2m_unmapped == progress->Unmap2m_range.len
            &&& progress->Unmap2m_flushed
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: process.pagetable->Some_0.lock_state.without_reader(cpu_id), pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        }),
    ensures
        unmap_2m_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        unmap_2m_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(unmap_2m_exit_step_pre); reveal(unmap_2m_exit_step); }

/// The enter step pushed onto an empty trace is the partial trace after entering.
pub(super) proof fn unmap_2m_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange2M)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_2m_enter_step_pre(pre, cpu_id, range),
        unmap_2m_enter_step(pre, post, cpu_id, range),
    ensures
        unmap_2m_trace_after_enter(steps.view(), cpu_id, range),
{ reveal(unmap_2m_trace_after_enter); }

/// The range steps appended after the enter step give the partial trace after unmapping the range.
pub(super) proof fn unmap_2m_trace_range_steps(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, range: VaRange2M)
    requires
        unmap_2m_trace_after_enter(before, cpu_id, range),
        before.len() + range.len + 1 <= steps.view().len() <= before.len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
    ensures
        unmap_2m_trace_after_range(steps.view(), cpu_id, range),
{ reveal(unmap_2m_trace_after_enter); reveal(unmap_2m_trace_after_range); }

/// The exit step pushed after the unmapped partial trace completes the syscall trace.
pub(super) proof fn unmap_2m_trace_exit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize)
    requires
        unmap_2m_trace_after_range(before, cpu_id, spec_va_range_2m(va, range)),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_2m_exit_step_pre(pre, cpu_id),
        unmap_2m_exit_step(pre, post, cpu_id),
    ensures
        unmap_2m_syscall_trace(steps.view(), cpu_id, va, range),
{ reveal(unmap_2m_trace_after_range); reveal(unmap_2m_syscall_trace); }

/// Removing the `unmapped`-th page of the range, still mapped, under the unmap locks is the leaf step on `pre`/`post`.
pub(super) proof fn unmap_2m_leaf_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, range: VaRange2M, unmapped: usize, progress: Option<SyscallProgress>,
)
    requires
        thread_pagetable_op_in_progress(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].owning_proc == prc_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap2m { range, unmapped, flushed: false }),
        progress == Some(SyscallProgress::Unmap2m { range, unmapped: (unmapped + 1) as usize, flushed: false }),
        unmapped < range.len,
        pre.process_map[prc_ptr].pagetable->Some_0.mapping_2m.dom().contains(range.view()[unmapped as int]),
        post == (KernelU {
            process_map: pre.process_map.insert(prc_ptr, ProcessU {
                pagetable: Some(PageTableU { mapping_2m: pre.process_map[prc_ptr].pagetable->Some_0.mapping_2m.remove(range.view()[unmapped as int]), ..pre.process_map[prc_ptr].pagetable->Some_0 }),
                ..pre.process_map[prc_ptr]
            }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: progress, ..pre.thread_map[thrd_ptr] }),
            ..pre
        }),
    ensures
        unmap_2m_leaf_step_pre(pre, cpu_id),
        unmap_2m_leaf_step(pre, post, cpu_id),
{ reveal(unmap_2m_leaf_step_pre); reveal(unmap_2m_leaf_step); }

/// A leaf step pushed after range steps that start at `start` is a range step.
pub(super) proof fn unmap_2m_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_2m_leaf_step_pre(pre, cpu_id),
        unmap_2m_leaf_step(pre, post, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_2m_range_step); }

/// Removing `va`, the `unmapped`-th page of the range, from `pre`'s projection to `post` while the caller write-holds its cpu
/// and thread and holds the pagetable of the thread's present process in either mode, as `clear_2m_mapping_present_in_window`
/// records it, after range steps that start at `start` leaves only range steps.
pub(super) proof fn unmap_2m_leaf_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, range: VaRange2M, unmapped: usize, va: VAddr,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }),
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.pt_mp.dom().contains(pagetable),
        pre.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped, flushed: false }),
        unmapped < range.len,
        range.view()[unmapped as int] == va,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().insert(va, MapEntry { present: false, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va) }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view()
            == (Thread { syscall_progress: Ghost(Some(SyscallProgress::Unmap2m { range, unmapped: (unmapped + 1) as usize, flushed: false })), ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{
    kernel_pagetable_2m_present_cleared_and_progress_changed_implies_u_step(pre, post, pagetable, va, thrd_ptr);
    kernel_write_held_context_projection(pre, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(pre, prc_ptr);
    unmap_2m_leaf_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, prc_ptr, thrd_ptr, range, unmapped,
        Some(SyscallProgress::Unmap2m { range, unmapped: (unmapped + 1) as usize, flushed: false }));
    unmap_2m_range_steps_from_leaf(steps, before, start, kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id);
}

/// The caller write-holding its cpu and thread and holding the pagetable of the thread's present process in either mode after
/// clearing the whole range and before recording the flush, while the thread's container exists, satisfies the flush
/// precondition and projects its K anchors.
pub(super) proof fn unmap_2m_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    pcid: Pcid, range: VaRange2M,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: false }),
    ensures
        unmap_2m_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: false }),
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == pcid,
{
    reveal(unmap_2m_flush_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// TLB flushes of the caller's PCID, recorded after range steps that start at `start` while the caller's held objects keep
/// their projection at `entry`, leave only range steps.
pub(super) proof fn unmap_2m_range_steps_from_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
    ctn_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        unmap_2m_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        entry.thread_map[thrd_ptr].owning_proc == prc_ptr,
        entry.thread_map[thrd_ptr].owning_container == ctn_ptr,
        entry.process_map[prc_ptr].pcid == pcid,
        TLB_FLUSH_VA_RANGE_MAX_PAGES < entry.thread_map[thrd_ptr].syscall_progress->Some_0->Unmap2m_range.len,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(cpu_id), ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[prc_ptr].pcid == entry.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_2m_range_step); reveal(unmap_2m_flush_step_pre); reveal(unmap_4k_tlb_flush_step); }

/// TLB flushes of the caller's PCID recorded from `entry` after range steps that start at `start`, while the caller write-holds
/// its cpu and thread and holds the pagetable of the thread's present process with the whole range cleared and the thread's
/// container exists, leave only range steps.
pub(super) proof fn unmap_2m_tlb_flush_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange2M,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        typed_lock_maps_aligned(entry, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        entry.prc_mp.dom().contains(prc_ptr),
        entry.ctn_mp.dom().contains(ctn_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: false }),
        TLB_FLUSH_VA_RANGE_MAX_PAGES < range.len,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(cpu_id), ..old_u.container_map[ctn_ptr] }), ..old_u };
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
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{
    unmap_2m_flush_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, range);
    unmap_2m_range_steps_from_tlb_flush(steps, before, start, kernel_k_to_kernel_u(*entry), cpu_id, thrd_ptr, prc_ptr, ctn_ptr, pcid);
}

/// Per-address TLB flushes of the range's 2M addresses under the caller's PCID, recorded after range steps that start at
/// `start` while the caller's held objects keep their projection at `entry` and the range has at most
/// `TLB_FLUSH_VA_RANGE_MAX_PAGES` pages, leave only range steps.
pub(super) proof fn unmap_2m_range_steps_from_tlb_va_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    range: VaRange2M,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        unmap_2m_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        entry.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: false }),
        range.len <= TLB_FLUSH_VA_RANGE_MAX_PAGES,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& unmap_4k_tlb_va_flush_step(old_u, steps.view()[j].new_u, cpu_id, range.start, range.len, true)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[prc_ptr].pcid == entry.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
        },
        entry.thread_map[thrd_ptr].owning_proc == prc_ptr,
        entry.thread_map[thrd_ptr].owning_container == ctn_ptr,
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_2m_range_step); reveal(unmap_2m_flush_step_pre); }

/// Per-address TLB flushes of the range's 2M addresses under the caller's PCID recorded from `entry` after range steps that
/// start at `start`, while the caller write-holds its cpu and thread and holds the pagetable of the thread's present process
/// with the whole range of at most `TLB_FLUSH_VA_RANGE_MAX_PAGES` pages cleared and the thread's container exists, leave
/// only range steps.
pub(super) proof fn unmap_2m_tlb_va_flush_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange2M,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        typed_lock_maps_aligned(entry, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        entry.prc_mp.dom().contains(prc_ptr),
        entry.ctn_mp.dom().contains(ctn_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: false }),
        range.len <= TLB_FLUSH_VA_RANGE_MAX_PAGES,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            &&& unmap_4k_tlb_va_flush_step(old_u, steps.view()[j].new_u, cpu_id, range.start, range.len, true)
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
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{
    unmap_2m_flush_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, range);
    unmap_2m_range_steps_from_tlb_va_flush(steps, before, start, kernel_k_to_kernel_u(*entry), cpu_id, thrd_ptr, prc_ptr, ctn_ptr, range);
}

/// Recording the flush in the progress and releasing this cpu's read hold on the cpu set of the thread's container is the
/// flushed step on `pre`/`post`.
pub(super) proof fn unmap_2m_flushed_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, range: VaRange2M, unmapped: usize, progress: Option<SyscallProgress>,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap2m { range, unmapped, flushed: false }),
        pre.thread_map[thrd_ptr].owning_container == ctn_ptr,
        progress == Some(SyscallProgress::Unmap2m { range, unmapped, flushed: true }),
        pre.thread_map.dom().contains(thrd_ptr),
        pre.container_map[ctn_ptr].cpu_set_lock.read_held_by(cpu_id),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: progress, ..pre.thread_map[thrd_ptr] }),
            container_map: pre.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: pre.container_map[ctn_ptr].cpu_set_lock.without_reader(cpu_id), ..pre.container_map[ctn_ptr] }),
            ..pre
        }),
    ensures
        unmap_2m_flushed_step(pre, post, cpu_id),
{ reveal(unmap_2m_flushed_step); }

/// The flushed step pushed after range steps that start at `start` is a range step.
pub(super) proof fn unmap_2m_range_steps_from_flushed(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_2m_flush_step_pre(pre, cpu_id),
        unmap_2m_flushed_step(pre, post, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_2m_range_step); }

/// Recording the flush in the progress from `pre` to `post` after range steps that start at `start`, where `pre` extends the
/// step's start `snap` by page-table ghost state and by this cpu's released read hold on the cpu set of its container,
/// while the caller write-holds its cpu and thread and holds the pagetable of the thread's present process with the whole
/// range cleared, leaves only range steps.
pub(super) proof fn unmap_2m_flushed_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, snap: &KernelK, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange2M,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*snap), new_u: kernel_k_to_kernel_u(*post) }),
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: false }),
        *pre == (KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, cpu_set_mp: pre.cpu_set_mp, ..*snap }),
        pre.pt_mp.dom() == snap.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(pt)] snap.pt_mp.dom().contains(pt) ==> {
            &&& pre.pt_mp.spec_index(pt).locking_thread() == snap.pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_1g()
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
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped: range.len, flushed: true }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{
    let ghost_tables = KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*snap };
    reveal(kernel_cpu_nonlock_fields_unchanged); kernel_u_domains_projection(snap); kernel_container_projection_at(snap, ctn_ptr);
    kernel_cpu_tlb_updated_implies_u_step(snap, &ghost_tables);
    kernel_cpu_set_lock_mode_changed_implies_u_step(&ghost_tables, pre, ctn_ptr);
    kernel_thread_syscall_progress_changed_implies_u_step(pre, post, thrd_ptr);
    unmap_2m_flush_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, range);
    assert(unmap_2m_flush_step_pre(kernel_k_to_kernel_u(*snap), cpu_id)) by { reveal(unmap_2m_flush_step_pre); };
    unmap_2m_flushed_step_from_u(kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id, thrd_ptr, ctn_ptr, range, range.len, post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view());
    unmap_2m_range_steps_from_flushed(steps, before, start, kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id);
}

/// 2M quota refunds to the caller's container chain after range steps that start at `start` leave only range steps.
pub(super) proof fn unmap_2m_range_steps_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    progress: Option<SyscallProgress>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_2m_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        progress is Some,
        progress->Some_0 is Unmap2m,
        progress->Some_0->Unmap2m_unmapped == progress->Some_0->Unmap2m_range.len,
        progress->Some_0->Unmap2m_flushed,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_2m_increased(old_u, steps.view()[j].new_u, ctn_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thrd_ptr].owning_container == ctn_ptr
            &&& old_u.thread_map[thrd_ptr].owning_proc == prc_ptr
            &&& old_u.thread_map[thrd_ptr].syscall_progress == progress
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_2m_range_step); reveal(unmap_2m_exit_step_pre); }
} // verus!

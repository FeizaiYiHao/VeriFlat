use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::syscall_mmap_2m_spec::*;

verus! {
/// The entry state's K facts on the running thread, its process, and its pagetable decide the mmap result `ret`. A range result
/// checked on `cur`, which has the entry pagetable's mappings, is exact: a free range has no 4K, 2M, or 1G leaf in any page's
/// 2M window, and a range found in use has page `at` whose held window has its leaves present and holds the 4K leaf `found`
/// or, if there is none, a 2M leaf or a covering 1G leaf, all of which are present. Without a checked table, a range result
/// is only known to be success or in use.
pub(super) proof fn mmap_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType, cur: Option<WholePageTable<PT_TYPE>>,
    found: Option<(L4Index, L3Index, L2Index, L1Index)>, at: int)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 0x200000 || !spec_va_2m_valid(va) || va >= usize::MAX - range * 0x200000 || !spec_va_2m_range_valid(va, range)),
        mmap_2m_syscall_va_range(va, range).wf(),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = mmap_2m_syscall_va_range(va, range);
            let checked = cur->Some_0;
            let clear = forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> {
                let idx = spec_va2index(va_range.view()[j]);
                &&& !checked.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
                &&& !checked.mapping_2m().dom().contains(va_range.view()[j])
                &&& forall|l1i: L1Index| #![trigger checked.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))] pei_valid(l1i)
                    ==> !checked.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))
            };
            let at_va = va_range.view()[at];
            let at_idx = spec_va2index(at_va);
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& ret is ErrorNoQuota ==> !thread.being_killed() && (thread.view().quota_2m < range || thread.view().quota_4k < 2 * range)
            &&& (ret is Success || ret is Error || ret is ErrorVaInUse) ==> !thread.being_killed() && thread.view().quota_2m >= range && thread.view().quota_4k >= 2 * range
                && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& (ret is Success || ret is ErrorVaInUse) ==> !process.view().zombie && spec_v2l4index(va) >= table.kernel_l4_end()
            &&& cur is Some && (ret is Success || ret is ErrorVaInUse) ==> {
                &&& checked.mapping_4k() == table.mapping_4k()
                &&& checked.mapping_2m() == table.mapping_2m()
                &&& checked.mapping_1g() == table.mapping_1g()
            }
            &&& cur is Some && ret is ErrorVaInUse ==> {
                &&& 0 <= at < range
                &&& va_range.covering_4k_range().wf()
                &&& forall|w: WindowVa| #![trigger va_range_2m_windows(va_range.covering_4k_range()).contains(w)] va_range_2m_windows(va_range.covering_4k_range()).contains(w) ==> checked.window_leaves_present(w)
                &&& forall|v: VAddr| #![trigger checked.mapping_1g().dom().contains(v)] checked.mapping_1g().dom().contains(v) ==> checked.mapping_1g().spec_index(v).present
                &&& found is Some ==> {
                    let f = found->Some_0;
                    &&& f.0 == at_idx.0 && f.1 == at_idx.1 && f.2 == at_idx.2 && pei_valid(f.3)
                    &&& checked.mapping_4k().dom().contains(spec_index2va(f))
                }
                &&& found is None ==> checked.mapping_2m().dom().contains(at_va) || checked.mapping_1g().dom().contains(spec_index2va((at_idx.0, at_idx.1, 0, 0)))
            }
            &&& ret is Error ==> spec_v2l4index(va) < table.kernel_l4_end()
            &&& cur is Some && ret is Success ==> clear
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is Error || ret is Success || ret is ErrorVaInUse
        },
    ensures
        cur is Some || !(ret is Success || ret is ErrorVaInUse) ==> mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
        ret is Success || ret is ErrorVaInUse ==> mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) is Success
            || mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) is ErrorVaInUse,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is Error || ret is ErrorVaInUse { kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(thread.owning_proc).view().pagetable); }
        if ret is Success || ret is ErrorVaInUse {
            let prc_ptr = thread.owning_proc;
            let root = krnl.prc_mp.spec_index(prc_ptr).view().pagetable;
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), root);
            let u_pt = kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable->Some_0;
            kernel_process_projection_at(krnl, prc_ptr);
            assert(u_pt == table.user_view(krnl.pt_mp.spec_index(root).lock_state_u()));
            if cur is Some && ret is ErrorVaInUse {
                let va_range = mmap_2m_syscall_va_range(va, range);
                let at_va = va_range.view()[at];
                let at_idx = spec_va2index(at_va);
                assert(spec_va_2m_valid(at_va));
                assert(spec_index2va((at_idx.0, at_idx.1, at_idx.2, 0usize)) == at_va && pei_valid(at_idx.0) && pei_valid(at_idx.1) && pei_valid(at_idx.2)) by {
                    spec_va_2m_valid_index_roundtrip(at_va);
                };
                assert(spec_va2index(window_of(at_va).va) == (at_idx.0, at_idx.1, at_idx.2, 0usize)) by { spec_va_2m_valid_index_roundtrip(at_va); spec_va_4k_index_roundtrip_at(at_va, at_idx.0, at_idx.1, at_idx.2, 0usize); };
                assert(cur->Some_0.window_leaves_present(window_of(at_va))) by {
                    let cover = va_range.covering_4k_range();
                    va_range.wf_implies_view_index_is_start_plus_offset(); cover.wf_implies_view_index_is_start_plus_offset();
                    va_range_2m_windows_contains_window_of_first_n_pages(cover, cover.len as int);
                    assert(spec_va_add_range(va, (512 * at) as usize) == spec_va_add_range_2m(va, at as usize)) by (nonlinear_arith) requires 0 <= at < range, range <= usize::MAX / 0x200000;
                    assert(cover.view()[512 * at] == at_va);
                };
                if found is Some {
                    let f = found->Some_0;
                    let fv = spec_index2va(f);
                    spec_va_4k_index_roundtrip_at(fv, f.0, f.1, f.2, f.3);
                    assert(cur->Some_0.mapping_4k().spec_index(fv).present);
                    assert(u_pt.mapping_4k.dom().contains(spec_index2va((at_idx.0, at_idx.1, at_idx.2, f.3))));
                } else if cur->Some_0.mapping_2m().dom().contains(at_va) {
                    assert(cur->Some_0.mapping_2m().spec_index(at_va).present);
                    assert(u_pt.mapping_2m.dom().contains(at_va));
                } else {
                    assert(u_pt.mapping_1g.dom().contains(spec_index2va((at_idx.0, at_idx.1, 0, 0))));
                }
            }
        }
    }
}

/// The entry state's running thread's container is in the user view, as the enter step requires.
pub(super) proof fn mmap_2m_enter_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.ctn_mp.dom().contains(krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thrd_ptr).owning_container),
{ kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); }
/// Write-locking the caller's cpu and thread, which entering to fill already holds, with the cpu inside its kernel step, locking
/// its pagetable `pagetable_ptr` for `phase`, setting its range windows to `windows`, the window locks of `krnl` after locking
/// `range`, and recording the first page is the enter step from `krnl`'s projection to `post` when the syscall succeeds there.
pub(super) proof fn mmap_2m_enter_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize, range: VaRange2M, phase: Mmap2mPhase, windows: Map<WindowVa, LockStateU>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        range == mmap_2m_syscall_va_range(va, len),
        range.wf(),
        mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_locking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range.covering_4k_range()),
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.syscall_progress is None
            &&& thread.owning_proc == prc_ptr
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& !(phase is Filled)
            &&& phase is Read ==> cpu.lock_state is Unlocked && thread.lock_state is Unlocked && !(pagetable.lock_state is WriteLocked)
            &&& phase is Fill ==> cpu.lock_state is WriteLocked && thread.lock_state is WriteLocked && pagetable.lock_state is Unlocked
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase }), ..thread
                }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: if phase is Read { LockStateU::ReadLocked } else { LockStateU::WriteLocked }, pagetable_window_locks: windows, ..pagetable }),
                    ..process
                }),
                ..pre
            })
        },
    ensures
        mmap_2m_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range, phase),
        mmap_2m_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range, phase),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_2m_enter_step_pre); reveal(mmap_2m_enter_step); }

/// Entering to fill in two sections, first locking the pagetable `pagetable_ptr` and recording the first page from `krnl`'s
/// projection to `mid`, then locking the range's existing windows from `mid` to `post` with the thread's quota and progress kept,
/// is the enter step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_2m_fill_enter_step_from_u(krnl: &KernelK, mid: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize, range: VaRange2M, windows: Map<WindowVa, LockStateU>, quota: usize, progress: Option<SyscallProgress>,
    owner: RwLockProcessPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        range == mmap_2m_syscall_va_range(va, len),
        range.wf(),
        mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_locking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range.covering_4k_range()),
        owner == prc_ptr,
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.syscall_progress is None
            &&& thread.owning_proc == prc_ptr
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& cpu.lock_state is WriteLocked && thread.lock_state is WriteLocked && process.pagetable->Some_0.lock_state is Unlocked
            &&& mid == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase: Mmap2mPhase::Fill }),
                    ..thread
                }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        },
        mid.thread_map.spec_index(thrd_ptr).quota_4k == quota,
        mid.thread_map.spec_index(thrd_ptr).syscall_progress == progress,
        post == (KernelU {
            thread_map: mid.thread_map.insert(thrd_ptr, ThreadU { quota_4k: quota, syscall_progress: progress, ..mid.thread_map.spec_index(thrd_ptr) }),
            process_map: if mid.process_map.dom().contains(owner) && mid.process_map[owner].pagetable is Some {
                mid.process_map.insert(owner, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: windows, ..mid.process_map[owner].pagetable->Some_0 }), ..mid.process_map[owner] })
            } else { mid.process_map },
            ..mid
        }),
    ensures
        mmap_2m_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range, Mmap2mPhase::Fill),
        mmap_2m_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range, Mmap2mPhase::Fill),
{
    let pre = kernel_k_to_kernel_u(*krnl);
    let process = pre.process_map.spec_index(prc_ptr);
    kernel_process_projection_at(krnl, prc_ptr);
    assert(post.thread_map =~= mid.thread_map);
    assert(post.process_map =~= pre.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process
    }));
    mmap_2m_enter_step_from_u(krnl, post, cpu_id, prc_ptr, thrd_ptr, pagetable_ptr, va, len, range, Mmap2mPhase::Fill, windows);
}

/// The entry state's K facts on the running cpu and its current thread, both unlocked, with the syscall result success or in
/// use there, give the hold step's precondition.
pub(super) proof fn mmap_2m_hold_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, va: VAddr, len: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        mmap_2m_syscall_va_range(va, len).wf(),
        len > 0,
        mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success || mmap_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is ErrorVaInUse,
        !krnl.cpu_arr.spec_index(cpu_id).view().locked(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        !krnl.thrd_mp.spec_index(thrd_ptr).locked(),
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.ctn_mp.dom().contains(krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container),
    ensures mmap_2m_hold_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, mmap_2m_syscall_va_range(va, len)),
{ kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_2m_hold_step_pre); }

/// Write-locking the caller's cpu and its current thread `thrd_ptr` with the cpu inside its kernel step and changing nothing
/// else is the hold step on `pre`/`post`.
pub(super) proof fn mmap_2m_hold_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thrd_ptr) }),
            ..pre
        }),
    ensures mmap_2m_hold_step(pre, post, cpu_id),
{ reveal(mmap_2m_hold_step); }

/// Unlocking the caller's write-locked cpu and its current thread `thrd_ptr` with no progress recorded, returning the cpu to
/// its trap path, and changing nothing else is the release step on `pre`/`post`.
pub(super) proof fn mmap_2m_release_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_array[cpu_id as int].lock_state is WriteLocked,
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map.dom().contains(thrd_ptr),
        pre.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked,
        pre.thread_map.spec_index(thrd_ptr).syscall_progress is None,
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thrd_ptr) }),
            ..pre
        }),
    ensures
        mmap_2m_release_step_pre(pre, cpu_id),
        mmap_2m_release_step(pre, post, cpu_id),
{ reveal(mmap_2m_release_step_pre); reveal(mmap_2m_release_step); }

/// Turning the fill phase's write lock on the pagetable `pagetable_ptr` into a read lock with its window locks kept as `windows` is
/// the downgrade step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_2m_downgrade_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, windows: Map<WindowVa, LockStateU>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let progress = thread.syscall_progress->Some_0;
            let filled = SyscallProgress::Mmap2m { range: progress->Mmap2m_range, mapped: progress->Mmap2m_mapped, directory: Mmap2mDirectory::None, phase: Mmap2mPhase::Filled };
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Mmap2m
            &&& progress->Mmap2m_phase is Fill
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(filled), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process
                }),
                ..pre
            })
        },
    ensures
        mmap_2m_downgrade_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_2m_downgrade_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_2m_downgrade_step_pre); reveal(mmap_2m_downgrade_step); }
/// of pagetable `pagetable_ptr` to `windows`, those of `krnl` after unlocking `range`, returning the cpu to its trap path, and
/// leaving the pagetable in `table_lock`, is the exit step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_2m_exit_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, range: VaRange2M, table_lock: LockStateU, windows: Map<WindowVa, LockStateU>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_unlocking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range.covering_4k_range()),
        {
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
            &&& thread.syscall_progress is Some
            &&& progress is Mmap2m
            &&& !(progress->Mmap2m_phase is Fill)
            &&& progress->Mmap2m_range == range
            &&& progress->Mmap2m_mapped == range.len
            &&& progress->Mmap2m_directory is None
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: table_lock, pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process
                }),
                ..pre
            })
        },
        table_lock is Unlocked || table_lock is ReadLocked,
    ensures
        mmap_2m_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_2m_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_2m_exit_step_pre); reveal(mmap_2m_exit_step); }


/// Publishing the next recorded page of `pre` under the mmap locks with the pagetable read-locked as `entry`, whose frame no
/// mapping of `pre` reaches, is the leaf step from `pre` to `post`.
pub(super) proof fn mmap_2m_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, va: VAddr, entry: MapEntry)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            let progress = thread.syscall_progress->Some_0;
            let idx = spec_va2index(va);
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& pre.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& pagetable.lock_state is ReadLocked
            &&& thread.syscall_progress is Some
            &&& progress is Mmap2m
            &&& !(progress->Mmap2m_phase is Fill)
            &&& progress->Mmap2m_mapped < progress->Mmap2m_range.len
            &&& progress->Mmap2m_range.view()[progress->Mmap2m_mapped as int] == va
            &&& thread.quota_2m >= 1
            &&& !pagetable.mapping_2m.dom().contains(va)
            &&& !pagetable.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            &&& forall|l1i: L1Index| #![trigger pagetable.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))]
                pei_valid(l1i) ==> !pagetable.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))
            &&& entry.present
            &&& entry.write
            &&& !entry.execute_disable
            &&& entry.owning_container.view() == thread.owning_container
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre.process_map[p].pagetable->Some_0.mapping_2m[v]]
                pre.process_map.dom().contains(p) && pre.process_map[p].pagetable is Some && pre.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
                ==> pre.process_map[p].pagetable->Some_0.mapping_2m[v].addr != entry.addr
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre.process_map[p].pagetable->Some_0.mapping_4k[v]]
                pre.process_map.dom().contains(p) && pre.process_map[p].pagetable is Some && pre.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> !(entry.addr <= pre.process_map[p].pagetable->Some_0.mapping_4k[v].addr < entry.addr + 0x200000)
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre.process_map[p].iommu_table->Some_0.mapping_4k[v]]
                pre.process_map.dom().contains(p) && pre.process_map[p].iommu_table is Some && pre.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
                ==> !(entry.addr <= pre.process_map[p].iommu_table->Some_0.mapping_4k[v].addr < entry.addr + 0x200000)
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { quota_2m: (thread.quota_2m - 1) as usize, syscall_progress: mmap_2m_progress_after_leaf(thread.syscall_progress), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { mapping_2m: pagetable.mapping_2m.insert(va, entry), ..pagetable }), ..process }),
                ..pre
            })
        },
    ensures
        mmap_2m_leaf_step_pre(pre, cpu_id),
        mmap_2m_leaf_step(pre, post, cpu_id),
{ reveal(mmap_2m_leaf_step_pre); reveal(mmap_2m_leaf_step); }

/// Directory steps appended after range steps that start at `start` are range steps.
pub(super) proof fn mmap_2m_range_steps_from_directory(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_2m_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            &&& mmap_2m_directory_step_pre(steps.view()[j].old_u, cpu_id)
            &&& mmap_2m_directory_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_2m_range_step); }

/// A leaf step pushed after range steps that start at `start` is a range step.
pub(super) proof fn mmap_2m_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        mmap_2m_leaf_step_pre(steps.view().last().old_u, cpu_id),
        mmap_2m_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_2m_range_step); }

/// A downgrade step pushed after range steps that start at `start` is a range step.
pub(super) proof fn mmap_2m_range_steps_from_downgrade(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        mmap_2m_downgrade_step_pre(steps.view().last().old_u, cpu_id),
        mmap_2m_downgrade_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_2m_range_step); }

/// The hold step recorded on an empty trace is the partial trace after holding.
pub(super) proof fn mmap_2m_trace_hold_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange2M)
    requires
        before.len() == 0,
        steps.view() == record_user_view_change(before, pre, post),
        mmap_2m_hold_step_pre(pre, cpu_id, range),
        mmap_2m_hold_step(pre, post, cpu_id),
    ensures
        mmap_2m_trace_after_hold(steps.view(), cpu_id, range),
        steps.view().len() == 1,
{ reveal(mmap_2m_hold_step_pre); reveal(mmap_2m_hold_step); reveal(mmap_2m_trace_after_hold); }

/// The release step recorded after the partial trace after holding is the failure trace.
pub(super) proof fn mmap_2m_trace_release_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize)
    requires
        mmap_2m_trace_after_hold(before, cpu_id, mmap_2m_syscall_va_range(va, range)),
        steps.view() == record_user_view_change(before, pre, post),
        mmap_2m_release_step_pre(pre, cpu_id),
        mmap_2m_release_step(pre, post, cpu_id),
    ensures
        mmap_2m_syscall_failure_trace(steps.view(), cpu_id, va, range),
        steps.view()[1].old_u == pre,
{ reveal(mmap_2m_release_step_pre); reveal(mmap_2m_release_step); reveal(mmap_2m_trace_after_hold); reveal(mmap_2m_syscall_failure_trace); }

/// The enter step pushed onto an empty trace to read, or onto the partial trace after holding to fill, is the partial trace
/// after entering.
pub(super) proof fn mmap_2m_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange2M, phase: Mmap2mPhase)
    requires
        phase is Read || phase is Fill,
        phase is Read ==> before.len() == 0,
        phase is Fill ==> mmap_2m_trace_after_hold(before, cpu_id, range),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_2m_enter_step_pre(pre, cpu_id, range, phase),
        mmap_2m_enter_step(pre, post, cpu_id, range, phase),
    ensures
        mmap_2m_trace_after_enter(steps.view(), cpu_id, range, phase),
{ reveal(mmap_2m_trace_after_hold); reveal(mmap_2m_trace_after_enter); }

/// The range steps appended after the enter step give the partial trace after mapping the range.
pub(super) proof fn mmap_2m_trace_range_steps(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, range: VaRange2M, phase: Mmap2mPhase)
    requires
        mmap_2m_trace_after_enter(before, cpu_id, range, phase),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len + NUM_CPUS + 2,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
    ensures
        mmap_2m_trace_after_range(steps.view(), cpu_id, range, phase),
{ reveal(mmap_2m_trace_after_enter); reveal(mmap_2m_trace_after_range); }

/// The exit step pushed after the mapped partial trace completes the syscall trace.
pub(super) proof fn mmap_2m_trace_exit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, phase: Mmap2mPhase)
    requires
        mmap_2m_trace_after_range(before, cpu_id, mmap_2m_syscall_va_range(va, range), phase),
        phase is Read || phase is Fill,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_2m_exit_step_pre(pre, cpu_id),
        mmap_2m_exit_step(pre, post, cpu_id),
    ensures
        mmap_2m_syscall_trace(steps.view(), cpu_id, va, range, phase),
{ reveal(mmap_2m_trace_after_range); reveal(mmap_2m_syscall_trace); }

/// The caller write-holding its cpu and thread and holding the pagetable of the thread's present process in either mode with
/// progress at the first page of `range` outside the fill phase, while the thread's container exists, satisfies the flush
/// precondition and projects its K anchors.
pub(super) proof fn mmap_2m_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    range: VaRange2M, phase: Mmap2mPhase,
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
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
        !(phase is Fill),
    ensures
        mmap_2m_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid,
{
    reveal(mmap_2m_flush_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// TLB flushes of the caller's PCID recorded from `entry` after range steps that start at `start`, while the caller
/// write-holds its cpu and thread and holds the pagetable of the thread's present process with progress at the first page and
/// the thread's container exists, leave only range steps.
pub(super) proof fn mmap_2m_tlb_flush_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, range: VaRange2M, phase: Mmap2mPhase,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_2m_range_step(before[j], cpu_id),
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
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
        !(phase is Fill),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, entry.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid)
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
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
{
    mmap_2m_flush_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range, phase);
    reveal(mmap_2m_range_step); reveal(mmap_2m_flush_step_pre); reveal(unmap_4k_tlb_flush_step);
}

/// Releasing this thread's read hold on the cpu set of its container from `snap` to `pre`, where `pre` extends the step's
/// start `snap` by page-table ghost state and by that release, while the caller write-holds its cpu and thread and holds the
/// pagetable of the thread's present process with progress at the first page: the projection changes exactly when the cpu
/// set's projected lock does, and then by a flushed step.
pub(super) proof fn mmap_2m_flushed_step_from_k(
    snap: &KernelK, pre: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    pagetable: RwLockPageTableRoot, range: VaRange2M, phase: Mmap2mPhase,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
        !(phase is Fill),
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
        !(pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).locking_thread() is Write),
    ensures
        (kernel_k_to_kernel_u(*snap) == kernel_k_to_kernel_u(*pre)) == (snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u()
            == pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u()),
        mmap_2m_range_step(KernelStep { old_u: kernel_k_to_kernel_u(*snap), new_u: kernel_k_to_kernel_u(*pre) }, cpu_id),
{
    let ghost_tables = KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*snap };
    reveal(kernel_cpu_nonlock_fields_unchanged); kernel_u_domains_projection(snap);
    kernel_cpu_tlb_updated_implies_u_step(snap, &ghost_tables);
    kernel_cpu_set_lock_mode_changed_implies_u_step(&ghost_tables, pre, ctn_ptr);
    kernel_container_projection_at(snap, ctn_ptr);
    mmap_2m_flush_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range, phase);
    reveal(mmap_2m_range_step); reveal(mmap_2m_flush_step_pre); reveal(mmap_2m_flushed_step_pre); reveal(mmap_2m_flushed_step);
    let pre_u = kernel_k_to_kernel_u(*snap);
    let cpu_set_lock = pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u();
    if snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u() == cpu_set_lock {
        assert_maps_equal!(pre_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock, ..pre_u.container_map[ctn_ptr] }), pre_u.container_map);
    }
}

/// The record of a flushed step from `old_u` to `new_u` after range steps that start at `start` leaves only range steps.
pub(super) proof fn mmap_2m_flushed_range_steps_from_u(steps: &KernelSteps, before: Seq<KernelStep>, start: int, old_u: KernelU, new_u: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_2m_range_step(before[j], cpu_id),
        steps.view() == record_user_view_change(before, old_u, new_u),
        mmap_2m_range_step(KernelStep { old_u, new_u }, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
{}

/// A container 4K quota credit to the container `ctn_ptr` of the caller's current thread `thrd_ptr`, recorded from a state where the
/// caller write-holds its cpu and thread and holds its pagetable with progress at the first page of `range` outside the fill phase,
/// after range steps that start at `start` leaves only range steps.
pub(super) proof fn mmap_2m_l1_reclaim_range_steps_from_u(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, range: VaRange2M, phase: Mmap2mPhase,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_2m_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        kernel_u_container_quota_4k_increased(steps.view().last().old_u, steps.view().last().new_u, ctn_ptr),
        mmap_4k_locked(steps.view().last().old_u, cpu_id),
        steps.view().last().old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        steps.view().last().old_u.thread_map[thrd_ptr].owning_container == ctn_ptr,
        steps.view().last().old_u.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Mmap2m { range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
        !(phase is Fill),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_2m_range_step); reveal(mmap_2m_l1_reclaim_step_pre); }
} // verus!

use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread, its process, and its pagetable decide the mmap result `ret`. A range result
/// checked on `cur`, which has the entry pagetable's mappings, is exact: a range found in use under a read lock has every leaf it
/// covers present, since its 2M windows are held with their leaves present and every 1G leaf is present, and `found` names a 4K
/// leaf in its index interval or, if there is none, some page is covered by a 2M or 1G leaf. Without a checked table, a range
/// result is only known to be success or in use.
pub(super) proof fn mmap_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType, cur: Option<WholePageTable<PT_TYPE>>,
    found: Option<(L4Index, L3Index, L2Index, L1Index)>)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        cur is Some && ret is ErrorVaInUse ==> spec_va_range_4k(va, range).wf(),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = spec_va_range_4k(va, range);
            let start = spec_va2index(va);
            let end = spec_va2index(va_range.view()[range - 1]);
            let checked = cur->Some_0;
            let clear = checked.spec_mapping_4k_range_empty(start, end) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> {
                let idx = spec_va2index(va_range.view()[j]);
                &&& !checked.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
                &&& !checked.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
                &&& !checked.mapping_4k().dom().contains(va_range.view()[j])
            };
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& ret is ErrorNoQuota ==> !thread.being_killed() && thread.view().quota_4k < 4 * range
            &&& (ret is Success || ret is Error || ret is ErrorVaInUse) ==> !thread.being_killed() && thread.view().quota_4k >= 4 * range && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& (ret is Success || ret is ErrorVaInUse) ==> !process.view().zombie && spec_v2l4index(va) >= table.kernel_l4_end()
            &&& cur is Some && (ret is Success || ret is ErrorVaInUse) ==> {
                &&& checked.mapping_4k() == table.mapping_4k()
                &&& checked.mapping_2m() == table.mapping_2m()
                &&& checked.mapping_1g() == table.mapping_1g()
            }
            &&& cur is Some && ret is ErrorVaInUse ==> checked.leaves_present() || {
                &&& forall|w: WindowVa| #![trigger va_range_2m_windows(va_range).contains(w)] va_range_2m_windows(va_range).contains(w) ==> checked.window_leaves_present(w)
                &&& forall|v: VAddr| #![trigger checked.mapping_1g().dom().contains(v)] checked.mapping_1g().dom().contains(v) ==> checked.mapping_1g().spec_index(v).present
                &&& found is Some ==> {
                    let f = found->Some_0;
                    &&& pei_valid(f.0) && pei_valid(f.1) && pei_valid(f.2) && pei_valid(f.3)
                    &&& spec_l4_index_path_le(start, f)
                    &&& spec_l4_index_path_le(f, end)
                    &&& checked.mapping_4k().dom().contains(spec_index2va(f))
                }
                &&& found is None ==> checked.spec_mapping_4k_range_empty(start, end)
                &&& found is None ==> checked.spec_mapping_4k_va_range_empty(va, va_range.view()[range - 1])
            }
            &&& ret is Error ==> spec_v2l4index(va) < table.kernel_l4_end()
            &&& cur is Some && ret is Success ==> clear
            &&& cur is Some && ret is ErrorVaInUse ==> !clear
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is Error || ret is Success || ret is ErrorVaInUse
        },
    ensures
        cur is Some || !(ret is Success || ret is ErrorVaInUse) ==> mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
        ret is Success || ret is ErrorVaInUse ==> mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) is Success
            || mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) is ErrorVaInUse,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is Error || ret is ErrorVaInUse { kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(thread.owning_proc).view().pagetable); }
        if ret is Success || ret is ErrorVaInUse { kernel_pagetable_mappings_projection_at(krnl, thread.owning_proc); kernel_process_projection_at(krnl, thread.owning_proc); }
        if cur is Some && ret is ErrorVaInUse {
            let checked = cur->Some_0;
            let va_range = spec_va_range_4k(va, range);
            let last = va_range.view()[range - 1];
            let (s4, s3, s2, s1) = spec_va2index(va);
            let (e4, e3, e2, e1) = spec_va2index(last);
            let u_table = kernel_k_to_kernel_u(*krnl).process_map[thread.owning_proc].pagetable->Some_0;
            assert(last == spec_va_add_range(va, (range - 1) as usize) && spec_va_4k_valid(last)) by { va_range.wf_implies_view_index_is_start_plus_offset(); };
            assert(spec_index2va((s4, s3, s2, s1)) == va && spec_index2va((e4, e3, e2, e1)) == last && pei_valid(s4) && pei_valid(s3) && pei_valid(s2) && pei_valid(s1)
                && pei_valid(e4) && pei_valid(e3) && pei_valid(e2) && pei_valid(e1)) by { broadcast use spec_va_4k_valid_index_roundtrip; };
            assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le((s4, s3, s2, s1), (l4i, l3i, l2i, l1i))
                && spec_l4_index_path_le((l4i, l3i, l2i, l1i), (e4, e3, e2, e1)) && #[trigger] u_table.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                implies ({
                    let k = ((spec_index2va((l4i, l3i, l2i, l1i)) - va) / 4096) as int;
                    &&& 0 <= k < range
                    &&& va_range.view()[k] == spec_index2va((l4i, l3i, l2i, l1i))
                }) by {
                let x = spec_index2va((l4i, l3i, l2i, l1i));
                assert(spec_index2va((s4, s3, s2, s1)) <= spec_index2va((l4i, l3i, l2i, l1i)) && spec_index2va((l4i, l3i, l2i, l1i)) <= spec_index2va((e4, e3, e2, e1))
                    && (spec_index2va((l4i, l3i, l2i, l1i)) - spec_index2va((s4, s3, s2, s1))) % 4096 == 0) by (bit_vector)
                    requires
                        s4 < 512 && s3 < 512 && s2 < 512 && s1 < 512 && e4 < 512 && e3 < 512 && e2 < 512 && e1 < 512 && l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512,
                        s4 < l4i || (s4 == l4i && (s3 < l3i || (s3 == l3i && (s2 < l2i || (s2 == l2i && s1 <= l1i))))),
                        l4i < e4 || (l4i == e4 && (l3i < e3 || (l3i == e3 && (l2i < e2 || (l2i == e2 && l1i <= e1))))),
                ;
                let k = (x - va) / 4096;
                assert(k * 4096 == x - va && k < range) by (nonlinear_arith)
                    requires
                        k == (x - va) / 4096,
                        (x - va) % 4096 == 0,
                        va <= x <= last,
                        last == va + (range - 1) * 4096,
                        range > 0,
                ;
                assert(va_range.view()[k as int] == spec_va_add_range(va, k as usize)) by { va_range.wf_implies_view_index_is_start_plus_offset(); };
            };
            if !checked.leaves_present() {
                if found is Some {
                    let f = found->Some_0;
                    let fv = spec_index2va((f.0, f.1, f.2, f.3));
                    va_range_2m_windows_contains_window_of_every_va_in_range(va_range);
                    spec_va_4k_index_roundtrip_at(va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                    spec_va_4k_index_roundtrip_at(fv, f.0, f.1, f.2, f.3);
                    assert(checked.mapping_4k().spec_index(fv).present);
                    assert(u_table.mapping_4k.dom().contains(fv));
                } else { reveal(WholePageTable::spec_mapping_4k_va_range_empty); va_range_2m_windows_contains_window_of_first_n_pages(va_range, range as int); }
            }
        }
    }
}

/// The entry state's running thread's container is in the user view, as the enter step requires.
pub(super) proof fn mmap_4k_enter_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
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
pub(super) proof fn mmap_4k_enter_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize, range: VaRange4K, phase: Mmap4kPhase, windows: Map<WindowVa, LockStateU>)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        range == spec_va_range_4k(va, len),
        range.wf(),
        mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_locking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range, cpu_id),
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
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(SyscallProgress::Mmap4k { range, mapped: 0, directory: Mmap4kDirectory::None, phase }), ..thread
                }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: if phase is Read { pagetable.lock_state.with_reader(cpu_id) } else { LockStateU::WriteLocked { writer: cpu_id } }, pagetable_window_locks: windows, ..pagetable }),
                    ..process
                }),
                ..pre
            })
        },
    ensures
        mmap_4k_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range, phase),
        mmap_4k_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range, phase),
{
    kernel_cpu_projection_at(krnl, cpu_id); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_process_projection_at(krnl, prc_ptr);
    reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step);
}

/// Entering to fill in two sections, first locking the pagetable `pagetable_ptr` and recording the first page from `krnl`'s
/// projection to `mid`, then locking the range's existing windows from `mid` to `post` with the thread's quota and progress kept,
/// is the enter step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_4k_fill_enter_step_from_u(krnl: &KernelK, mid: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize, range: VaRange4K, windows: Map<WindowVa, LockStateU>, quota: usize, progress: Option<SyscallProgress>,
    owner: RwLockProcessPtr)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        range == spec_va_range_4k(va, len),
        range.wf(),
        mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_locking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range, cpu_id),
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
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(SyscallProgress::Mmap4k { range, mapped: 0, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Fill }),
                    ..thread
                }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..process.pagetable->Some_0 }), ..process }),
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
        mmap_4k_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range, Mmap4kPhase::Fill),
        mmap_4k_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range, Mmap4kPhase::Fill),
{
    let pre = kernel_k_to_kernel_u(*krnl);
    let process = pre.process_map.spec_index(prc_ptr);
    kernel_process_projection_at(krnl, prc_ptr);
    assert(post.thread_map =~= mid.thread_map);
    assert(post.process_map =~= pre.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process
    }));
    mmap_4k_enter_step_from_u(krnl, post, cpu_id, prc_ptr, thrd_ptr, pagetable_ptr, va, len, range, Mmap4kPhase::Fill, windows);
}

/// The entry state's K facts on the running cpu and its current thread, both unlocked, with the syscall result success or in
/// use there, give the hold step's precondition.
pub(super) proof fn mmap_4k_hold_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, va: VAddr, len: usize)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        spec_va_range_4k(va, len).wf(),
        len > 0,
        mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success || mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is ErrorVaInUse,
        !krnl.cpu_arr.spec_index(cpu_id).view().locked(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        !krnl.thrd_mp.spec_index(thrd_ptr).locked(),
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.ctn_mp.dom().contains(krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container),
    ensures mmap_4k_hold_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, spec_va_range_4k(va, len)),
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_process_projection_at(krnl, prc_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
    reveal(mmap_4k_hold_step_pre);
}

/// Write-locking the caller's cpu and its current thread `thrd_ptr` with the cpu inside its kernel step and changing nothing
/// else is the hold step on `pre`/`post`.
pub(super) proof fn mmap_4k_hold_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..pre.thread_map.spec_index(thrd_ptr) }),
            ..pre
        }),
    ensures mmap_4k_hold_step(pre, post, cpu_id),
{ reveal(mmap_4k_hold_step); }

/// Unlocking the caller's write-locked cpu and its current thread `thrd_ptr` with no progress recorded, returning the cpu to
/// its trap path, and changing nothing else is the release step on `pre`/`post`.
pub(super) proof fn mmap_4k_release_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
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
        mmap_4k_release_step_pre(pre, cpu_id),
        mmap_4k_release_step(pre, post, cpu_id),
{ reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); }

/// Turning the fill phase's write lock on the pagetable `pagetable_ptr` into a read lock with its window locks kept as `windows` is
/// the downgrade step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_4k_downgrade_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
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
            let filled = SyscallProgress::Mmap4k { range: progress->Mmap4k_range, mapped: progress->Mmap4k_mapped, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Filled };
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
            &&& progress->Mmap4k_phase is Fill
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(filled), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: process.pagetable->Some_0.lock_state.with_reader(cpu_id), pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process
                }),
                ..pre
            })
        },
    ensures
        mmap_4k_downgrade_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_4k_downgrade_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); }

/// Publishing the next recorded page under the mmap locks is the leaf step from `krnl`'s projection to `post`. The published
/// page is `Owned4k` in `krnl`, so no IOMMU table of `krnl` maps it and no 2M or 1G frame of `krnl` contains it.
pub(super) proof fn mmap_4k_leaf_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, va: VAddr)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let process = pre.process_map.spec_index(prc_ptr);
            let progress = thread.syscall_progress->Some_0;
            let entry = post.process_map.spec_index(prc_ptr).pagetable->Some_0.mapping_4k.spec_index(va);
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& pre.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& !(process.pagetable->Some_0.lock_state is Unlocked)
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
            &&& !(progress->Mmap4k_phase is Fill)
            &&& progress->Mmap4k_mapped < progress->Mmap4k_range.len
            &&& progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int] == va
            &&& thread.quota_4k >= 1
            &&& !process.pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& entry.present
            &&& entry.write
            &&& !entry.execute_disable
            &&& entry.owning_container.view() == thread.owning_container
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre.process_map[p].pagetable->Some_0.mapping_4k[v]]
                pre.process_map.dom().contains(p) && pre.process_map[p].pagetable is Some && pre.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> pre.process_map[p].pagetable->Some_0.mapping_4k[v].addr != entry.addr
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(entry.addr)).view().view().state is Owned4k
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { mapping_4k: process.pagetable->Some_0.mapping_4k.insert(va, entry), ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        },
    ensures
        mmap_4k_leaf_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_4k_leaf_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{
    let pre = kernel_k_to_kernel_u(*krnl);
    let addr = post.process_map.spec_index(prc_ptr).pagetable->Some_0.mapping_4k.spec_index(va).addr;
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre.process_map[p].iommu_table->Some_0.mapping_4k[v]]
        pre.process_map.dom().contains(p) && pre.process_map[p].iommu_table is Some && pre.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
        ==> pre.process_map[p].iommu_table->Some_0.mapping_4k[v].addr != addr) by { reveal(kernel_k_to_kernel_u); reveal(process_iommu_table_wf); reveal(page_iommu_table_wf); };
    kernel_owned_4k_page_implies_u_outside_2m_mapping_frames(*krnl, addr); kernel_owned_4k_page_implies_u_outside_1g_mapping_frames(*krnl, addr);
    reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step);
}

/// Clearing the progress and releasing the mmap locks after the whole recorded range `range` is mapped, setting the window locks
/// of pagetable `pagetable_ptr` to `windows`, those of `krnl` after unlocking `range`, returning the cpu to its trap path, and
/// dropping the cpu's read hold on the pagetable, is the exit step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_4k_exit_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, range: VaRange4K, windows: Map<WindowVa, LockStateU>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(cpu_id),
        windows == pagetable_window_locks_after_unlocking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range),
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
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
            &&& !(progress->Mmap4k_phase is Fill)
            &&& progress->Mmap4k_range == range
            &&& progress->Mmap4k_mapped == range.len
            &&& progress->Mmap4k_directory is None
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: process.pagetable->Some_0.lock_state.without_reader(cpu_id), pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process
                }),
                ..pre
            })
        },
    ensures
        mmap_4k_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_4k_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); }

/// Directory steps appended after range steps that start at `start` are range steps.
pub(super) proof fn mmap_4k_range_steps_from_directory(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            &&& mmap_4k_directory_step_pre(steps.view()[j].old_u, cpu_id)
            &&& mmap_4k_directory_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_4k_range_step); }

/// A leaf step pushed after range steps that start at `start` is a range step.
pub(super) proof fn mmap_4k_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        mmap_4k_leaf_step_pre(steps.view().last().old_u, cpu_id),
        mmap_4k_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_4k_range_step); }

/// A downgrade step pushed after range steps that start at `start` is a range step.
pub(super) proof fn mmap_4k_range_steps_from_downgrade(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        mmap_4k_downgrade_step_pre(steps.view().last().old_u, cpu_id),
        mmap_4k_downgrade_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_4k_range_step); }

/// The hold step recorded on an empty trace is the partial trace after holding.
pub(super) proof fn mmap_4k_trace_hold_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K)
    requires
        before.len() == 0,
        steps.view() == record_user_view_change(before, pre, post),
        mmap_4k_hold_step_pre(pre, cpu_id, range),
        mmap_4k_hold_step(pre, post, cpu_id),
    ensures
        mmap_4k_trace_after_hold(steps.view(), cpu_id, range),
        steps.view().len() == 1,
{ reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); reveal(mmap_4k_trace_after_hold); }

/// The release step recorded after the partial trace after holding is the failure trace.
pub(super) proof fn mmap_4k_trace_release_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize)
    requires
        mmap_4k_trace_after_hold(before, cpu_id, spec_va_range_4k(va, range)),
        steps.view() == record_user_view_change(before, pre, post),
        mmap_4k_release_step_pre(pre, cpu_id),
        mmap_4k_release_step(pre, post, cpu_id),
    ensures
        mmap_4k_syscall_failure_trace(steps.view(), cpu_id, va, range),
        steps.view()[1].old_u == pre,
{ reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); reveal(mmap_4k_trace_after_hold); reveal(mmap_4k_syscall_failure_trace); }

/// The enter step pushed onto an empty trace to read, or onto the partial trace after holding to fill, is the partial trace
/// after entering.
pub(super) proof fn mmap_4k_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K, phase: Mmap4kPhase)
    requires
        phase is Read || phase is Fill,
        phase is Read ==> before.len() == 0,
        phase is Fill ==> mmap_4k_trace_after_hold(before, cpu_id, range),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_4k_enter_step_pre(pre, cpu_id, range, phase),
        mmap_4k_enter_step(pre, post, cpu_id, range, phase),
    ensures
        mmap_4k_trace_after_enter(steps.view(), cpu_id, range, phase),
{ reveal(mmap_4k_trace_after_hold); reveal(mmap_4k_trace_after_enter); }

/// The range steps appended after the enter step give the partial trace after mapping the range.
pub(super) proof fn mmap_4k_trace_range_steps(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K, phase: Mmap4kPhase)
    requires
        mmap_4k_trace_after_enter(before, cpu_id, range, phase),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len + 1,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
    ensures
        mmap_4k_trace_after_range(steps.view(), cpu_id, range, phase),
{ reveal(mmap_4k_trace_after_enter); reveal(mmap_4k_trace_after_range); }

/// The exit step pushed after the mapped partial trace completes the syscall trace.
pub(super) proof fn mmap_4k_trace_exit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, phase: Mmap4kPhase)
    requires
        mmap_4k_trace_after_range(before, cpu_id, spec_va_range_4k(va, range), phase),
        phase is Read || phase is Fill,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_4k_exit_step_pre(pre, cpu_id),
        mmap_4k_exit_step(pre, post, cpu_id),
    ensures
        mmap_4k_syscall_trace(steps.view(), cpu_id, va, range, phase),
{ reveal(mmap_4k_trace_after_range); reveal(mmap_4k_syscall_trace); }
} // verus!

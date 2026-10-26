use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread, its process, and its pagetable decide the mmap result `ret`. A range result
/// checked on `cur`, which has the entry pagetable's mappings, is exact: a range found in use under a read lock has every leaf it
/// covers present, since its 2M windows are held and every 2M and 1G leaf is present, and `found` names a 4K leaf in its index
/// interval or, if there is none, some page is covered by a 2M or 1G leaf. Without a checked table, a range result is only known
/// to be success or in use.
pub(super) proof fn mmap_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType, cur: Option<PageTableC<PT_TYPE>>,
    found: Option<(L4Index, L3Index, L2Index, L1Index)>)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        cur is Some && ret is ErrorVaInUse ==> mmap_4k_syscall_va_range(va, range).wf(),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = mmap_4k_syscall_va_range(va, range);
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
            &&& !(ret is CpuIdle) ==> krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
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
                &&& forall|v: VAddr| #![trigger checked.mapping_2m().dom().contains(v)] checked.mapping_2m().dom().contains(v) ==> checked.mapping_2m().spec_index(v).present
                &&& forall|v: VAddr| #![trigger checked.mapping_1g().dom().contains(v)] checked.mapping_1g().dom().contains(v) ==> checked.mapping_1g().spec_index(v).present
                &&& found is Some ==> {
                    let f = found->Some_0;
                    &&& pei_valid(f.0) && pei_valid(f.1) && pei_valid(f.2) && pei_valid(f.3)
                    &&& spec_l4_index_path_le(start, f)
                    &&& spec_l4_index_path_le(f, end)
                    &&& checked.mapping_4k().dom().contains(spec_index2va(f))
                }
                &&& found is None ==> checked.spec_mapping_4k_range_empty(start, end)
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
    let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is Error || ret is ErrorVaInUse { kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(thread.owning_proc).view().pagetable); }
        if ret is Success || ret is ErrorVaInUse { kernel_pagetable_mappings_projection_at(krnl, thread.owning_proc); kernel_process_projection_at(krnl, thread.owning_proc); }
        if cur is Some && ret is ErrorVaInUse && !cur->Some_0.leaves_present() {
            let checked = cur->Some_0;
            let va_range = mmap_4k_syscall_va_range(va, range);
            let u_table = kernel_k_to_kernel_u(*krnl).process_map[thread.owning_proc].pagetable->Some_0;
            va_range.va_range_lemma();
            if found is Some {
                let f = found->Some_0;
                let fv = spec_index2va((f.0, f.1, f.2, f.3));
                va_range_2m_windows_contains_window_of_every_va_in_range(va_range);
                spec_va_4k_index_roundtrip_at(va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                spec_va_4k_index_roundtrip_at(fv, f.0, f.1, f.2, f.3);
                assert(checked.mapping_4k().spec_index(fv).present);
                assert(u_table.mapping_4k.dom().contains(fv));
            } else {
                broadcast use PageTableC::mapping_4k_index_range_empty_implies_va_empty_at, spec_va_4k_valid_index_roundtrip;
            }
        }
    }
}

/// The entry state's running thread's container is in the user view, as the enter step requires.
pub(super) proof fn mmap_4k_enter_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.ctn_mp.dom().contains(krnl.thr_mp.spec_index(thread_ptr).view().owning_container),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr).owning_container),
{ kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); }

/// Write-locking the caller's cpu and thread, which entering to fill already holds, locking its pagetable for `phase`, and
/// recording the first page is the enter step on `pre`/`post` when the syscall succeeds on `pre`.
pub(super) proof fn mmap_4k_enter_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr, len: usize,
    range: VaRange4K, phase: Mmap4kPhase)
    requires
        index_valid(NUM_CPUS, cpu_id),
        range == mmap_4k_syscall_va_range(va, len),
        range.wf(),
        mmap_4k_syscall_result(pre, cpu_id, va, len) is Success,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let pagetable = process.pagetable->Some_0;
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.syscall_progress is None
            &&& thread.owning_proc == process_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& process.pagetable is Some
            &&& !(phase is Filled)
            &&& phase is Read ==> cpu.lock_state is Unlocked && thread.lock_state is Unlocked && !(pagetable.lock_state is WriteLocked)
            &&& phase is Fill ==> cpu.lock_state is WriteLocked && thread.lock_state is WriteLocked && pagetable.lock_state is Unlocked
        },
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Mmap4k { range, mapped: 0, directory: Mmap4kDirectory::None, phase }), ..pre.thread_map.spec_index(thread_ptr)
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: if phase is Read { LockStateU::ReadLocked } else { LockStateU::WriteLocked }, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
                ..pre.process_map.spec_index(process_ptr)
            }),
            ..pre
        }),
    ensures
        mmap_4k_enter_step_pre(pre, cpu_id, range, phase),
        mmap_4k_enter_step(pre, post, cpu_id, range, phase),
{ reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); }

/// The entry state's K facts on the running cpu and its current thread, both unlocked, with the syscall result success or in
/// use there, give the hold step's precondition.
pub(super) proof fn mmap_4k_hold_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr, len: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        mmap_4k_syscall_va_range(va, len).wf(),
        len > 0,
        mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success || mmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is ErrorVaInUse,
        !krnl.cpu_arr.spec_index(cpu_id).view().locked(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        !krnl.thr_mp.spec_index(thread_ptr).locked(),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.ctn_mp.dom().contains(krnl.thr_mp.spec_index(thread_ptr).view().owning_container),
    ensures mmap_4k_hold_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, mmap_4k_syscall_va_range(va, len)),
{ kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_process_projection_at(krnl, process_ptr); reveal(mmap_4k_hold_step_pre); }

/// Write-locking the caller's cpu and its current thread `thread_ptr` and changing nothing else is the hold step on
/// `pre`/`post`.
pub(super) proof fn mmap_4k_hold_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
    ensures mmap_4k_hold_step(pre, post, cpu_id),
{ reveal(mmap_4k_hold_step); }

/// Unlocking the caller's write-locked cpu and its current thread `thread_ptr` with no progress recorded and changing nothing
/// else is the release step on `pre`/`post`.
pub(super) proof fn mmap_4k_release_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_array[cpu_id as int].lock_state is WriteLocked,
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map.dom().contains(thread_ptr),
        pre.thread_map.spec_index(thread_ptr).lock_state is WriteLocked,
        pre.thread_map.spec_index(thread_ptr).syscall_progress is None,
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
    ensures
        mmap_4k_release_step_pre(pre, cpu_id),
        mmap_4k_release_step(pre, post, cpu_id),
{ reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); }

/// Turning the fill phase's write lock on the pagetable into a read lock is the downgrade step on `pre`/`post`.
pub(super) proof fn mmap_4k_downgrade_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            let filled = SyscallProgress::Mmap4k { range: progress->Mmap4k_range, mapped: progress->Mmap4k_mapped, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Filled };
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == process_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
            &&& progress->Mmap4k_phase is Fill
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(filled), ..thread }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        },
    ensures
        mmap_4k_downgrade_step_pre(pre, cpu_id),
        mmap_4k_downgrade_step(pre, post, cpu_id),
{ reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); }

/// Publishing the next recorded page under the mmap locks is the leaf step from `krnl`'s projection to `post`. The published
/// page is `Owned4k` in `krnl`, so no IOMMU table of `krnl` maps it.
pub(super) proof fn mmap_4k_leaf_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            let entry = post.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k.spec_index(va);
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == process_ptr
            &&& pre.process_map.dom().contains(process_ptr)
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
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { mapping_4k: process.pagetable->Some_0.mapping_4k.insert(va, entry), ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        },
    ensures
        mmap_4k_leaf_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_4k_leaf_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{
    let pre = kernel_k_to_kernel_u(*krnl);
    let addr = post.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k.spec_index(va).addr;
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre.process_map[p].iommu_table->Some_0.mapping_4k[v]]
        pre.process_map.dom().contains(p) && pre.process_map[p].iommu_table is Some && pre.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
        ==> pre.process_map[p].iommu_table->Some_0.mapping_4k[v].addr != addr) by { reveal(kernel_k_to_kernel_u); reveal(process_iommu_table_match); reveal(page_iommu_table_wf); };
    reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step);
}

/// Clearing the progress and releasing the mmap locks after the whole range is mapped, leaving the pagetable in `table_lock`, is
/// the exit step on `pre`/`post`.
pub(super) proof fn mmap_4k_exit_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, table_lock: LockStateU)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == process_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& !(process.pagetable->Some_0.lock_state is Unlocked)
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
            &&& !(progress->Mmap4k_phase is Fill)
            &&& progress->Mmap4k_mapped == progress->Mmap4k_range.len
            &&& progress->Mmap4k_directory is None
        },
        table_lock is Unlocked || table_lock is ReadLocked,
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map.spec_index(thread_ptr) }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: table_lock, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
                ..pre.process_map.spec_index(process_ptr)
            }),
            ..pre
        }),
    ensures
        mmap_4k_exit_step_pre(pre, cpu_id),
        mmap_4k_exit_step(pre, post, cpu_id),
{ reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); }

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
        mmap_4k_trace_after_hold(before, cpu_id, mmap_4k_syscall_va_range(va, range)),
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
        mmap_4k_trace_after_range(before, cpu_id, mmap_4k_syscall_va_range(va, range), phase),
        phase is Read || phase is Fill,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_4k_exit_step_pre(pre, cpu_id),
        mmap_4k_exit_step(pre, post, cpu_id),
    ensures
        mmap_4k_syscall_trace(steps.view(), cpu_id, va, range, phase),
{ reveal(mmap_4k_trace_after_range); reveal(mmap_4k_syscall_trace); }
} // verus!

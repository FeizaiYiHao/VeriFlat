use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, process, and pagetable decide the mmap result `ret`. A range in use has page `at` whose slot holds the 2M leaf `found_2m`, the 4K leaf `found_4k`, or else a 1G leaf.
pub(super) proof fn mmap_1g_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType, at: int, found_2m: Option<L2Index>,
    found_4k: Option<(L4Index, L3Index, L2Index, L1Index)>)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - range * 0x40000000 || !spec_va_1g_range_valid(va, range)),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = spec_va_range_1g(va, range);
            let at_va = va_range.view()[at];
            let at_idx = spec_va2index(at_va);
            let clear = forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> {
                let idx = spec_va2index(va_range.view()[j]);
                &&& !table.mapping_1g().dom().contains(va_range.view()[j])
                &&& forall|l2i: L2Index| #![trigger table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))] pei_valid(l2i)
                    ==> !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))
                &&& forall|l2i: L2Index, l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))] pei_valid(l2i) && pei_valid(l1i)
                    ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))
            };
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& ret is ErrorNoQuota ==> !thread.being_killed() && (thread.view().quota_1g < range || thread.view().quota_4k < range)
            &&& (ret is Success || ret is ErrorVaInUse) ==> !thread.being_killed() && thread.view().quota_1g >= range && thread.view().quota_4k >= range
            &&& (ret is Success || ret is ErrorVaInUse) ==> !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable) && table.leaves_present()
                && table.kernel_l4_end() == KERNEL_MEM_END_L4INDEX
            &&& ret is Success ==> clear
            &&& ret is ErrorVaInUse ==> {
                &&& 0 <= at < range
                &&& found_2m is Some ==> pei_valid(found_2m->Some_0) && table.mapping_2m().dom().contains(spec_index2va((at_idx.0, at_idx.1, found_2m->Some_0, 0)))
                &&& found_4k is Some ==> {
                    let f = found_4k->Some_0;
                    &&& f.0 == at_idx.0 && f.1 == at_idx.1 && pei_valid(f.2) && pei_valid(f.3)
                    &&& table.mapping_4k().dom().contains(spec_index2va(f))
                }
                &&& found_2m is None && found_4k is None ==> table.mapping_1g().dom().contains(at_va)
            }
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is Success || ret is ErrorVaInUse
        }),
    ensures
        mmap_1g_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is ErrorVaInUse {
            let prc_ptr = thread.owning_proc;
            let root = krnl.prc_mp.spec_index(prc_ptr).view().pagetable;
            kernel_l4_end_projection_at(krnl, root); kernel_process_projection_at(krnl, prc_ptr); kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
            let va_range = spec_va_range_1g(va, range);
            assert(spec_v2l4index(va_range.covering_4k_range().start) >= kernel_k_to_kernel_u(*krnl).kernel_l4_end) by { spec_va_1g_valid_index_roundtrip(va); };
            if ret is ErrorVaInUse {
                let u_pt = kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable->Some_0;
                assert(!mmap_1g_slot_unmapped(u_pt, va_range.view()[at]));
            }
        }
    }
}

/// Write-locking the caller's cpu, with the cpu inside its kernel step, its running thread, and the pagetable `pagetable_ptr` of its process, and recording the first page is the enter step from `krnl`'s projection to `post` when the syscall succeeds there.
pub(super) proof fn mmap_1g_enter_step_from_u(
    krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize, range: VaRange1G,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        range == spec_va_range_1g(va, len),
        range.wf(),
        mmap_1g_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        krnl.ctn_mp.dom().contains(krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container),
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
            &&& pagetable.lock_state is Unlocked
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked { writer: cpu_id },
                    syscall_progress: Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: false, flushed: false }), ..thread
                }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..pagetable }), ..process }),
                ..pre
            })
        }),
    ensures
        mmap_1g_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range),
        mmap_1g_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range),
{
    kernel_u_domains_projection(krnl); kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thrd_ptr); kernel_process_projection_at(krnl, prc_ptr);
    reveal(mmap_1g_enter_step_pre); reveal(mmap_1g_enter_step);
}

/// Clearing the progress and unlocking the caller's cpu, which leaves its kernel step for its trap path, its running thread, and the pagetable `pagetable_ptr` of its process, which it write-holds, after the mapped range is the exit step from `krnl`'s projection to `post`.
pub(super) proof fn mmap_1g_exit_step_from_u(krnl: &KernelK, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot)
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
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == prc_ptr
            &&& process.pagetable->Some_0.lock_state == (LockStateU::WriteLocked { writer: cpu_id })
            &&& thread.syscall_progress is Some
            &&& progress is Mmap1g
            &&& progress->Mmap1g_mapped == progress->Mmap1g_range.len
            &&& !progress->Mmap1g_directory
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
                process_map: pre.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        }),
    ensures
        mmap_1g_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        mmap_1g_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, prc_ptr); reveal(mmap_1g_exit_step_pre); reveal(mmap_1g_exit_step); }

/// The enter step pushed onto an empty trace is the partial trace after entering.
pub(super) proof fn mmap_1g_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange1G)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_1g_enter_step_pre(pre, cpu_id, range),
        mmap_1g_enter_step(pre, post, cpu_id, range),
    ensures mmap_1g_trace_after_enter(steps.view(), cpu_id, range),
{ reveal(mmap_1g_trace_after_enter); }

/// The range steps appended after the enter step give the partial trace after mapping the range.
pub(super) proof fn mmap_1g_trace_range_steps(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, range: VaRange1G)
    requires
        mmap_1g_trace_after_enter(before, cpu_id, range),
        before.len() + range.len <= steps.view().len() <= before.len() + 516 * range.len + NUM_CPUS + 1,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
    ensures mmap_1g_trace_after_range(steps.view(), cpu_id, range),
{ reveal(mmap_1g_trace_after_enter); reveal(mmap_1g_trace_after_range); }

/// The exit step pushed after the mapped partial trace completes the syscall trace.
pub(super) proof fn mmap_1g_trace_exit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize)
    requires
        mmap_1g_trace_after_range(before, cpu_id, spec_va_range_1g(va, range)),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_1g_exit_step_pre(pre, cpu_id),
        mmap_1g_exit_step(pre, post, cpu_id),
    ensures mmap_1g_syscall_trace(steps.view(), cpu_id, va, range),
{ reveal(mmap_1g_trace_after_range); reveal(mmap_1g_syscall_trace); }
} // verus!

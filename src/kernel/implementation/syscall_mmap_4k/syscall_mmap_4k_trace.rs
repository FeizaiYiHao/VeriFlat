use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_spec::*;

verus! {
/// Write-locking the caller's context and recording the first page is the enter step on `pre`/`post`.
pub(super) proof fn mmap_4k_enter_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, range: VaRange4K)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let pagetable = process.pagetable->Some_0;
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.owning_proc == process_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& process.pagetable is Some
            &&& pagetable.lock_state is Unlocked
            &&& range.wf()
            &&& range.len > 0
            &&& user_va_range(pre, range)
            &&& thread.quota_4k >= 4 * range.len
            &&& forall|i: int| #![trigger pagetable.mapping_4k.dom().contains(range.view()[i])] 0 <= i < range.len ==> !pagetable.mapping_4k.dom().contains(range.view()[i])
            &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> {
                let idx = spec_va2index(range.view()[i]);
                &&& !pagetable.mapping_2m.dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
                &&& !pagetable.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            }
        },
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Mmap4k { range, mapped: 0, directory: Mmap4kDirectory::None }),
                ..pre.thread_map.spec_index(thread_ptr)
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
                ..pre.process_map.spec_index(process_ptr)
            }),
            ..pre
        }),
    ensures
        mmap_4k_enter_step_pre(pre, cpu_id, range),
        mmap_4k_enter_step(pre, post, cpu_id, range),
{ reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); }

/// Publishing the next recorded page under the mmap locks is the leaf step on `pre`/`post`.
pub(super) proof fn mmap_4k_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
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
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
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
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_4k_progress_after_leaf(thread.syscall_progress), ..thread
                }),
                process_map: pre.process_map.insert(process_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: process.pagetable->Some_0.mapping_4k.insert(va, entry), ..process.pagetable->Some_0 }), ..process
                }),
                ..pre
            })
        },
    ensures
        mmap_4k_leaf_step_pre(pre, cpu_id),
        mmap_4k_leaf_step(pre, post, cpu_id),
{ reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); }

/// Clearing the progress and releasing the mmap locks after the whole range is mapped is the exit step on `pre`/`post`.
pub(super) proof fn mmap_4k_exit_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
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
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Mmap4k
            &&& progress->Mmap4k_mapped == progress->Mmap4k_range.len
            &&& progress->Mmap4k_directory is None
        },
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map.spec_index(thread_ptr) }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
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

/// The enter step pushed onto an empty trace is the partial trace after entering.
pub(super) proof fn mmap_4k_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_4k_enter_step_pre(pre, cpu_id, range),
        mmap_4k_enter_step(pre, post, cpu_id, range),
    ensures
        mmap_4k_trace_after_enter(steps.view(), cpu_id, range),
{ reveal(mmap_4k_trace_after_enter); }

/// The range steps appended after the enter step give the partial trace after mapping the range.
pub(super) proof fn mmap_4k_trace_range_steps(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K)
    requires
        mmap_4k_trace_after_enter(before, cpu_id, range),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
    ensures
        mmap_4k_trace_after_range(steps.view(), cpu_id, range),
{ reveal(mmap_4k_trace_after_enter); reveal(mmap_4k_trace_after_range); }

/// The exit step pushed after the mapped partial trace completes the syscall trace.
pub(super) proof fn mmap_4k_trace_exit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize)
    requires
        mmap_4k_trace_after_range(before, cpu_id, mmap_4k_syscall_va_range(va, range)),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        mmap_4k_exit_step_pre(pre, cpu_id),
        mmap_4k_exit_step(pre, post, cpu_id),
    ensures
        mmap_4k_syscall_trace(steps.view(), cpu_id, va, range),
{ reveal(mmap_4k_trace_after_range); reveal(mmap_4k_syscall_trace); }
} // verus!

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::syscall_new_container_spec::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
verus! {
/// Acquiring the caller's context locks and recording the progress is the enter step on `pre`/`post`.
pub(super) proof fn new_container_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let container = pre.container_map.spec_index(container_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let transfer = pre.cpu_array[transfer_cpu as int];
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& container.lock_state is Unlocked
            &&& container.cpu_set_lock is Unlocked
            &&& !container.killed
            &&& container.depth < MAX_CONTAINER_TREE_DEPTH
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is Unlocked
            &&& range.wf()
            &&& 0 < range.len <= (usize::MAX - 9) / 3
            &&& user_va_range(pre, range)
            &&& process_quota <= funding <= usize::MAX - 9 - 3 * range.len
            &&& thread.quota_4k >= 9 + funding + 3 * range.len
            &&& thread.quota_2m >= 2
            &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> process.pagetable->Some_0.mapping_4k.dom().contains(range.view()[i])
            &&& index_valid(NUM_CPUS, transfer_cpu)
            &&& transfer.state is Off
            &&& transfer.owning_container == container_ptr
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, cpu_set_lock: LockStateU::WriteLocked, ..pre.container_map[container_ptr]
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::WriteLocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: pre.endpoint_map,
            ..pre
        }),
        post == (KernelU {
            thread_map: locked.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, child_container: None })),
                ..locked.thread_map[thread_ptr]
            }),
            ..locked
        }),
    ensures
        new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu),
        new_container_enter_step(pre, post, cpu_id, range, funding, process_quota, transfer_cpu, regs),
{
    reveal(new_container_enter_step_pre); reveal(new_container_enter_step);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked,
        syscall_progress: Some(SyscallProgress::NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, child_container: None })),
        ..pre.thread_map.spec_index(thread_ptr)
    }));
}

/// The caller holding its context locks with an unlocked Off transfer cpu satisfies the publish precondition.
pub(super) proof fn new_container_publish_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, record: NewContainerProgress,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let container = pre.container_map.spec_index(container_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let transfer = pre.cpu_array[record.transfer_cpu as int];
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::NewContainer(record))
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& container.lock_state is WriteLocked
            &&& container.cpu_set_lock is WriteLocked
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is WriteLocked
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& index_valid(NUM_CPUS, record.transfer_cpu)
            &&& transfer.lock_state is Unlocked
            &&& transfer.state is Off
            &&& transfer.owning_container == container_ptr
        },
    ensures
        new_container_publish_step_pre(pre, cpu_id),
{ reveal(new_container_publish_step_pre); }

/// Creating the child container with its root process from `pre` to `post` is the publish step.
pub(super) proof fn new_container_publish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr,
    root_ptr: RwLockProcessPtr, record: NewContainerProgress,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map.spec_index(thread_ptr).syscall_progress == Some(SyscallProgress::NewContainer(record)),
        pre.thread_map.spec_index(thread_ptr).owning_container == container_ptr,
        kernel_u_container_root_created(pre, post, container_ptr, child_ptr, root_ptr, thread_ptr, record.transfer_cpu, record.funding, record.process_quota,
            Some(SyscallProgress::Share4k {
                source_range: record.range, target_range: record.range, shared: 0,
                origin: Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child_ptr), ..record }),
            })),
        post.container_map[container_ptr].children.last() == child_ptr,
        post.container_map[child_ptr].root_process == root_ptr,
    ensures
        new_container_publish_step(pre, post, cpu_id),
{ reveal(new_container_publish_step); }

/// The caller holding every retained lock after the whole range is shared satisfies the finish precondition.
pub(super) proof fn new_container_finish_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr,
    root_ptr: RwLockProcessPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let progress = thread.syscall_progress->Some_0;
            let parent = pre.process_map.spec_index(process_ptr);
            let root = pre.process_map.spec_index(root_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Share4k
            &&& progress->Share4k_origin is NewContainer
            &&& progress->Share4k_origin->NewContainer_0.child_container == Some(child_ptr)
            &&& progress->Share4k_shared == progress->Share4k_source_range.len
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& pre.container_map.dom().contains(child_ptr)
            &&& pre.container_map.spec_index(child_ptr).lock_state is WriteLocked
            &&& pre.container_map.spec_index(child_ptr).root_process == root_ptr
            &&& pre.container_map.spec_index(child_ptr).parent == Some(container_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& parent.lock_state is WriteLocked
            &&& parent.pagetable is Some
            &&& parent.pagetable->Some_0.lock_state is WriteLocked
            &&& pre.process_map.dom().contains(root_ptr)
            &&& root.lock_state is WriteLocked
            &&& root.pagetable is Some
            &&& root.pagetable->Some_0.lock_state is WriteLocked
            &&& root.owning_container == child_ptr
        },
    ensures
        new_container_finish_step_pre(pre, cpu_id),
{ reveal(new_container_finish_step_pre); }

/// Creating the root process's first thread while releasing every retained lock is the finish step on `pre`/`post`.
pub(super) proof fn new_container_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    child_ptr: RwLockContainerPtr, root_ptr: RwLockProcessPtr, new_thread_ptr: RwLockThreadPtr, regs: Registers,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& cpu.current_thread == Some(thread_ptr)
            &&& thread.syscall_progress is Some
            &&& progress is Share4k
            &&& progress->Share4k_origin is NewContainer
            &&& progress->Share4k_origin->NewContainer_0.child_container == Some(child_ptr)
            &&& progress->Share4k_origin->NewContainer_0.regs == regs
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.container_map.spec_index(child_ptr).root_process == root_ptr
            &&& pre.process_map.spec_index(root_ptr).iommu_table is None
        },
        post.process_map.spec_index(root_ptr).owned_threads.last() == new_thread_ptr,
        kernel_u_new_thread_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..pre.container_map[container_ptr] })
                .insert(child_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..pre.container_map[child_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::Unlocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr].pagetable->Some_0 }), ..pre.process_map[process_ptr]
            }).insert(root_ptr, ProcessU {
                lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[root_ptr].pagetable->Some_0 }),
                iommu_table: None, ..pre.process_map[root_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: pre.endpoint_map,
            ..pre
        }, post, root_ptr, thread_ptr, child_ptr, new_thread_ptr, regs, None, None),
    ensures
        new_container_finish_step(pre, post, cpu_id),
{ reveal(new_container_finish_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(super) proof fn new_container_trace_enter_step(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize,
    transfer_cpu: CpuId, regs: Registers,
)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu),
        new_container_enter_step(pre, post, cpu_id, range, funding, process_quota, transfer_cpu, regs),
    ensures
        new_container_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
{ reveal(new_container_trace_after_enter); }

/// The publish step pushed after the partial trace that starts at `start` is the partial trace after publishing.
pub(super) proof fn new_container_trace_publish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize,
    transfer_cpu: CpuId, regs: Registers,
)
    requires
        0 <= start <= before.len(),
        new_container_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
        steps.view() == before.push(steps.view().last()),
        new_container_publish_step_pre(steps.view().last().old_u, cpu_id),
        new_container_publish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_container_trace_after_publish(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
{ reveal(new_container_trace_after_enter); reveal(new_container_trace_after_publish); }

/// The share steps pushed after the partial trace that starts at `start` give the partial trace after sharing.
pub(super) proof fn new_container_trace_share_steps(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize,
    transfer_cpu: CpuId, regs: Registers,
)
    requires
        0 <= start <= before.len(),
        new_container_trace_after_publish(before.subrange(start, before.len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
    ensures
        new_container_trace_after_share(steps.view(), start, pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
{ reveal(new_container_trace_after_publish); reveal(new_container_trace_after_share); }

/// The finish step pushed after the shared partial trace that starts at `start` completes the commit trace.
pub(super) proof fn new_container_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize,
    transfer_cpu: CpuId, regs: Registers,
)
    requires
        0 <= start <= before.len(),
        new_container_trace_after_share(before, start, pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
        steps.view() == before.push(steps.view().last()),
        new_container_finish_step_pre(steps.view().last().old_u, cpu_id),
        new_container_finish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_container_commit_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs),
{ reveal(new_container_trace_after_share); reveal(new_container_commit_trace); }

/// A rejected call records no step.
pub(super) proof fn new_container_trace_stutter(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
    ret: RetValueType,
)
    requires
        trace.len() == 0,
        !(ret is SuccessThreeUsize),
    ensures
        new_container_syscall_trace(trace, pre, pre, cpu_id, va, range, funding, process_quota, transfer_cpu, regs, ret),
{ reveal(new_container_syscall_trace); }

/// A complete commit trace ending in `post` is the successful syscall trace.
pub(super) proof fn new_container_syscall_trace_from_commit(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding: usize, process_quota: usize, transfer_cpu: CpuId,
    regs: Registers, ret: RetValueType,
)
    requires
        trace.len() > 0,
        new_container_commit_trace(trace, pre, cpu_id, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) },
            funding, process_quota, transfer_cpu, regs),
        trace.last().new_u == post,
        ret is SuccessThreeUsize,
    ensures
        new_container_syscall_trace(trace, pre, post, cpu_id, va, range, funding, process_quota, transfer_cpu, regs, ret),
{ reveal(new_container_syscall_trace); }
} // verus!

use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
/// The result of `syscall_new_container` from the state at entry, in the implementation's check order:
/// malformed arguments or funding, a killed parent container, a parent at the maximum tree depth, a
/// killed process or caller, too little caller 4K or 2M quota, a source range below the first user L4
/// index or with a page that has no present 4K leaf, and a transfer cpu that the parent container does
/// not own or that is not Off. `Success` stands for `SuccessThreeUsize`, whose fresh container, process,
/// and thread pointers the state does not determine.
pub open spec fn new_container_syscall_result(
    pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId,
) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    let parent = pre.container_map[thread.owning_container];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k;
    let transfer = pre.cpu_array[transfer_cpu_id as int];
    let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
    if range == 0 || range > usize::MAX / 4096 || range > (usize::MAX - 9) / 3 || !spec_va_4k_valid(va) || transfer_cpu_id >= NUM_CPUS
        || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) || process_quota_4k > funding_page_count
        || funding_page_count > usize::MAX - 9 - 3 * range {
        RetValueType::Error
    } else if parent.killed { RetValueType::ErrorContainerKilled }
    else if parent.depth >= MAX_CONTAINER_TREE_DEPTH { RetValueType::Error }
    else if pre.process_map[thread.owning_proc].killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if thread.quota_4k < 9 + funding_page_count + 3 * range || thread.quota_2m < 2 { RetValueType::ErrorNoQuota }
    else if !(user_va_range(pre, va_range) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(va_range.view()[j]) && mapping[va_range.view()[j]].present) {
        RetValueType::Error
    } else if transfer.owning_container != thread.owning_container { RetValueType::ErrorIpcCpuOwnerMismatch }
    else if !(transfer.state is Off) { RetValueType::ErrorIpcCpuNotOff }
    else { RetValueType::Success }
}

/// The cpu runs a live thread of a live process inside its live container, which is below the
/// maximum container depth; the thread has no syscall in progress; `range` is a nonempty well-formed user
/// range whose every page the process maps; `process_quota <= funding`, and the thread's quotas pay
/// for the child's pages, `funding`, and three directory pages per shared page; `transfer_cpu` is an
/// Off cpu of the container. The cpu, the container and its cpu set, the process and its page table,
/// and the thread are unlocked.
#[verifier::opaque]
pub open spec fn new_container_enter_step_pre(
    old_u: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let container = old_u.container_map[thread.owning_container];
    let process = old_u.process_map[thread.owning_proc];
    let pagetable = process.pagetable->Some_0;
    let transfer = old_u.cpu_array[transfer_cpu as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& container.lock_state is Unlocked
    &&& container.cpu_set_lock is Unlocked
    &&& !container.killed
    &&& container.depth < MAX_CONTAINER_TREE_DEPTH
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& range.wf()
    &&& 0 < range.len <= (usize::MAX - 9) / 3
    &&& user_va_range(old_u, range)
    &&& process_quota <= funding <= usize::MAX - 9 - 3 * range.len
    &&& thread.quota_4k >= 9 + funding + 3 * range.len
    &&& thread.quota_2m >= 2
    &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
    &&& index_valid(NUM_CPUS, transfer_cpu)
    &&& transfer.state is Off
    &&& transfer.owning_container == thread.owning_container
}

/// Entering write-locks the cpu, the container and its cpu set, the process and its page table, and the
/// thread, and records the call's arguments in the thread's progress.
#[verifier::opaque]
pub open spec fn new_container_enter_step(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map[thread_ptr];
    let process = old_u.process_map[thread.owning_proc];
    let progress = SyscallProgress::NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, child_container: None });
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..cpu }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU {
            lock_state: LockStateU::WriteLocked, cpu_set_lock: LockStateU::WriteLocked, ..old_u.container_map[thread.owning_container]
        }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::WriteLocked, pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.pagetable->Some_0 }), ..process
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        ..old_u
    })
}

/// Publication runs while the running thread records a container creation and holds the cpu, its
/// container and that container's cpu set, its process and that process's page table, and itself; the
/// recorded transfer cpu is an unlocked Off cpu of the container.
#[verifier::opaque]
pub open spec fn new_container_publish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let process = old_u.process_map[thread.owning_proc];
    let transfer_cpu = thread.syscall_progress->Some_0->NewContainer_0.transfer_cpu;
    let transfer = old_u.cpu_array[transfer_cpu as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is NewContainer
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
    &&& old_u.container_map[thread.owning_container].cpu_set_lock is WriteLocked
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& process.lock_state is WriteLocked
    &&& process.pagetable is Some
    &&& process.pagetable->Some_0.lock_state is WriteLocked
    &&& index_valid(NUM_CPUS, transfer_cpu)
    &&& transfer.lock_state is Unlocked
    &&& transfer.state is Off
    &&& transfer.owning_container == thread.owning_container
}

/// Publication creates the child container as the container's last child together with its root
/// process, moves the transfer cpu into it, pays the recorded funding, and starts sharing the recorded
/// range into the root process.
#[verifier::opaque]
pub open spec fn new_container_publish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map[thread_ptr];
    let progress = thread.syscall_progress->Some_0;
    let child = new_u.container_map[thread.owning_container].children.last();
    let range = progress->NewContainer_0.range;
    let origin = Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child), ..progress->NewContainer_0 });
    let sharing = SyscallProgress::Share4k { source_range: range, target_range: range, shared: 0, origin };
    kernel_u_container_root_created(old_u, new_u, thread.owning_container, child, new_u.container_map[child].root_process, thread_ptr,
        progress->NewContainer_0.transfer_cpu, progress->NewContainer_0.funding, progress->NewContainer_0.process_quota, Some(sharing))
}

/// Finishing runs after the whole recorded range has been shared into the root process of the recorded
/// child of the thread's container, while the running thread holds the cpu, its container and the child
/// container, its process and the root process with their page tables, and itself.
#[verifier::opaque]
pub open spec fn new_container_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let progress = thread.syscall_progress->Some_0;
    let child = progress->Share4k_origin->NewContainer_0.child_container->Some_0;
    let parent = old_u.process_map[thread.owning_proc];
    let root = old_u.process_map[old_u.container_map[child].root_process];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& progress is Share4k
    &&& progress->Share4k_origin is NewContainer
    &&& progress->Share4k_shared == progress->Share4k_source_range.len
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
    &&& old_u.container_map.dom().contains(child)
    &&& old_u.container_map[child].lock_state is WriteLocked
    &&& old_u.container_map[child].parent == Some(thread.owning_container)
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& parent.lock_state is WriteLocked
    &&& parent.pagetable is Some
    &&& parent.pagetable->Some_0.lock_state is WriteLocked
    &&& old_u.process_map.dom().contains(old_u.container_map[child].root_process)
    &&& root.lock_state is WriteLocked
    &&& root.pagetable is Some
    &&& root.pagetable->Some_0.lock_state is WriteLocked
    &&& root.owning_container == child
}

/// The last step creates the root process's first thread with the recorded registers, clears the
/// caller's progress, and releases every retained observable lock.
#[verifier::opaque]
pub open spec fn new_container_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map[thread_ptr];
    let origin = thread.syscall_progress->Some_0->Share4k_origin;
    let container = thread.owning_container;
    let child = origin->NewContainer_0.child_container->Some_0;
    let parent = thread.owning_proc;
    let root = old_u.container_map[child].root_process;
    kernel_u_new_thread_changed(KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..cpu }),
        container_map: old_u.container_map.insert(container, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[container] })
            .insert(child, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[child] }),
        process_map: old_u.process_map.insert(parent, ProcessU { lock_state: LockStateU::Unlocked,
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..old_u.process_map[parent].pagetable->Some_0 }), ..old_u.process_map[parent]
        }).insert(root, ProcessU { lock_state: LockStateU::Unlocked,
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..old_u.process_map[root].pagetable->Some_0 }), ..old_u.process_map[root]
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..thread }),
        ..old_u
    }, new_u, root, thread_ptr, child, new_u.process_map[root].owned_threads.last(), origin->NewContainer_0.regs, None, None)
}

/// The partial trace after entering: one enter step from `pre`.
#[verifier::opaque]
pub open spec fn new_container_trace_after_enter(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu)
    &&& new_container_enter_step(pre, trace[0].new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs)
}

/// The partial trace after publishing: the enter step from `pre` and the publish step.
#[verifier::opaque]
pub open spec fn new_container_trace_after_publish(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
) -> bool {
    &&& trace.len() == 2
    &&& trace[0].old_u == pre
    &&& new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu)
    &&& new_container_enter_step(pre, trace[0].new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs)
    &&& new_container_publish_step_pre(trace[1].old_u, cpu_id)
    &&& new_container_publish_step(trace[1].old_u, trace[1].new_u, cpu_id)
}

/// The steps from `start` after sharing: enter from `pre`, publish, and then only share steps.
#[verifier::opaque]
pub open spec fn new_container_trace_after_share(
    trace: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
) -> bool {
    &&& 0 <= start
    &&& start + range.len + 2 <= trace.len() <= start + 4 * range.len + 2
    &&& trace[start].old_u == pre
    &&& new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu)
    &&& new_container_enter_step(pre, trace[start].new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs)
    &&& new_container_publish_step_pre(trace[start + 1].old_u, cpu_id)
    &&& new_container_publish_step(trace[start + 1].old_u, trace[start + 1].new_u, cpu_id)
    &&& forall|j: int| #![trigger trace[j]] start + 2 <= j < trace.len() ==> share_4k_range_step(trace[j], cpu_id)
}

/// The steps of a successful call: enter, publish, the share steps, and finish.
#[verifier::opaque]
pub open spec fn new_container_commit_trace(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
) -> bool {
    &&& range.len + 3 <= trace.len() <= 4 * range.len + 3
    &&& trace[0].old_u == pre
    &&& new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu)
    &&& new_container_enter_step(pre, trace[0].new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs)
    &&& new_container_publish_step_pre(trace[1].old_u, cpu_id)
    &&& new_container_publish_step(trace[1].old_u, trace[1].new_u, cpu_id)
    &&& forall|j: int| #![trigger trace[j]] 2 <= j < trace.len() - 1 ==> share_4k_range_step(trace[j], cpu_id)
    &&& new_container_finish_step_pre(trace.last().old_u, cpu_id)
    &&& new_container_finish_step(trace.last().old_u, trace.last().new_u, cpu_id)
}

/// Complete trace of the call: the commit steps on success, a stutter otherwise.
#[verifier::opaque]
pub open spec fn new_container_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding: usize,
    process_quota: usize, transfer_cpu: CpuId, regs: Registers, result: RetValueType,
) -> bool {
    let range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
    if result is SuccessThreeUsize {
        &&& new_container_commit_trace(trace, pre, cpu_id, range, funding, process_quota, transfer_cpu, regs)
        &&& trace.last().new_u == post
    } else { trace.len() == 0 && post == pre }
}
}

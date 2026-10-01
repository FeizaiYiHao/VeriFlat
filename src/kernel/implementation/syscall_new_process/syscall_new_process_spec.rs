use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
/// The cpu runs a live thread of a live process; the thread has no syscall in progress; `range` is
/// a nonempty well-formed user range whose every page the process maps; the thread's container has a
/// free PCID; the thread's 4K quota pays for the new process's pages and three directory pages per
/// shared page; a present `endpoint_index` names a live descriptor. The cpu, the process and its
/// page table, the thread, and that endpoint are unlocked; the container is never locked.
#[verifier::opaque]
pub open spec fn new_process_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K, endpoint_index: Option<EndpointIdx>, with_iommu: bool) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let container = old_u.container_map[thread.owning_container];
    let process = old_u.process_map[thread.owning_proc];
    let pagetable = process.pagetable->Some_0;
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index->Some_0 as int]->Some_0;
    let base: usize = if with_iommu { 6 } else { 4 };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& !container.free_pcids.is_empty()
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& process.pagetable is Some
    &&& pagetable.lock_state is Unlocked
    &&& range.wf()
    &&& 0 < range.len <= (usize::MAX - base) / 3
    &&& user_va_range(old_u, range)
    &&& thread.quota_4k >= base + 3 * range.len
    &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
    &&& endpoint_index is Some ==> {
        &&& edp_idx_valid(endpoint_index->Some_0)
        &&& thread.endpoint_descriptors[endpoint_index->Some_0 as int] is Some
        &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
        &&& old_u.endpoint_map[endpoint_ptr].lock_state is Unlocked
    }
}

/// Entering write-locks the cpu, the process and its page table, the thread, and the endpoint at
/// `endpoint_index`, and records the call's arguments in the thread's progress.
#[verifier::opaque]
pub open spec fn new_process_enter_step(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map[thread_ptr];
    let process = old_u.process_map[thread.owning_proc];
    let progress = SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: None });
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..cpu }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::WriteLocked, pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.pagetable->Some_0 }), ..process
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..thread }),
        endpoint_map: match endpoint_index {
            Some(i) => old_u.endpoint_map.insert(thread.endpoint_descriptors[i as int]->Some_0, EndpointU {
                lock_state: LockStateU::WriteLocked, ..old_u.endpoint_map[thread.endpoint_descriptors[i as int]->Some_0]
            }),
            None => old_u.endpoint_map,
        },
        ..old_u
    })
}

/// Publication runs while the running thread records a process creation and holds the cpu, its
/// process and that process's page table, and itself.
#[verifier::opaque]
pub open spec fn new_process_publish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let process = old_u.process_map[thread.owning_proc];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& thread.syscall_progress->Some_0 is NewProcess
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& process.lock_state is WriteLocked
    &&& process.pagetable is Some
    &&& process.pagetable->Some_0.lock_state is WriteLocked
}

/// Publication creates the child as the process's last child with empty write-locked tables,
/// consumes one free PCID of the container and the thread's 4K quota for the child's pages,
/// releases the process, and starts sharing the recorded range into the child.
#[verifier::opaque]
pub open spec fn new_process_publish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map[thread_ptr];
    let parent = thread.owning_proc;
    let container = thread.owning_container;
    let progress = thread.syscall_progress->Some_0;
    let child = new_u.process_map[parent].children.last();
    let ancestors = old_u.process_map[parent].uppertree_seq.push(parent);
    let empty_table = PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() };
    let cost: usize = if progress->NewProcess_0.with_iommu { 5 } else { 3 };
    let range = progress->NewProcess_0.range;
    let origin = Share4kOrigin::NewProcess(NewProcessProgress { child: Some(child), ..progress->NewProcess_0 });
    let sharing = SyscallProgress::Share4k { source_range: range, target_range: range, shared: 0, origin };
    &&& !old_u.process_map.dom().contains(child)
    &&& thread.quota_4k >= cost
    &&& new_u.container_map[container].free_pcids.subset_of(old_u.container_map[container].free_pcids)
    &&& old_u.container_map[container].free_pcids.difference(new_u.container_map[container].free_pcids).len() == 1
    &&& new_u.process_map.dom() == old_u.process_map.dom().insert(child)
    &&& forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] old_u.process_map.dom().contains(p) ==> new_u.process_map[p] == (ProcessU {
        lock_state: if p == parent { LockStateU::Unlocked } else { old_u.process_map[p].lock_state },
        children: if p == parent { old_u.process_map[p].children.push(child) } else { old_u.process_map[p].children },
        subtree_set: if ancestors.contains(p) { old_u.process_map[p].subtree_set.insert(child) } else { old_u.process_map[p].subtree_set },
        ..old_u.process_map[p]
    })
    &&& new_u.process_map[child] == (ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false, pagetable: Some(empty_table),
            iommu_table: if progress->NewProcess_0.with_iommu { Some(empty_table) } else { None }, pcid: new_u.process_map[child].pcid,
            owned_pci_functions: Set::empty(), quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent), children: Seq::empty(),
            depth: (old_u.process_map[parent].depth + 1) as usize, uppertree_seq: ancestors, subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
        })
    &&& new_u == (KernelU {
        process_map: new_u.process_map,
        container_map: old_u.container_map.insert(container, ContainerU {
            owned_processes: old_u.container_map[container].owned_processes.insert(child), free_pcids: new_u.container_map[container].free_pcids,
            ..old_u.container_map[container]
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k - cost) as usize, syscall_progress: Some(sharing), ..thread }),
        ..old_u
    })
}

/// Finishing runs after the whole recorded range has been shared into the recorded child, while the
/// running thread holds the cpu, its process's page table, the child and its tables, itself, and the
/// recorded endpoint.
#[verifier::opaque]
pub open spec fn new_process_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let progress = thread.syscall_progress->Some_0;
    let origin = progress->Share4k_origin;
    let parent = old_u.process_map[thread.owning_proc];
    let child = old_u.process_map[origin->NewProcess_0.child->Some_0];
    let endpoint_ptr = thread.endpoint_descriptors[origin->NewProcess_0.endpoint_index->Some_0 as int]->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& progress is Share4k
    &&& origin is NewProcess
    &&& progress->Share4k_shared == progress->Share4k_source_range.len
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& parent.pagetable is Some
    &&& parent.pagetable->Some_0.lock_state is WriteLocked
    &&& old_u.process_map.dom().contains(origin->NewProcess_0.child->Some_0)
    &&& child.lock_state is WriteLocked
    &&& child.pagetable is Some
    &&& child.pagetable->Some_0.lock_state is WriteLocked
    &&& child.iommu_table is Some ==> child.iommu_table->Some_0.lock_state is WriteLocked
    &&& origin->NewProcess_0.endpoint_index is Some ==> old_u.endpoint_map.dom().contains(endpoint_ptr) && old_u.endpoint_map[endpoint_ptr].lock_state is WriteLocked
}

/// The last step creates the child's first thread with the recorded registers and endpoint,
/// clears the caller's progress, and releases every retained observable lock.
#[verifier::opaque]
pub open spec fn new_process_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map[thread_ptr];
    let origin = thread.syscall_progress->Some_0->Share4k_origin;
    let parent = thread.owning_proc;
    let child_ptr = origin->NewProcess_0.child->Some_0;
    let child = old_u.process_map[child_ptr];
    let endpoint = match origin->NewProcess_0.endpoint_index { Some(i) => thread.endpoint_descriptors[i as int], None => None };
    kernel_u_new_thread_changed(KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..cpu }),
        process_map: old_u.process_map.insert(parent, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..old_u.process_map[parent].pagetable->Some_0 }), ..old_u.process_map[parent]
        }).insert(child_ptr, ProcessU {
            lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..child.pagetable->Some_0 }),
            iommu_table: match child.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None }, ..child
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..thread }),
        endpoint_map: match endpoint {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map[e] }),
            None => old_u.endpoint_map,
        },
        ..old_u
    }, new_u, child_ptr, thread_ptr, thread.owning_container, new_u.process_map[child_ptr].owned_threads.last(), origin->NewProcess_0.regs, endpoint, None)
}

/// The partial trace after entering: one enter step from `pre`.
#[verifier::opaque]
pub open spec fn new_process_trace_after_enter(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& new_process_enter_step_pre(pre, cpu_id, range, endpoint_index, with_iommu)
    &&& new_process_enter_step(pre, trace[0].new_u, cpu_id, range, regs, endpoint_index, with_iommu)
}

/// The partial trace after publishing: the enter step from `pre` and the publish step.
#[verifier::opaque]
pub open spec fn new_process_trace_after_publish(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
) -> bool {
    &&& trace.len() == 2
    &&& trace[0].old_u == pre
    &&& new_process_enter_step_pre(pre, cpu_id, range, endpoint_index, with_iommu)
    &&& new_process_enter_step(pre, trace[0].new_u, cpu_id, range, regs, endpoint_index, with_iommu)
    &&& new_process_publish_step_pre(trace[1].old_u, cpu_id)
    &&& new_process_publish_step(trace[1].old_u, trace[1].new_u, cpu_id)
}

/// The steps from `start` after sharing: enter from `pre`, publish, and then only share steps.
#[verifier::opaque]
pub open spec fn new_process_trace_after_share(
    trace: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
) -> bool {
    &&& 0 <= start
    &&& start + range.len + 2 <= trace.len() <= start + 4 * range.len + 2
    &&& trace[start].old_u == pre
    &&& new_process_enter_step_pre(pre, cpu_id, range, endpoint_index, with_iommu)
    &&& new_process_enter_step(pre, trace[start].new_u, cpu_id, range, regs, endpoint_index, with_iommu)
    &&& new_process_publish_step_pre(trace[start + 1].old_u, cpu_id)
    &&& new_process_publish_step(trace[start + 1].old_u, trace[start + 1].new_u, cpu_id)
    &&& forall|j: int| #![trigger trace[j]] start + 2 <= j < trace.len() ==> share_4k_range_step(trace[j], cpu_id)
}

/// The steps of a successful call: enter, publish, the share steps, and finish.
#[verifier::opaque]
pub open spec fn new_process_commit_trace(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
) -> bool {
    &&& range.len as int + 3 <= trace.len() as int <= 4 * range.len as int + 3
    &&& trace[0].old_u == pre
    &&& new_process_enter_step_pre(pre, cpu_id, range, endpoint_index, with_iommu)
    &&& new_process_enter_step(pre, trace[0].new_u, cpu_id, range, regs, endpoint_index, with_iommu)
    &&& new_process_publish_step_pre(trace[1].old_u, cpu_id)
    &&& new_process_publish_step(trace[1].old_u, trace[1].new_u, cpu_id)
    &&& forall|i: int| #![trigger trace[i]] 2 <= i < trace.len() - 1 ==> share_4k_range_step(trace[i], cpu_id)
    &&& new_process_finish_step_pre(trace.last().old_u, cpu_id)
    &&& new_process_finish_step(trace.last().old_u, trace.last().new_u, cpu_id)
}

/// Complete trace of the call: the commit steps on success, a stutter otherwise.
#[verifier::opaque]
pub open spec fn new_process_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize,
    regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool, result: RetValueType,
) -> bool {
    let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
    if result is SuccessPairUsize || result is SuccessThreeUsize {
        &&& new_process_commit_trace(trace, pre, cpu_id, source_range, regs, endpoint_index, with_iommu)
        &&& trace.last().new_u == post
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
}

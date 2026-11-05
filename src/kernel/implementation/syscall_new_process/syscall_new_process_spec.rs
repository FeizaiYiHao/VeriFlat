use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
#[cfg(verus_keep_ghost)]
use crate::kernel::kernel_step_spec::kernel_u_new_thread_changed;

verus! {
/// The result of `syscall_new_process` and its endpoint and IOMMU variants from the state at entry, in
/// the implementation's check order: malformed arguments, a cpu no longer Running or marked by a killer, a killed process or caller, no free PCID in
/// the caller's container, an empty `ep_idx` descriptor, too little caller 4K quota, and a
/// range below the first user L4 index or with a page that has no present 4K leaf. `Success` stands for
/// the variant's success value, whose fresh process, IOMMU table, and thread pointers the state does
/// not determine.
pub open spec fn new_process_syscall_result(pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    let mapping = pre.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k;
    // The child's own 4K pages: its process, page-table object, L4 page, and first thread, plus the IOMMU table object and
    // its root page with an IOMMU table; every shared page may add three directory pages (L3, L2, L1) to the child's table.
    let base: usize = if with_iommu { 6 } else { 4 };
    let va_range = spec_va_range_4k(va, range);
    if range == 0 || range > usize::MAX / 4096 || range > (usize::MAX - base) / 3 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) {
        RetValueType::Error
    } else if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if pre.process_map[thread.owning_proc].killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if pre.container_map[thread.owning_container].free_pcids.is_empty() { RetValueType::ErrorNoPcid }
    else if ep_idx is Some && thread.endpoint_descriptors[ep_idx->Some_0 as int] is None { RetValueType::Error }
    else if thread.quota_4k < base + 3 * range { RetValueType::ErrorNoQuota }
    else if user_va_range(pre, va_range) && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> mapping.dom().contains(va_range.view()[j]) {
        RetValueType::Success
    } else { RetValueType::Error }
}

/// The cpu runs a live thread of a live process; the thread has no syscall in progress; `range` is
/// a nonempty well-formed user range whose every page the process maps; the thread's container has a
/// free PCID; the thread's 4K quota pays for the new process's pages and three directory pages per
/// shared page; a present `ep_idx` names a live descriptor. The cpu, the process, the thread,
/// and that endpoint are unlocked, the page table is not write-locked, and the container is never locked.
#[verifier::opaque]
pub open spec fn new_process_enter_step_pre(old_u: KernelU, cpu_id: CpuId, range: VaRange4K, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let container = old_u.container_map[thread.owning_container];
    let process = old_u.process_map[thread.owning_proc];
    let pagetable = process.pagetable->Some_0;
    let ep_ptr = thread.endpoint_descriptors[ep_idx->Some_0 as int]->Some_0;
    // The child's own pages, as in `new_process_syscall_result`; each shared page may cost three directory pages.
    let base: usize = if with_iommu { 6 } else { 4 };
    &&& cpu_runs_live_thread_at_entry(old_u, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& thread.lock_state is Unlocked
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& !container.free_pcids.is_empty()
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& process.pagetable is Some
    &&& !(pagetable.lock_state is WriteLocked)
    &&& range.wf()
    &&& 0 < range.len <= (usize::MAX - base) / 3
    &&& user_va_range(old_u, range)
    &&& thread.quota_4k >= base + 3 * range.len
    &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
    &&& ep_idx is Some ==> {
        &&& edp_idx_valid(ep_idx->Some_0)
        &&& thread.endpoint_descriptors[ep_idx->Some_0 as int] is Some
        &&& old_u.endpoint_map.dom().contains(ep_ptr)
        &&& old_u.endpoint_map[ep_ptr].lock_state is Unlocked
    }
}

/// Entering write-locks the cpu, the process, the thread, and the endpoint at `ep_idx`,
/// read-locks the process's page table and write-locks its existing windows over `range`, and records the call's arguments in
/// the thread's progress.
#[verifier::opaque]
pub open spec fn new_process_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thrd_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map[thrd_ptr];
    let process = old_u.process_map[thread.owning_proc];
    let progress = SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index: ep_idx, with_iommu, child: None });
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..cpu }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU {
            lock_state: LockStateU::WriteLocked { writer: cpu_id }, pagetable: Some(PageTableU {
                lock_state: process.pagetable->Some_0.lock_state.with_reader(cpu_id), pagetable_window_locks: pagetable_window_locks_after_locking_range(process.pagetable->Some_0.pagetable_window_locks, range, cpu_id),
                ..process.pagetable->Some_0
            }), ..process
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(progress), ..thread }),
        endpoint_map: match ep_idx {
            Some(i) => old_u.endpoint_map.insert(thread.endpoint_descriptors[i as int]->Some_0, EndpointU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..old_u.endpoint_map[thread.endpoint_descriptors[i as int]->Some_0] }),
            None => old_u.endpoint_map,
        },
        ..old_u
    })
}

/// Publication runs while the running thread records a process creation and holds the cpu, its
/// process, a read lock on that process's page table, and itself.
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
    &&& process.pagetable->Some_0.lock_state is ReadLocked
}

/// Publication creates the child as the process's last child with empty write-locked tables,
/// consumes one free PCID of the container and the thread's 4K quota for the child's pages,
/// releases the process, and starts sharing the recorded range into the child.
#[verifier::opaque]
pub open spec fn new_process_publish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map[thrd_ptr];
    let parent = thread.owning_proc;
    let container = thread.owning_container;
    let progress = thread.syscall_progress->Some_0;
    let child = new_u.process_map[parent].children.last();
    let cp = new_u.process_map[child].pcid;
    let ancestors = old_u.process_map[parent].uppertree_seq.push(parent);
    let empty_table = PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty(), pagetable_window_locks: Map::empty() };
    // The child's process, page-table object, and L4 page, plus the IOMMU table object and its root page with an IOMMU table.
    let cost: usize = if progress->NewProcess_0.with_iommu { 5 } else { 3 };
    let range = progress->NewProcess_0.range;
    let origin = Share4kOrigin::NewProcess(NewProcessProgress { child: Some(child), ..progress->NewProcess_0 });
    let sharing = SyscallProgress::Share4k { source_range: range, target_range: range, shared: 0, directory: Mmap4kDirectory::None, origin };
    &&& !old_u.process_map.dom().contains(child)
    &&& thread.quota_4k >= cost
    &&& old_u.container_map[container].free_pcids.contains(cp)
    &&& new_u.process_map.dom() == old_u.process_map.dom().insert(child)
    &&& forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] old_u.process_map.dom().contains(p) ==> new_u.process_map[p] == (ProcessU {
        lock_state: if p == parent { LockStateU::Unlocked } else { old_u.process_map[p].lock_state },
        children: if p == parent { old_u.process_map[p].children.push(child) } else { old_u.process_map[p].children },
        subtree_set: if ancestors.contains(p) { old_u.process_map[p].subtree_set.insert(child) } else { old_u.process_map[p].subtree_set },
        ..old_u.process_map[p]
    })
    &&& new_u.process_map[child] == (ProcessU {
        lock_state: LockStateU::WriteLocked { writer: cpu_id }, zombie: false, pagetable: Some(empty_table),
        iommu_table: if progress->NewProcess_0.with_iommu { Some(empty_table) } else { None }, pcid: cp, owning_container: container,
        owned_pci_functions: Set::empty(), quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent), children: Seq::empty(),
        depth: (old_u.process_map[parent].depth + 1) as usize, uppertree_seq: ancestors, subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
    })
    &&& new_u == (KernelU {
        process_map: new_u.process_map,
        container_map: old_u.container_map.insert(container, ContainerU {
            owned_processes: old_u.container_map[container].owned_processes.insert(child), free_pcids: old_u.container_map[container].free_pcids.remove(cp),
            ..old_u.container_map[container]
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { quota_4k: (thread.quota_4k - cost) as usize, syscall_progress: Some(sharing), ..thread }),
        ..old_u
    })
}

/// Finishing runs after the whole recorded range has been shared into the recorded child of the
/// thread's container, while the running thread holds the cpu, a read lock on its process's page table,
/// the child and its tables, itself, and the endpoint at the recorded valid descriptor index.
#[verifier::opaque]
pub open spec fn new_process_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    let progress = thread.syscall_progress->Some_0;
    let origin = progress->Share4k_origin;
    let parent = old_u.process_map[thread.owning_proc];
    let child = old_u.process_map[origin->NewProcess_0.child->Some_0];
    let ep_ptr = thread.endpoint_descriptors[origin->NewProcess_0.endpoint_index->Some_0 as int]->Some_0;
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
    &&& parent.pagetable->Some_0.lock_state.read_held_by(cpu_id)
    &&& old_u.process_map.dom().contains(origin->NewProcess_0.child->Some_0)
    &&& child.lock_state is WriteLocked
    &&& child.pagetable is Some
    &&& child.pagetable->Some_0.lock_state is WriteLocked
    &&& child.iommu_table is Some ==> child.iommu_table->Some_0.lock_state is WriteLocked
    &&& child.owning_container == thread.owning_container
    &&& origin->NewProcess_0.endpoint_index is Some ==> {
        &&& edp_idx_valid(origin->NewProcess_0.endpoint_index->Some_0)
        &&& old_u.endpoint_map.dom().contains(ep_ptr)
        &&& old_u.endpoint_map[ep_ptr].lock_state is WriteLocked
    }
}

/// The last step creates the child's first thread with the recorded registers and endpoint,
/// clears the caller's progress, and releases every retained observable lock, including the windows over the recorded range
/// of both page tables, and drops the cpu's read hold on the parent's page table (other readers may remain).
#[verifier::opaque]
pub open spec fn new_process_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thrd_ptr = cpu.current_thread->Some_0;
    let thread = old_u.thread_map[thrd_ptr];
    let origin = thread.syscall_progress->Some_0->Share4k_origin;
    let parent = thread.owning_proc;
    let child_ptr = origin->NewProcess_0.child->Some_0;
    let child = old_u.process_map[child_ptr];
    let endpoint = match origin->NewProcess_0.endpoint_index { Some(i) => thread.endpoint_descriptors[i as int], None => None };
    let range = origin->NewProcess_0.range;
    let parent_table = old_u.process_map[parent].pagetable->Some_0;
    let child_table = child.pagetable->Some_0;
    kernel_u_new_thread_changed(KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        process_map: old_u.process_map.insert(parent, ProcessU {
            pagetable: Some(PageTableU {
                lock_state: parent_table.lock_state.without_reader(cpu_id), pagetable_window_locks: pagetable_window_locks_after_unlocking_range(parent_table.pagetable_window_locks, range), ..parent_table
            }), ..old_u.process_map[parent]
        }).insert(child_ptr, ProcessU {
            lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU {
                lock_state: LockStateU::Unlocked, pagetable_window_locks: pagetable_window_locks_after_unlocking_range(child_table.pagetable_window_locks, range), ..child_table
            }),
            iommu_table: match child.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None }, ..child
        }),
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..thread }),
        endpoint_map: match endpoint {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map[e] }),
            None => old_u.endpoint_map,
        },
        ..old_u
    }, new_u, child_ptr, thrd_ptr, thread.owning_container, cpu_id, new_u.process_map[child_ptr].owned_threads.last(), origin->NewProcess_0.regs, endpoint, None)
}

/// The partial trace after entering: one enter step from `pre`.
#[verifier::opaque]
pub open spec fn new_process_trace_after_enter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& new_process_enter_step_pre(pre, cpu_id, range, ep_idx, with_iommu)
    &&& new_process_enter_step(pre, trace[0].new_u, cpu_id, range, regs, ep_idx, with_iommu)
}

/// The partial trace after publishing: the partial trace after entering, then the publish step.
#[verifier::opaque]
pub open spec fn new_process_trace_after_publish(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> bool {
    &&& trace.len() == 2
    &&& new_process_trace_after_enter(trace.take(1), pre, cpu_id, range, regs, ep_idx, with_iommu)
    &&& new_process_publish_step_pre(trace[1].old_u, cpu_id)
    &&& new_process_publish_step(trace[1].old_u, trace[1].new_u, cpu_id)
}

/// The steps from `start` after sharing: the partial trace after publishing at `start`, then only share steps.
#[verifier::opaque]
pub open spec fn new_process_trace_after_share(trace: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> bool {
    &&& 0 <= start
    // Enter, publish, and one to four share steps per page: the leaf and up to three new directories.
    &&& start + range.len + 2 <= trace.len() <= start + 4 * range.len + 2
    &&& new_process_trace_after_publish(trace.subrange(start, start + 2), pre, cpu_id, range, regs, ep_idx, with_iommu)
    &&& forall|j: int| #![trigger trace[j]] start + 2 <= j < trace.len() ==> share_4k_range_step(trace[j], cpu_id)
}

/// The steps of a successful call: the partial trace after sharing, then the finish step.
#[verifier::opaque]
pub open spec fn new_process_commit_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool) -> bool {
    // Enter, publish, one to four share steps per page, and finish.
    &&& range.len as int + 3 <= trace.len() as int <= 4 * range.len as int + 3
    &&& new_process_trace_after_share(trace.drop_last(), 0, pre, cpu_id, range, regs, ep_idx, with_iommu)
    &&& new_process_finish_step_pre(trace.last().old_u, cpu_id)
    &&& new_process_finish_step(trace.last().old_u, trace.last().new_u, cpu_id)
}

/// Complete trace of the call: the commit steps on success, a stutter otherwise.
#[verifier::opaque]
pub open spec fn new_process_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool, result: RetValueType) -> bool {
    if result is SuccessPairUsize || result is SuccessThreeUsize {
        &&& new_process_commit_trace(trace, pre, cpu_id, spec_va_range_4k(va, range), regs, ep_idx, with_iommu)
        &&& trace.last().new_u == post
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
}

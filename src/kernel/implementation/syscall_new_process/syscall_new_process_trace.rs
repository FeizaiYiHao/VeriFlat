use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::syscall_new_process_spec::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
verus! {
/// Acquiring the caller's context locks and recording the progress is the enter step on `pre`/`post`.
pub(super) proof fn new_process_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, endpoint_ptr: Option<RwLockEndpointPtr>, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>,
    with_iommu: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let base: usize = if with_iommu { 6 } else { 4 };
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
            &&& !pre.container_map.spec_index(container_ptr).free_pcids.is_empty()
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is Unlocked
            &&& range.wf()
            &&& 0 < range.len <= (usize::MAX - base) / 3
            &&& user_va_range(pre, range)
            &&& thread.quota_4k >= base + 3 * range.len
            &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> process.pagetable->Some_0.mapping_4k.dom().contains(range.view()[i])
            &&& (endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0) && endpoint_ptr is Some && thread.endpoint_descriptors[endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (endpoint_index is None ==> endpoint_ptr is None)
            &&& (endpoint_ptr is Some ==> pre.endpoint_map.dom().contains(endpoint_ptr->Some_0) && pre.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state is Unlocked)
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::WriteLocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: match endpoint_ptr {
                Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::WriteLocked, ..pre.endpoint_map.spec_index(e) }),
                None => pre.endpoint_map,
            },
            ..pre
        }),
        post == (KernelU {
            thread_map: locked.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: None })),
                ..locked.thread_map[thread_ptr]
            }),
            ..locked
        }),
    ensures
        new_process_enter_step_pre(pre, cpu_id, range, endpoint_index, with_iommu),
        new_process_enter_step(pre, post, cpu_id, range, regs, endpoint_index, with_iommu),
{
    reveal(new_process_enter_step_pre); reveal(new_process_enter_step);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked,
        syscall_progress: Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: None })),
        ..pre.thread_map.spec_index(thread_ptr)
    }));
}

/// Publishing the staged child while releasing the parent is the publish step on `pre`/`post`.
pub(super) proof fn new_process_publish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let parent = pre.process_map.spec_index(parent_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: None }))
            &&& thread.owning_proc == parent_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.process_map.dom().contains(parent_ptr)
            &&& parent.lock_state is WriteLocked
            &&& parent.pagetable is Some
            &&& parent.pagetable->Some_0.lock_state is WriteLocked
        },
        {
            let ancestors = pre.process_map[parent_ptr].uppertree_seq.push(parent_ptr);
            let empty_table = PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() };
            let cost: usize = if with_iommu { 5 } else { 3 };
            let origin = Share4kOrigin::NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: Some(child_ptr) });
            let sharing = SyscallProgress::Share4k { source_range: range, target_range: range, shared: 0, origin };
            &&& !pre.process_map.dom().contains(child_ptr)
            &&& pre.thread_map[thread_ptr].quota_4k >= cost
            &&& post.container_map[container_ptr].free_pcids.subset_of(pre.container_map[container_ptr].free_pcids)
            &&& pre.container_map[container_ptr].free_pcids.difference(post.container_map[container_ptr].free_pcids).len() == 1
            &&& post.process_map.dom() == pre.process_map.dom().insert(child_ptr)
            &&& forall|p: RwLockProcessPtr| #![trigger post.process_map[p]] pre.process_map.dom().contains(p) ==> post.process_map[p] == (ProcessU {
                lock_state: if p == parent_ptr { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
                children: if p == parent_ptr { pre.process_map[p].children.push(child_ptr) } else { pre.process_map[p].children },
                subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child_ptr) } else { pre.process_map[p].subtree_set },
                ..pre.process_map[p]
            })
            &&& post.process_map[child_ptr] == (ProcessU {
                lock_state: LockStateU::WriteLocked, zombie: false, pagetable: Some(empty_table),
                iommu_table: if with_iommu { Some(empty_table) } else { None }, pcid: post.process_map[child_ptr].pcid, owned_pci_functions: Set::empty(),
                quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent_ptr), children: Seq::empty(),
                depth: (pre.process_map[parent_ptr].depth + 1) as usize, uppertree_seq: ancestors,
                subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
            })
            &&& post == (KernelU {
                process_map: post.process_map,
                container_map: pre.container_map.insert(container_ptr, ContainerU {
                    owned_processes: pre.container_map[container_ptr].owned_processes.insert(child_ptr),
                    free_pcids: post.container_map[container_ptr].free_pcids, ..pre.container_map[container_ptr]
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    quota_4k: (pre.thread_map[thread_ptr].quota_4k - cost) as usize, syscall_progress: Some(sharing), ..pre.thread_map[thread_ptr]
                }),
                ..pre
            })
        },
    ensures
        new_process_publish_step_pre(pre, cpu_id),
        new_process_publish_step(pre, post, cpu_id),
{ reveal(new_process_publish_step_pre); reveal(new_process_publish_step); }

/// The caller holding every retained lock after the whole range is shared satisfies the finish precondition.
pub(super) proof fn new_process_finish_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_ptr: Option<RwLockEndpointPtr>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let parent = pre.process_map.spec_index(parent_ptr);
            let child = pre.process_map.spec_index(child_ptr);
            let progress = thread.syscall_progress->Some_0;
            let record = progress->Share4k_origin->NewProcess_0;
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Share4k
            &&& progress->Share4k_origin is NewProcess
            &&& progress->Share4k_shared == progress->Share4k_source_range.len
            &&& record.child == Some(child_ptr)
            &&& thread.owning_proc == parent_ptr
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& pre.process_map.dom().contains(parent_ptr)
            &&& parent.pagetable is Some
            &&& parent.pagetable->Some_0.lock_state is WriteLocked
            &&& pre.process_map.dom().contains(child_ptr)
            &&& child.lock_state is WriteLocked
            &&& child.pagetable is Some
            &&& child.pagetable->Some_0.lock_state is WriteLocked
            &&& (child.iommu_table is Some ==> child.iommu_table->Some_0.lock_state is WriteLocked)
            &&& (record.endpoint_index is Some ==> endpoint_ptr is Some && thread.endpoint_descriptors[record.endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (endpoint_ptr is Some ==> pre.endpoint_map.dom().contains(endpoint_ptr->Some_0) && pre.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state is WriteLocked)
        },
    ensures
        new_process_finish_step_pre(pre, cpu_id),
{ reveal(new_process_finish_step_pre); }

/// Creating the child's first thread while releasing every retained lock is the finish step on `pre`/`post`.
pub(super) proof fn new_process_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, endpoint_ptr: Option<RwLockEndpointPtr>, regs: Registers,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let progress = thread.syscall_progress->Some_0;
            let record = progress->Share4k_origin->NewProcess_0;
            &&& cpu.current_thread == Some(thread_ptr)
            &&& thread.syscall_progress is Some
            &&& progress is Share4k
            &&& progress->Share4k_origin is NewProcess
            &&& record.child == Some(child_ptr)
            &&& record.regs == regs
            &&& thread.owning_proc == parent_ptr
            &&& thread.owning_container == container_ptr
            &&& (record.endpoint_index is Some ==> thread.endpoint_descriptors[record.endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (record.endpoint_index is None ==> endpoint_ptr is None)
        },
        post.process_map.spec_index(child_ptr).owned_threads.last() == new_thread_ptr,
        kernel_u_new_thread_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(parent_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[parent_ptr].pagetable->Some_0 }), ..pre.process_map[parent_ptr]
            }).insert(child_ptr, ProcessU {
                lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[child_ptr].pagetable->Some_0 }),
                iommu_table: match pre.process_map[child_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
                ..pre.process_map[child_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: match endpoint_ptr {
                Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..pre.endpoint_map.spec_index(e) }),
                None => pre.endpoint_map,
            },
            ..pre
        }, post, child_ptr, thread_ptr, container_ptr, new_thread_ptr, regs, endpoint_ptr, None),
    ensures
        new_process_finish_step(pre, post, cpu_id),
{ reveal(new_process_finish_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(super) proof fn new_process_trace_enter_step(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers,
    endpoint_index: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        new_process_enter_step_pre(pre, cpu_id, range, endpoint_index, with_iommu),
        new_process_enter_step(pre, post, cpu_id, range, regs, endpoint_index, with_iommu),
    ensures
        new_process_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, range, regs, endpoint_index, with_iommu),
{ reveal(new_process_trace_after_enter); }

/// The publish step pushed after the partial trace that starts at `start` is the partial trace after publishing.
pub(super) proof fn new_process_trace_publish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers,
    endpoint_index: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        0 <= start <= before.len(),
        new_process_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, range, regs, endpoint_index, with_iommu),
        steps.view() == before.push(steps.view().last()),
        new_process_publish_step_pre(steps.view().last().old_u, cpu_id),
        new_process_publish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_process_trace_after_publish(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, regs, endpoint_index, with_iommu),
{ reveal(new_process_trace_after_enter); reveal(new_process_trace_after_publish); }

/// The share steps pushed after the partial trace that starts at `start` give the partial trace after sharing.
pub(super) proof fn new_process_trace_share_steps(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers,
    endpoint_index: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        0 <= start <= before.len(),
        new_process_trace_after_publish(before.subrange(start, before.len() as int), pre, cpu_id, range, regs, endpoint_index, with_iommu),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
    ensures
        new_process_trace_after_share(steps.view(), start, pre, cpu_id, range, regs, endpoint_index, with_iommu),
{ reveal(new_process_trace_after_publish); reveal(new_process_trace_after_share); }

/// The finish step pushed after the shared partial trace that starts at `start` completes the commit trace.
pub(super) proof fn new_process_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers,
    endpoint_index: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        0 <= start <= before.len(),
        new_process_trace_after_share(before, start, pre, cpu_id, range, regs, endpoint_index, with_iommu),
        steps.view() == before.push(steps.view().last()),
        new_process_finish_step_pre(steps.view().last().old_u, cpu_id),
        new_process_finish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_process_commit_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, regs, endpoint_index, with_iommu),
{ reveal(new_process_trace_after_share); reveal(new_process_commit_trace); }

/// A rejected call records no step.
pub(super) proof fn new_process_trace_stutter(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool, ret: RetValueType,
)
    requires
        trace.len() == 0,
        !(ret is SuccessPairUsize || ret is SuccessThreeUsize),
    ensures
        new_process_syscall_trace(trace, pre, pre, cpu_id, va, range, regs, endpoint_index, with_iommu, ret),
{ reveal(new_process_syscall_trace); }

/// A complete commit trace ending in `post` is the successful syscall trace.
pub(super) proof fn new_process_syscall_trace_from_commit(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, regs: Registers, endpoint_index: Option<EndpointIdx>,
    with_iommu: bool, ret: RetValueType,
)
    requires
        trace.len() > 0,
        new_process_commit_trace(trace, pre, cpu_id, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) },
            regs, endpoint_index, with_iommu),
        trace.last().new_u == post,
        ret is SuccessPairUsize || ret is SuccessThreeUsize,
    ensures
        new_process_syscall_trace(trace, pre, post, cpu_id, va, range, regs, endpoint_index, with_iommu, ret),
{ reveal(new_process_syscall_trace); }
} // verus!

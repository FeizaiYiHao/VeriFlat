use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;
use super::syscall_new_container_spec::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
verus! {
/// Acquiring the caller's context locks, the container under the owner `locked_k` records for it, and recording the
/// progress is the enter step on `pre`/`post`.
pub(super) proof fn new_container_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, locked_k: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, endpoint_ptr: Option<RwLockEndpointPtr>, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
    endpoint_index: Option<EndpointIdx>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        locked == kernel_k_to_kernel_u(*locked_k),
        locked_k.prc_mp.dom().contains(process_ptr),
        locked_k.ctn_mp.spec_index(container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(locked_k.prc_mp.spec_index(process_ptr).view_rodata().view().depth)),
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
            &&& !container.zombie
            &&& container.depth < MAX_CONTAINER_TREE_DEPTH
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& process.pagetable is Some
            &&& !(process.pagetable->Some_0.lock_state is WriteLocked)
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
            &&& (endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0) && endpoint_ptr is Some && thread.endpoint_descriptors[endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (endpoint_index is None ==> endpoint_ptr is None)
            &&& (endpoint_ptr is Some ==> pre.endpoint_map.dom().contains(endpoint_ptr->Some_0) && pre.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state is Unlocked)
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, lock_process_owner: locked_k.ctn_mp.spec_index(container_ptr).lock_process_owner_u(), cpu_set_lock: LockStateU::WriteLocked,
                ..pre.container_map[container_ptr]
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::WriteLocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: match endpoint_ptr { Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::WriteLocked, ..pre.endpoint_map.spec_index(e) }), None => pre.endpoint_map },
            ..pre
        }),
        post == (KernelU {
            thread_map: locked.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, endpoint_index, child_container: None })),
                ..locked.thread_map[thread_ptr]
            }),
            ..locked
        }),
    ensures
        new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu, endpoint_index),
        new_container_enter_step(pre, post, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
{
    kernel_process_projection_at(locked_k, process_ptr); reveal(new_container_enter_step_pre); reveal(new_container_enter_step);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked,
        syscall_progress: Some(SyscallProgress::NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, endpoint_index, child_container: None })),
        ..pre.thread_map.spec_index(thread_ptr)
    }));
}

/// The caller's write-held context, its recorded progress, and an Off transfer cpu of its container at `krnl` give the publish
/// step's precondition on its user view once the transfer cpu is unlocked, together with the objects that step binds.
pub(super) proof fn new_container_publish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    record: NewContainerProgress,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, record.transfer_cpu),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(process_ptr).view().pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewContainer(record)),
        krnl.cpu_arr.spec_index(record.transfer_cpu).view().view().view().state is Off,
        krnl.cpu_arr.spec_index(record.transfer_cpu).view().view().view().owning_container == container_ptr,
    ensures
        krnl.cpu_arr.spec_index(record.transfer_cpu).value.locking_thread() is None ==> new_container_publish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr).syscall_progress == Some(SyscallProgress::NewContainer(record)),
        kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr).owning_container == container_ptr,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, record.transfer_cpu); reveal(new_container_publish_step_pre);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), krnl.prc_mp.spec_index(process_ptr).view().pagetable); kernel_pagetable_mappings_projection_at(krnl, process_ptr);
}

/// Creating the child container with its root process from `pre` to `post` is the publish step.
pub(super) proof fn new_container_publish_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr, root_ptr: RwLockProcessPtr, record: NewContainerProgress)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map.spec_index(thread_ptr).syscall_progress == Some(SyscallProgress::NewContainer(record)),
        pre.thread_map.spec_index(thread_ptr).owning_container == container_ptr,
        kernel_u_container_root_created(pre, post, container_ptr, child_ptr, root_ptr, thread_ptr, record.transfer_cpu, record.funding, record.process_quota,
            Some(SyscallProgress::Share4k { source_range: record.range, target_range: record.range, shared: 0, origin: Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child_ptr), ..record }) })),
        post.container_map[container_ptr].children.last() == child_ptr,
        post.container_map[child_ptr].root_process == root_ptr,
    ensures
        new_container_publish_step(pre, post, cpu_id),
{ reveal(new_container_publish_step); }

/// The caller's write-held context, both containers and processes with their page tables, the optional endpoint, and the fully
/// shared progress at `krnl` give the finish step's precondition on its user view, together with the objects that step binds.
pub(super) proof fn new_container_finish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    child_ptr: RwLockContainerPtr, root_ptr: RwLockProcessPtr, endpoint_ptr: Option<RwLockEndpointPtr>,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), child_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), root_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(process_ptr).view().pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(root_ptr).view().pagetable, TypedLockMode::Write),
        endpoint_ptr matches Some(e) ==> krnl.ep_mp.dom().contains(e) && typed_lock_map_contains_mode(lctx.endpoint_lock_map(), e, TypedLockMode::Write),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.ctn_mp.dom().contains(child_ptr),
        krnl.prc_mp.dom().contains(root_ptr),
        !krnl.prc_mp.spec_index(root_ptr).view().zombie,
        krnl.prc_mp.spec_index(root_ptr).view().iommu_table is None,
        krnl.prc_mp.spec_index(root_ptr).view_rodata().view().owning_container == child_ptr,
        krnl.ctn_mp.spec_index(child_ptr).view().root_process == root_ptr,
        krnl.ctn_mp.spec_index(child_ptr).view_rodata().view().parent == Some(container_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { source_range, shared, origin, .. })
            && shared == source_range.len && origin is NewContainer && origin->NewContainer_0.child_container == Some(child_ptr)
            && (origin->NewContainer_0.endpoint_index matches Some(i) ==> edp_idx_valid(i) && endpoint_ptr is Some && krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(i) == endpoint_ptr),
    ensures
        new_container_finish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).container_map.spec_index(child_ptr).root_process == root_ptr,
        kernel_k_to_kernel_u(*krnl).process_map.spec_index(root_ptr).iommu_table is None,
{
    process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); reveal(share_4k_objects_k);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, endpoint_ptr);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, root_ptr, thread_ptr, None);
    kernel_share_4k_objects_projection(krnl, lctx, cpu_id);
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), krnl.prc_mp.spec_index(process_ptr).view().pagetable); kernel_pagetable_mappings_projection_at(krnl, process_ptr);
    reveal(new_container_finish_step_pre);
}

/// Creating the root process's first thread while releasing every retained lock is the finish step on `pre`/`post`.
pub(super) proof fn new_container_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    child_ptr: RwLockContainerPtr, root_ptr: RwLockProcessPtr, new_thread_ptr: RwLockThreadPtr, endpoint_ptr: Option<RwLockEndpointPtr>, regs: Registers,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let progress = thread.syscall_progress->Some_0;
            let record = progress->Share4k_origin->NewContainer_0;
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
            &&& (record.endpoint_index is Some ==> thread.endpoint_descriptors[record.endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (record.endpoint_index is None ==> endpoint_ptr is None)
        },
        post.process_map.spec_index(root_ptr).owned_threads.last() == new_thread_ptr,
        post.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked || post.process_map[process_ptr].pagetable->Some_0.lock_state is ReadLocked,
        kernel_u_new_thread_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(pre.cpu_array[cpu_id as int].state), ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..pre.container_map[container_ptr] })
                .insert(child_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..pre.container_map[child_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::Unlocked,
                pagetable: Some(PageTableU { lock_state: post.process_map[process_ptr].pagetable->Some_0.lock_state, ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }).insert(root_ptr, ProcessU {
                lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[root_ptr].pagetable->Some_0 }),
                iommu_table: None, ..pre.process_map[root_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: match endpoint_ptr { Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..pre.endpoint_map.spec_index(e) }), None => pre.endpoint_map },
            ..pre
        }, post, root_ptr, thread_ptr, child_ptr, cpu_id, new_thread_ptr, regs, endpoint_ptr, None),
    ensures
        new_container_finish_step(pre, post, cpu_id),
{ reveal(new_container_finish_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(super) proof fn new_container_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        new_container_enter_step_pre(pre, cpu_id, range, funding, process_quota, transfer_cpu, endpoint_index),
        new_container_enter_step(pre, post, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
    ensures
        new_container_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
{ reveal(new_container_trace_after_enter); }

/// The publish step pushed after the partial trace that starts at `start` is the partial trace after publishing.
pub(super) proof fn new_container_trace_publish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>)
    requires
        0 <= start <= before.len(),
        new_container_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
        steps.view() == before.push(steps.view().last()),
        new_container_publish_step_pre(steps.view().last().old_u, cpu_id),
        new_container_publish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_container_trace_after_publish(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
{ reveal(new_container_trace_after_enter); reveal(new_container_trace_after_publish); }

/// The share steps pushed after the partial trace that starts at `start` give the partial trace after sharing.
pub(super) proof fn new_container_trace_share_steps(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>)
    requires
        0 <= start <= before.len(),
        new_container_trace_after_publish(before.subrange(start, before.len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
    ensures
        new_container_trace_after_share(steps.view(), start, pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
{ reveal(new_container_trace_after_publish); reveal(new_container_trace_after_share); }

/// The finish step pushed after the shared partial trace that starts at `start` completes the commit trace.
pub(super) proof fn new_container_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>)
    requires
        0 <= start <= before.len(),
        new_container_trace_after_share(before, start, pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
        steps.view() == before.push(steps.view().last()),
        new_container_finish_step_pre(steps.view().last().old_u, cpu_id),
        new_container_finish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_container_commit_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
{ reveal(new_container_trace_after_share); reveal(new_container_commit_trace); }

/// The arguments and the caller's cpu, thread, container, process, page table, and transfer cpu at `krnl` decide the syscall result.
pub(super) proof fn new_container_result_from_k(
    krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId,
    endpoint_index: Option<EndpointIdx>, ret: RetValueType,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0);
            let t = thread.view();
            let container = krnl.ctn_mp.spec_index(t.owning_container);
            let process = krnl.prc_mp.spec_index(t.owning_proc);
            let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let transfer = krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view();
            let owner = container.lock_process_owner_u();
            let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            let bad_args = range == 0 || range > usize::MAX / 4096 || range > (usize::MAX - 9) / 3 || !spec_va_4k_valid(va) || transfer_cpu_id >= NUM_CPUS
                || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) || process_quota_4k > funding_page_count
                || funding_page_count > usize::MAX - 9 - 3 * range;
            let live = !bad_args && c.state is Running && !cpu.being_killed();
            let funded = live && !container.being_killed() && !container.view().zombie && container.view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH
                && !process.being_killed() && !thread.being_killed() && !(endpoint_index is Some && t.endpoint_descriptors.spec_index(endpoint_index->Some_0) is None)
                && t.quota_4k >= 9 + funding_page_count + 3 * range && t.quota_2m >= 2;
            &&& live ==> krnl.thr_mp.dom().contains(c.current_thread->Some_0) && krnl.ctn_mp.dom().contains(t.owning_container) && krnl.prc_mp.dom().contains(t.owning_proc)
            &&& funded ==> !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret == if bad_args { RetValueType::Error }
                else if !(c.state is Running) || cpu.being_killed() { RetValueType::CpuIdle }
                else if container.being_killed() { RetValueType::ErrorContainerKilled }
                else if owner is Some && owner->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth) { RetValueType::ErrorContainerLockOrderConflict }
                else if container.view().zombie { RetValueType::ErrorContainerZombie }
                else if container.view_rodata().view().depth >= MAX_CONTAINER_TREE_DEPTH { RetValueType::Error }
                else if process.being_killed() { RetValueType::ErrorProcessKilled }
                else if thread.being_killed() { RetValueType::ErrorThreadKilled }
                else if endpoint_index is Some && t.endpoint_descriptors.spec_index(endpoint_index->Some_0) is None { RetValueType::Error }
                else if t.quota_4k < 9 + funding_page_count + 3 * range || t.quota_2m < 2 { RetValueType::ErrorNoQuota }
                else if !(spec_v2l4index(va) >= table.kernel_l4_end() && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range
                    ==> table.mapping_4k().dom().contains(va_range.view()[j]) && table.mapping_4k()[va_range.view()[j]].present) { RetValueType::Error }
                else if transfer.owning_container != t.owning_container { RetValueType::ErrorIpcCpuOwnerMismatch }
                else if !(transfer.state is Off) { RetValueType::ErrorIpcCpuNotOff }
                else { RetValueType::Success }
        },
    ensures
        new_container_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) == ret,
{
    let thread_ptr = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    let t = krnl.thr_mp.spec_index(thread_ptr).view();
    let process = krnl.prc_mp.spec_index(t.owning_proc).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if index_valid(NUM_CPUS, transfer_cpu_id) { kernel_cpu_projection_at(krnl, transfer_cpu_id); }
    if krnl.ctn_mp.dom().contains(t.owning_container) { kernel_container_projection_at(krnl, t.owning_container); }
    if krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(t.owning_proc) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, t.owning_proc, thread_ptr, None); kernel_process_projection_at(krnl, t.owning_proc);
        if !process.zombie && krnl.pt_mp.dom().contains(process.pagetable) { kernel_l4_end_projection_at(krnl, process.pagetable); }
    }
}

/// A rejected call records no step.
pub(super) proof fn new_container_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is SuccessThreeUsize),
    ensures
        new_container_syscall_trace(trace, pre, pre, cpu_id, va, range, funding, process_quota, transfer_cpu, regs, endpoint_index, ret),
{ reveal(new_container_syscall_trace); }

/// A complete commit trace ending in `post` is the successful syscall trace.
pub(super) proof fn new_container_syscall_trace_from_commit(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>, ret: RetValueType)
    requires
        trace.len() > 0,
        new_container_commit_trace(trace, pre, cpu_id, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) },
            funding, process_quota, transfer_cpu, regs, endpoint_index),
        trace.last().new_u == post,
        ret is SuccessThreeUsize,
    ensures
        new_container_syscall_trace(trace, pre, post, cpu_id, va, range, funding, process_quota, transfer_cpu, regs, endpoint_index, ret),
{ reveal(new_container_syscall_trace); }

/// Publishing the staged container root from `staged` to `published`, where `staged` is `pre` with its transfer cpu write-locked
/// and `post` is `published` with `progress` recorded, is the root publication on the user views of `pre` and `post`.
pub(super) proof fn new_container_root_published_from_k(
    pre: &KernelK, staged: &KernelK, published: &KernelK, post: &KernelK, parent: RwLockContainerPtr, thread: RwLockThreadPtr, transfer_cpu: CpuId,
    container_page: PagePtr, pcid_allocator_page: PagePtr, pages: Seq<PagePtr>, funding: usize, funding_pages: Seq<PagePtr>, allocator_quota_4k: usize,
    process_quota_4k: usize, progress: Option<SyscallProgress>,
)
    requires
        pre.inv(),
        post.inv(),
        index_valid(NUM_CPUS, transfer_cpu),
        page_ptr_2m_valid(container_page),
        funding_pages.len() == funding,
        pre.cpu_arr.spec_index(transfer_cpu).value.view().view().owning_container == parent,
        publish_staged_container_root_eof_transition_framing(*staged, *published, parent, thread, container_page, pcid_allocator_page, pages[0], pages[1], pages[2],
            pages[3], pages[8], pages[4], pages[5], pages[6], pages[7], funding_pages, allocator_quota_4k, process_quota_4k),
        publish_staged_container_root_eof_preconditions(*staged, parent, thread, container_page, pcid_allocator_page, pages[0], pages[1], pages[2],
            pages[3], pages[8], pages[4], pages[5], pages[6], pages[7], funding_pages, allocator_quota_4k, process_quota_4k),
        *staged == (KernelK { pg_arr: staged.pg_arr, cpu_arr: staged.cpu_arr, ..*pre }),
        *post == (KernelK { pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*published }),
        kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, staged.cpu_arr),
        staged.cpu_arr.spec_index(transfer_cpu).value.view().view().state is Off,
        staged.cpu_arr.spec_index(transfer_cpu).value.locking_thread() is Write,
        forall|i: CpuId| #![trigger staged.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != transfer_cpu ==>
            staged.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
        post.thr_mp.unchanged_except(&published.thr_mp, thread),
        post.thr_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress, ..published.thr_mp.spec_index(thread).view() }),
        post.thr_mp.spec_index(thread).view().syscall_progress.view() == progress,
        post.thr_mp.spec_index(thread).locking_thread() == published.thr_mp.spec_index(thread).locking_thread(),
        post.thr_mp.spec_index(thread).being_killed() == published.thr_mp.spec_index(thread).being_killed(),
        post.ctn_mp.spec_index(container_page).locking_thread() is Write,
        post.pt_mp.spec_index(pages[5]).locking_thread() is Write,
        post.cpu_set_mp.spec_index(pages[8]).locking_thread() is Write,
    ensures
        kernel_u_container_root_published(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), parent, container_page, pages[4], thread, transfer_cpu, funding,
            process_quota_4k, new_container_moved_pages(container_page, pcid_allocator_page, pages[0], pages[1], pages[2], pages[3],
                pages[8], pages[4], pages[5], pages[6]).union(funding_pages.to_set()), pages[7], progress),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions); reveal(container_cpu_offline_flags_wf); reveal(kernel_cpu_nonlock_fields_unchanged);
    assert(cpu_offline_requests_of(post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_page))) == Seq::new(NUM_CPUS as nat, |i: int| false)) by {
        reveal(cpu_offline_requests_of);
        assert_seqs_equal!(cpu_offline_requests_of(post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_page))) == Seq::new(NUM_CPUS as nat, |i: int| false));
    };
    assert(scheduler_shards_of(post.sched_mp.spec_index(pages[3])) == Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty())) by {
        reveal(scheduler_shards_of);
        assert_seqs_equal!(scheduler_shards_of(post.sched_mp.spec_index(pages[3])) == Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()));
    };
    let moved = new_container_moved_pages(container_page, pcid_allocator_page, pages[0], pages[1], pages[2], pages[3], pages[8], pages[4], pages[5], pages[6])
        .union(funding_pages.to_set());
    assert(moved.contains(container_page) && moved.contains(pages[4]) && moved.contains(pages[8])) by {
        reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages); broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        page_2m_all_ptrs_contains_head(page_ptr2page_index(container_page));
    };
    kernel_container_root_published_implies_u_step(pre, post, parent, container_page, pages[4], thread, transfer_cpu, funding, process_quota_4k, moved, pages[7], pcid_allocator_page, progress);
}

pub(super) proof fn kernel_container_publication_composes(
    pre: KernelU, published: KernelU, post: KernelU, parent: RwLockContainerPtr, child: RwLockContainerPtr, process: RwLockProcessPtr,
    thread: RwLockThreadPtr, cpu: CpuId, funding: usize, process_quota: usize, moved: Set<PagePtr>, thread_page: PagePtr, progress: Option<SyscallProgress>,
)
    requires
        moved.len() == 2 * 512 + 8 + funding,
    ensures
        kernel_u_container_root_published(pre, published, parent, child, process, thread, cpu, funding, process_quota, moved, thread_page, progress) && kernel_u_cpu_and_page_owner_changed(published, post, cpu, parent, child, thread_page)
            ==> kernel_u_container_root_created(pre, post, parent, child, process, thread, cpu, funding, process_quota, progress) && post.container_map[parent].children.last() == child && post.container_map[child].root_process == process,
{
    if kernel_u_container_root_published(pre, published, parent, child, process, thread, cpu, funding, process_quota, moved, thread_page, progress)
        && kernel_u_cpu_and_page_owner_changed(published, post, cpu, parent, child, thread_page) {
        reveal(kernel_u_container_root_published); reveal(kernel_u_cpu_and_page_owner_changed); reveal(kernel_u_container_root_created);
        let moved_all = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
        assert_sets_equal!(post.container_map.dom(), pre.container_map.dom().insert(child));
        assert_sets_equal!(moved_all, moved.insert(thread_page));
        assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu as int, CpuU {
            lock_state: LockStateU::Unlocked, owning_container: child, ..pre.cpu_array[cpu as int]
        }));
    }
}
} // verus!

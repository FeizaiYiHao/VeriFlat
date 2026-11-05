use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
use super::syscall_new_process_spec::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
#[cfg(verus_keep_ghost)]
use crate::kernel::kernel_step_spec::kernel_u_new_thread_changed;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn new_process_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ep_idx: Option<EndpointIdx>, with_iommu: bool, ret: RetValueType, pcid: Pcid)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        {
            let base: usize = if with_iommu { 6 } else { 4 };
            let args_bad = range == 0 || range > usize::MAX / 4096 || range > (usize::MAX - base) / 3 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range);
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let prc_ptr = thread.view().owning_proc;
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let ctn_ptr = thread.view().owning_container;
            let allocator = krnl.pcid_allc_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator).view();
            let free = PcidAllocator::free_pcids(allocator.ref_counters.view());
            let has_pcid = allocator.pcid_is_free(pcid);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = spec_va_range_4k(va, range);
            let live = !args_bad && cpu.view().view().state is Running && !cpu.being_killed();
            let unkilled = live && !process.being_killed() && !thread.being_killed();
            let endpoint_missing = ep_idx is Some && thread.view().endpoint_descriptors.spec_index(ep_idx->Some_0) is None;
            let funded = unkilled && has_pcid && !endpoint_missing && thread.view().quota_4k >= base + 3 * range;
            let mapped = table.kernel_l4_end() <= spec_v2l4index(va) && forall|j: int| #![trigger va_range.view().spec_index(j)] 0 <= j < range
                ==> table.mapping_4k().dom().contains(va_range.view().spec_index(j)) && table.mapping_4k().spec_index(va_range.view().spec_index(j)).present;
            &&& live ==> cpu.view().view().current_thread is Some && krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(prc_ptr)
            &&& unkilled ==> krnl.ctn_mp.dom().contains(ctn_ptr)
            &&& funded ==> !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret is CpuIdle ==> !args_bad && !live
            &&& ret is ErrorProcessKilled ==> live && process.being_killed()
            &&& ret is ErrorThreadKilled ==> live && !process.being_killed() && thread.being_killed()
            &&& ret is ErrorNoPcid ==> unkilled && free.is_empty()
            &&& ret is Error ==> args_bad || (unkilled && has_pcid && endpoint_missing) || (funded && !mapped)
            &&& ret is ErrorNoQuota ==> unkilled && has_pcid && !endpoint_missing && thread.view().quota_4k < base + 3 * range
            &&& ret is Success ==> funded && mapped
            &&& ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoPcid || ret is Error || ret is ErrorNoQuota || ret is Success
        },
    ensures
        new_process_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range, ep_idx, with_iommu) == ret,
{
    let thrd_ptr = krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread->Some_0;
    let prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    let ctn_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    assert(krnl.pcid_allc_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator).view().pcid_is_free(pcid)
        ==> PcidAllocator::free_pcids(krnl.pcid_allc_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator).view().ref_counters.view()).contains(pcid));
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.thrd_mp.dom().contains(thrd_ptr) && krnl.prc_mp.dom().contains(prc_ptr) { kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); }
    if !krnl.prc_mp.spec_index(prc_ptr).view().zombie && krnl.prc_mp.dom().contains(prc_ptr) && krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(prc_ptr).view().pagetable) {
        kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(prc_ptr).view().pagetable); kernel_process_projection_at(krnl, prc_ptr);
    }
}

/// The entry state's K facts give the enter precondition on its user view.
pub(super) proof fn new_process_enter_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    ep_ptr: Option<RwLockEndpointPtr>, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid, range: VaRange4K, ep_idx: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let table = krnl.pt_mp.spec_index(pagetable_ptr);
            let base: usize = if with_iommu { 6 } else { 4 };
            &&& cpu.locking_thread() is None
            &&& cpu.view().view().state is Running
            &&& !cpu.being_killed()
            &&& cpu.view().view().current_thread == Some(thrd_ptr)
            &&& krnl.thrd_mp.dom().contains(thrd_ptr)
            &&& thread.locking_thread() is None
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.being_killed()
            &&& thread.view().owning_proc == prc_ptr
            &&& thread.view().owning_container == ctn_ptr
            &&& thread.view().quota_4k >= base + 3 * range.len
            &&& krnl.ctn_mp.dom().contains(ctn_ptr)
            &&& krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pcid_allc_ptr
            &&& krnl.pcid_allc_mp.spec_index(pcid_allc_ptr).view().pcid_is_free(pcid)
            &&& krnl.prc_mp.dom().contains(prc_ptr)
            &&& process.locking_thread() is None
            &&& !process.being_killed()
            &&& !process.view().zombie
            &&& process.view().pagetable == pagetable_ptr
            &&& krnl.pt_mp.dom().contains(pagetable_ptr)
            &&& !(table.locking_thread() is Write)
            &&& table.view().kernel_l4_end <= spec_v2l4index(range.start)
            &&& forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(range.view().spec_index(j))
                && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(range.view().spec_index(j)).present
            &&& range.wf()
            &&& 0 < range.len <= (usize::MAX - base) / 3
            &&& ep_idx is Some ==> edp_idx_valid(ep_idx->Some_0) && ep_ptr is Some && thread.view().endpoint_descriptors.spec_index(ep_idx->Some_0) == ep_ptr
            &&& ep_ptr is Some ==> krnl.ep_mp.dom().contains(ep_ptr->Some_0) && krnl.ep_mp.spec_index(ep_ptr->Some_0).locking_thread() is None
        },
    ensures
        new_process_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range, ep_idx, with_iommu),
{
    reveal(new_process_enter_step_pre); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
    assert(PcidAllocator::free_pcids(krnl.pcid_allc_mp.spec_index(pcid_allc_ptr).view().ref_counters.view()).contains(pcid));
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, ep_ptr); kernel_l4_end_projection_at(krnl, pagetable_ptr); kernel_process_projection_at(krnl, prc_ptr);
}

/// Acquiring the caller's context locks and the source windows over `range`, which turn `old_windows` into `windows`, and
/// recording the progress is the enter step on `pre`/`post`.
pub(super) proof fn new_process_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ep_ptr: Option<RwLockEndpointPtr>,
    range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool, old_windows: Map<WindowVa, LockStateU>, windows: Map<WindowVa, LockStateU>,
)
    requires
        {
            let thread = pre.thread_map.spec_index(thrd_ptr);
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& thread.owning_proc == prc_ptr
            &&& (ep_idx is Some ==> ep_ptr is Some && thread.endpoint_descriptors[ep_idx->Some_0 as int] == ep_ptr)
            &&& (ep_idx is None ==> ep_ptr is None)
        },
        pre.process_map[prc_ptr].pagetable->Some_0.pagetable_window_locks == old_windows,
        windows == pagetable_window_locks_after_locking_range(old_windows, range, cpu_id),
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(prc_ptr, ProcessU {
                lock_state: LockStateU::WriteLocked { writer: cpu_id },
                pagetable: Some(PageTableU { lock_state: pre.process_map[prc_ptr].pagetable->Some_0.lock_state.with_reader(cpu_id), pagetable_window_locks: windows, ..pre.process_map[prc_ptr].pagetable->Some_0 }),
                ..pre.process_map[prc_ptr]
            }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..pre.thread_map.spec_index(thrd_ptr) }),
            endpoint_map: match ep_ptr {
                Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..pre.endpoint_map.spec_index(e) }),
                None => pre.endpoint_map,
            },
            ..pre
        }),
        post == (KernelU {
            thread_map: locked.thread_map.insert(thrd_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index: ep_idx, with_iommu, child: None })),
                ..locked.thread_map[thrd_ptr]
            }),
            ..locked
        }),
    ensures
        new_process_enter_step(pre, post, cpu_id, range, regs, ep_idx, with_iommu),
{
    reveal(new_process_enter_step);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked { writer: cpu_id }, syscall_progress: Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index: ep_idx, with_iommu, child: None })),
        ..pre.thread_map.spec_index(thrd_ptr)
    }));
}

/// The write-held context's K facts give the publish precondition and the running thread's recorded call on the user view.
pub(super) proof fn new_process_publish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), parent_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(parent_ptr).view().pagetable, TypedLockMode::Read),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == parent_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index: ep_idx, with_iommu, child: None })),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        !krnl.prc_mp.spec_index(parent_ptr).view().zombie,
    ensures
        new_process_publish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
{
    reveal(new_process_publish_step_pre); kernel_write_held_context_projection(krnl, lctx, cpu_id, parent_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), krnl.prc_mp.spec_index(parent_ptr).view().pagetable); kernel_pagetable_mappings_projection_at(krnl, parent_ptr);
}

/// Publishing the staged child while releasing the parent is the publish step on `pre`/`post`.
pub(super) proof fn new_process_publish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool, pcid: Pcid,
)
    requires
        {
            let thread = pre.thread_map.spec_index(thrd_ptr);
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& thread.syscall_progress == Some(SyscallProgress::NewProcess(NewProcessProgress { range, regs, endpoint_index: ep_idx, with_iommu, child: None }))
            &&& thread.owning_proc == parent_ptr
            &&& thread.owning_container == ctn_ptr
        },
        {
            let ancestors = pre.process_map[parent_ptr].uppertree_seq.push(parent_ptr);
            let empty_table = PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty(), pagetable_window_locks: Map::empty() };
            let cost: usize = if with_iommu { 5 } else { 3 };
            let origin = Share4kOrigin::NewProcess(NewProcessProgress { range, regs, endpoint_index: ep_idx, with_iommu, child: Some(child_ptr) });
            let sharing = SyscallProgress::Share4k { source_range: range, target_range: range, shared: 0, directory: Mmap4kDirectory::None, origin };
            &&& pre.process_map.dom().contains(parent_ptr)
            &&& !pre.process_map.dom().contains(child_ptr)
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& pre.container_map.dom().contains(ctn_ptr)
            &&& pre.thread_map[thrd_ptr].quota_4k >= cost
            &&& pre.container_map[ctn_ptr].free_pcids.contains(pcid)
            &&& post.container_map[ctn_ptr].free_pcids == pre.container_map[ctn_ptr].free_pcids.remove(pcid)
            &&& post.process_map.dom() == pre.process_map.dom().insert(child_ptr)
            &&& forall|p: RwLockProcessPtr| #![trigger post.process_map[p]] pre.process_map.dom().contains(p) ==> post.process_map[p] == (ProcessU {
                lock_state: if p == parent_ptr { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
                children: if p == parent_ptr { pre.process_map[p].children.push(child_ptr) } else { pre.process_map[p].children },
                subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child_ptr) } else { pre.process_map[p].subtree_set },
                ..pre.process_map[p]
            })
            &&& post.process_map[child_ptr] == (ProcessU {
                lock_state: LockStateU::WriteLocked { writer: cpu_id }, zombie: false, pagetable: Some(empty_table),
                iommu_table: if with_iommu { Some(empty_table) } else { None }, pcid, owning_container: ctn_ptr, owned_pci_functions: Set::empty(),
                quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent_ptr), children: Seq::empty(),
                depth: (pre.process_map[parent_ptr].depth + 1) as usize, uppertree_seq: ancestors,
                subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
            })
            &&& post == (KernelU {
                process_map: post.process_map,
                container_map: pre.container_map.insert(ctn_ptr, ContainerU {
                    owned_processes: pre.container_map[ctn_ptr].owned_processes.insert(child_ptr),
                    free_pcids: post.container_map[ctn_ptr].free_pcids, ..pre.container_map[ctn_ptr]
                }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                    quota_4k: (pre.thread_map[thrd_ptr].quota_4k - cost) as usize, syscall_progress: Some(sharing), ..pre.thread_map[thrd_ptr]
                }),
                ..pre
            })
        },
    ensures
        new_process_publish_step(pre, post, cpu_id),
{ reveal(new_process_publish_step); }

/// The write-held context's K facts after the whole range is shared give the finish precondition and the running
/// thread's recorded child, registers, and endpoint on the user view.
pub(super) proof fn new_process_finish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, ep_ptr: Option<RwLockEndpointPtr>, ep_idx: EndpointIdx, regs: Registers, with_iommu: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        lctx.cpu_id() == cpu_id,
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), child_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(parent_ptr).view().pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(child_ptr).view().pagetable, TypedLockMode::Write),
        krnl.prc_mp.spec_index(child_ptr).view().iommu_table matches Some(t) ==> typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == parent_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { source_range, shared, origin, .. })
            && shared == source_range.len && origin == Share4kOrigin::NewProcess(NewProcessProgress {
                range: source_range, regs, endpoint_index: if ep_ptr is Some { Some(ep_idx) } else { None }, with_iommu, child: Some(child_ptr),
            }),
        ep_ptr is Some ==> {
            &&& edp_idx_valid(ep_idx)
            &&& krnl.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.spec_index(ep_idx) == ep_ptr
            &&& krnl.ep_mp.dom().contains(ep_ptr->Some_0)
            &&& typed_lock_map_contains_mode(lctx.endpoint_lock_map(), ep_ptr->Some_0, TypedLockMode::Write)
        },
        krnl.ctn_mp.dom().contains(ctn_ptr),
        krnl.prc_mp.dom().contains(parent_ptr),
        !krnl.prc_mp.spec_index(parent_ptr).view().zombie,
        krnl.prc_mp.dom().contains(child_ptr),
        !krnl.prc_mp.spec_index(child_ptr).view().zombie,
        krnl.prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == ctn_ptr,
    ensures
        new_process_finish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
{
    reveal(new_process_finish_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, child_ptr, thrd_ptr, ep_ptr); kernel_cpu_thread_projection_at(krnl, cpu_id, child_ptr, thrd_ptr, None);
    kernel_process_projection_at(krnl, child_ptr);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), krnl.prc_mp.spec_index(parent_ptr).view().pagetable); kernel_pagetable_mappings_projection_at(krnl, parent_ptr);
}

/// Creating the child's first thread while releasing every retained lock and the cpu's read hold on the parent's page table,
/// which turns the window maps `old_source_windows` and `old_child_windows` into `source_windows` and `child_windows`, is the
/// finish step on `pre`/`post`.
pub(super) proof fn new_process_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, new_thrd_ptr: RwLockThreadPtr, ep_ptr: Option<RwLockEndpointPtr>, regs: Registers,
    old_source_windows: Map<WindowVa, LockStateU>, source_windows: Map<WindowVa, LockStateU>, old_child_windows: Map<WindowVa, LockStateU>,
    child_windows: Map<WindowVa, LockStateU>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thrd_ptr);
            let progress = thread.syscall_progress->Some_0;
            let record = progress->Share4k_origin->NewProcess_0;
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& thread.syscall_progress is Some
            &&& progress is Share4k
            &&& progress->Share4k_origin is NewProcess
            &&& record.child == Some(child_ptr)
            &&& record.regs == regs
            &&& thread.owning_proc == parent_ptr
            &&& thread.owning_container == ctn_ptr
            &&& (record.endpoint_index is Some ==> thread.endpoint_descriptors[record.endpoint_index->Some_0 as int] == ep_ptr)
            &&& (record.endpoint_index is None ==> ep_ptr is None)
        },
        post.process_map.spec_index(child_ptr).owned_threads.last() == new_thrd_ptr,
        post.process_map[parent_ptr].pagetable->Some_0.lock_state == pre.process_map[parent_ptr].pagetable->Some_0.lock_state.without_reader(cpu_id),
        pre.process_map[parent_ptr].pagetable->Some_0.pagetable_window_locks == old_source_windows,
        pre.process_map[child_ptr].pagetable->Some_0.pagetable_window_locks == old_child_windows,
        source_windows == pagetable_window_locks_after_unlocking_range(old_source_windows, pre.thread_map[thrd_ptr].syscall_progress->Some_0->Share4k_origin->NewProcess_0.range),
        child_windows == pagetable_window_locks_after_unlocking_range(old_child_windows, pre.thread_map[thrd_ptr].syscall_progress->Some_0->Share4k_origin->NewProcess_0.range),
        kernel_u_new_thread_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(pre.cpu_array[cpu_id as int].state), ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(parent_ptr, ProcessU {
                pagetable: Some(PageTableU {
                    lock_state: post.process_map[parent_ptr].pagetable->Some_0.lock_state, pagetable_window_locks: source_windows, ..pre.process_map[parent_ptr].pagetable->Some_0
                }), ..pre.process_map[parent_ptr]
            }).insert(child_ptr, ProcessU {
                lock_state: LockStateU::Unlocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, pagetable_window_locks: child_windows, ..pre.process_map[child_ptr].pagetable->Some_0 }),
                iommu_table: match pre.process_map[child_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
                ..pre.process_map[child_ptr]
            }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thrd_ptr) }),
            endpoint_map: match ep_ptr {
                Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..pre.endpoint_map.spec_index(e) }),
                None => pre.endpoint_map,
            },
            ..pre
        }, post, child_ptr, thrd_ptr, ctn_ptr, cpu_id, new_thrd_ptr, regs, ep_ptr, None),
    ensures
        new_process_finish_step(pre, post, cpu_id),
{ reveal(new_process_finish_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(super) proof fn new_process_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        new_process_enter_step_pre(pre, cpu_id, range, ep_idx, with_iommu),
        new_process_enter_step(pre, post, cpu_id, range, regs, ep_idx, with_iommu),
    ensures
        new_process_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, range, regs, ep_idx, with_iommu),
{ reveal(new_process_trace_after_enter); }

/// The publish step pushed after the partial trace that starts at `start` is the partial trace after publishing.
pub(super) proof fn new_process_trace_publish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool)
    requires
        0 <= start <= before.len(),
        new_process_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, range, regs, ep_idx, with_iommu),
        steps.view() == before.push(steps.view().last()),
        new_process_publish_step_pre(steps.view().last().old_u, cpu_id),
        new_process_publish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_process_trace_after_publish(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, regs, ep_idx, with_iommu),
{
    reveal(new_process_trace_after_enter); reveal(new_process_trace_after_publish);
    assert_seqs_equal!(steps.view().subrange(start, steps.view().len() as int).take(1), before.subrange(start, before.len() as int));
}

/// The share steps pushed after the partial trace that starts at `start` give the partial trace after sharing.
pub(super) proof fn new_process_trace_share_steps(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool)
    requires
        0 <= start <= before.len(),
        new_process_trace_after_publish(before.subrange(start, before.len() as int), pre, cpu_id, range, regs, ep_idx, with_iommu),
        before.len() + range.len <= steps.view().len() <= before.len() + 4 * range.len,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
    ensures
        new_process_trace_after_share(steps.view(), start, pre, cpu_id, range, regs, ep_idx, with_iommu),
{
    reveal(new_process_trace_after_publish); reveal(new_process_trace_after_share);
    assert_seqs_equal!(steps.view().subrange(start, start + 2), before.subrange(start, before.len() as int));
}

/// The finish step pushed after the shared partial trace that starts at `start` completes the commit trace.
pub(super) proof fn new_process_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool)
    requires
        0 <= start <= before.len(),
        new_process_trace_after_share(before, start, pre, cpu_id, range, regs, ep_idx, with_iommu),
        steps.view() == before.push(steps.view().last()),
        new_process_finish_step_pre(steps.view().last().old_u, cpu_id),
        new_process_finish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        new_process_commit_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, range, regs, ep_idx, with_iommu),
{
    reveal(new_process_trace_after_share); reveal(new_process_commit_trace);
    assert_seqs_equal!(steps.view().subrange(start, steps.view().len() as int).drop_last(), before.subrange(start, before.len() as int));
    assert_seqs_equal!(before.subrange(start, before.len() as int).subrange(0, 2), before.subrange(start, start + 2));
}

/// A rejected call records no step.
pub(super) proof fn new_process_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, va: VAddr, range: usize, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is SuccessPairUsize || ret is SuccessThreeUsize),
    ensures
        new_process_syscall_trace(trace, pre, pre, cpu_id, va, range, regs, ep_idx, with_iommu, ret),
{ reveal(new_process_syscall_trace); }

/// A complete commit trace ending in `post` is the successful syscall trace.
pub(super) proof fn new_process_syscall_trace_from_commit(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize, regs: Registers, ep_idx: Option<EndpointIdx>, with_iommu: bool, ret: RetValueType)
    requires
        trace.len() > 0,
        new_process_commit_trace(trace, pre, cpu_id, spec_va_range_4k(va, range), regs, ep_idx, with_iommu),
        trace.last().new_u == post,
        ret is SuccessPairUsize || ret is SuccessThreeUsize,
    ensures
        new_process_syscall_trace(trace, pre, post, cpu_id, va, range, regs, ep_idx, with_iommu, ret),
{ reveal(new_process_syscall_trace); }
} // verus!

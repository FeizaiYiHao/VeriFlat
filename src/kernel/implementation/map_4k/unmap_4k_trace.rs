use vstd::prelude::*;
use crate::*;
use super::unmap_4k_spec::*;

verus! {
/// The caller write-holding its cpu and thread and holding the pagetable of the thread's present process in either mode, while
/// the range is not fully cleared and its next page has a present 4K leaf, satisfies the leaf precondition and projects its K
/// anchors.
pub proof fn unmap_4k_leaf_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, range: VaRange4K, unmapped: usize,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.pt_mp.dom().contains(pagetable),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        unmapped < range.len,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view()[unmapped as int]),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k()[range.view()[unmapped as int]].present,
    ensures
        unmap_4k_leaf_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
{
    reveal(unmap_4k_leaf_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr); kernel_process_projection_at(krnl, prc_ptr);
}

/// Clearing the next page `va` of the range under the unmap locks and advancing the progress is the leaf step on `pre`/`post`.
pub proof fn unmap_4k_leaf_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, va: VAddr, range: VaRange4K, unmapped: usize, progress: Option<SyscallProgress>,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].owning_proc == prc_ptr,
        pre.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        progress == Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }),
        range.view()[unmapped as int] == va,
        post == (KernelU {
            process_map: pre.process_map.insert(prc_ptr, ProcessU {
                pagetable: Some(PageTableU { mapping_4k: pre.process_map[prc_ptr].pagetable->Some_0.mapping_4k.remove(va), ..pre.process_map[prc_ptr].pagetable->Some_0 }),
                ..pre.process_map[prc_ptr]
            }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: progress, ..pre.thread_map[thrd_ptr] }),
            ..pre
        }),
    ensures unmap_4k_leaf_step(pre, post, cpu_id),
{ reveal(unmap_4k_leaf_step); }

/// The caller write-holding its cpu and thread and holding the pagetable of the thread's present process in either mode after
/// clearing the whole range and before recording the flush, while the thread's container exists, satisfies the flush
/// precondition and projects its K anchors.
pub proof fn unmap_4k_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    pcid: Pcid, range: VaRange4K,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
    ensures
        unmap_4k_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == pcid,
{
    reveal(unmap_4k_flush_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// While the caller write-holds its cpu, its held non-dangling thread keeps its `entry` object, and its page table, held in
/// either mode, keeps its `entry` payload up to the table stale-CPU record (and, while write-held, its lock owner and
/// mappings), the caller's thread, process, and container `ctn_ptr` project in `snap_u`, which `krnl` extends by a
/// TLB update and a read hold on the cpu set of that container, as each TLB-flush step of the range requires; a process or
/// container that `held` write-locks keeps its lock.
pub proof fn unmap_4k_tlb_flush_step_pre_from_k(
    krnl: &KernelK, entry: &KernelK, lctx: &LocalContext, held: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, snap_u: KernelU,
    ctn_ptr: RwLockContainerPtr,
)
    requires
        ctn_ptr == entry.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        snap_u.container_map.dom().contains(ctn_ptr),
        kernel_k_to_kernel_u(*krnl) == (KernelU {
            cpu_tlb: krnl.cpu_tlb.view(),
            container_map: snap_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..snap_u.container_map[ctn_ptr] }),
            ..snap_u
        }),
        krnl.inv(),
        entry.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_maps_unchanged(held, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        entry.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(entry.thrd_mp.spec_index(thrd_ptr)),
        entry.prc_mp.dom().contains(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc),
        entry.prc_mp.spec_index(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc).view().pagetable == pagetable,
        entry.pt_mp.dom().contains(pagetable),
        !entry.prc_mp.spec_index(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc).view().zombie,
        held.pagetable_lock_map().dom().contains(pagetable),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        held_threads_unchanged(entry.thrd_mp, krnl.thrd_mp, held),
        held_processes_unchanged(entry.prc_mp, krnl.prc_mp, held),
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus, ..entry.pt_mp.spec_index(pagetable).view() }),
        typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& krnl.pt_mp.spec_index(pagetable).locking_thread() == entry.pt_mp.spec_index(pagetable).locking_thread()
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_4k()
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_2m()
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_1g()
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).lower.pagetable_window_locks
        },
    ensures
        ({
            let u = snap_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let prc_ptr = entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
            &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& u.thread_map.dom().contains(thrd_ptr)
            &&& u.thread_map[thrd_ptr] == entry_u.thread_map[thrd_ptr]
            &&& u.process_map.dom().contains(prc_ptr)
            &&& typed_lock_map_contains_mode(held.process_lock_map(), prc_ptr, TypedLockMode::Write) ==> u.process_map[prc_ptr].lock_state == entry_u.process_map[prc_ptr].lock_state
            &&& u.process_map[prc_ptr].pagetable is Some
            &&& !(u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> u.process_map[prc_ptr].pagetable == entry_u.process_map[prc_ptr].pagetable
            &&& u.process_map[prc_ptr].pcid == entry_u.process_map[prc_ptr].pcid
            &&& u.container_map.dom().contains(ctn_ptr)
            &&& typed_lock_map_contains_mode(held.container_lock_map(), ctn_ptr, TypedLockMode::Write) ==> u.container_map[ctn_ptr].lock_state is WriteLocked
            &&& u.kernel_l4_end == entry_u.kernel_l4_end
        }),
{
    let prc_ptr = entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    process_thread_wf_thread_at(entry.prc_mp, entry.thrd_mp, thrd_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
    process_pagetable_wf_process_at(entry.prc_mp, entry.pt_mp, prc_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    kernel_thread_projection_at(krnl, thrd_ptr); kernel_thread_projection_at(entry, thrd_ptr);
    kernel_process_projection_at(krnl, prc_ptr); kernel_process_projection_at(entry, prc_ptr);
    kernel_l4_end_projection_at(krnl, pagetable); kernel_l4_end_projection_at(entry, pagetable);
    if typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        assert(pagetable_map_user_view(krnl.pt_mp, krnl.pt_lower.view()).spec_index(pagetable) =~~= pagetable_map_user_view(entry.pt_mp, entry.pt_lower.view()).spec_index(pagetable));
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// Recording the flush in the progress and releasing the read hold on the cpu set of the thread's container, which no
/// writer holds afterwards, is the flushed step on `pre`/`post`.
pub proof fn unmap_4k_flushed_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, range: VaRange4K, unmapped: usize, progress: Option<SyscallProgress>,
    cpu_set_lock: LockStateU,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        pre.thread_map[thrd_ptr].owning_container == ctn_ptr,
        progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: true }),
        pre.thread_map.dom().contains(thrd_ptr),
        !(cpu_set_lock is WriteLocked),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: progress, ..pre.thread_map[thrd_ptr] }),
            container_map: pre.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock, ..pre.container_map[ctn_ptr] }),
            ..pre
        }),
    ensures
        unmap_4k_flushed_step(pre, post, cpu_id),
{ reveal(unmap_4k_flushed_step); }

/// A leaf step pushed after range steps that start at `start` is a range step.
pub proof fn unmap_4k_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_leaf_step_pre(pre, cpu_id),
        unmap_4k_leaf_step(pre, post, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); }

/// TLB flushes of the caller's PCID, recorded after range steps that start at `start` while the caller's held
/// objects keep their projection at `entry`, leave only range steps.
pub proof fn unmap_4k_range_steps_from_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
    ctn_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        unmap_4k_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        entry.thread_map[thrd_ptr].owning_proc == prc_ptr,
        entry.thread_map[thrd_ptr].owning_container == ctn_ptr,
        entry.process_map[prc_ptr].pcid == pcid,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[prc_ptr].pcid == entry.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); }

/// The flushed step pushed after range steps that start at `start` is a range step.
pub proof fn unmap_4k_range_steps_from_flushed(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_flush_step_pre(pre, cpu_id),
        unmap_4k_flushed_step(pre, post, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); }

/// Quota refunds to the caller's container chain after range steps that start at `start` leave only range steps.
pub proof fn unmap_4k_range_steps_from_refund(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, progress: Option<SyscallProgress>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        progress is Some,
        progress->Some_0 is Unmap4k,
        progress->Some_0->Unmap4k_unmapped == progress->Some_0->Unmap4k_range.len,
        progress->Some_0->Unmap4k_flushed,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, ctn_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thrd_ptr].owning_container == ctn_ptr
            &&& old_u.thread_map[thrd_ptr].owning_proc == prc_ptr
            &&& old_u.thread_map[thrd_ptr].syscall_progress == progress
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); reveal(unmap_4k_refund_step_pre); }

/// Clearing `va`, the `unmapped`-th page of the range, from `pre` to `post` under the unmap locks and recording it after
/// range steps that start at `start` leaves only range steps.
pub proof fn unmap_4k_leaf_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, range: VaRange4K, unmapped: usize, va: VAddr,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        unmapped < range.len,
        range.view()[unmapped as int] == va,
        pre.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().insert(va, MapEntry { present: false, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va] }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(pre, post, pagetable, va, thrd_ptr);
    unmap_4k_leaf_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, pagetable, range, unmapped);
    unmap_4k_leaf_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, prc_ptr, thrd_ptr, va, range, unmapped, post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view());
    unmap_4k_range_steps_from_leaf(steps, before, start, kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id);
}

/// TLB flushes of the caller's PCID recorded from `entry` after range steps that start at `start`, while the caller
/// write-holds its cpu and thread and holds the pagetable of the thread's present process with the whole range cleared and
/// the thread's container exists, leave only range steps.
pub proof fn unmap_4k_tlb_flush_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange4K,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        typed_lock_maps_aligned(entry, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        entry.prc_mp.dom().contains(prc_ptr),
        entry.ctn_mp.dom().contains(ctn_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry_u.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[prc_ptr].pcid == entry_u.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    unmap_4k_flush_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, range);
    unmap_4k_range_steps_from_tlb_flush(steps, before, start, kernel_k_to_kernel_u(*entry), cpu_id, thrd_ptr, prc_ptr, ctn_ptr, pcid);
}

/// Recording the flush in the progress from `pre` to `post` after range steps that start at `start`, where `pre` extends
/// the step's start `snap` by page-table ghost state and by this thread's released read hold on the cpu set of its
/// container, while the caller write-holds its cpu and thread and holds the pagetable of the thread's present process with
/// the whole range cleared, leaves only range steps.
pub proof fn unmap_4k_flushed_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, snap: &KernelK, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange4K,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*snap), new_u: kernel_k_to_kernel_u(*post) }),
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
        *pre == (KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, cpu_set_mp: pre.cpu_set_mp, ..*snap }),
        pre.pt_mp.dom() == snap.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(pt)] snap.pt_mp.dom().contains(pt) ==> {
            &&& pre.pt_mp.spec_index(pt).locking_thread() == snap.pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).lower.pagetable_window_locks
        },
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.cpu_set_mp.unchanged_except(&snap.cpu_set_mp, pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
        pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed()
            == snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
        !(pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).locking_thread() is Write),
        *post == (KernelK { thrd_mp: post.thrd_mp, ..*pre }),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: true }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    let ghost_tables = KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*snap };
    let cpu_set_lock = pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u();
    reveal(kernel_cpu_nonlock_fields_unchanged); kernel_u_domains_projection(snap);
    kernel_cpu_tlb_updated_implies_u_step(snap, &ghost_tables);
    kernel_cpu_set_lock_mode_changed_implies_u_step(&ghost_tables, pre, ctn_ptr);
    kernel_thread_syscall_progress_changed_implies_u_step(pre, post, thrd_ptr);
    unmap_4k_flush_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, range);
    assert(unmap_4k_flush_step_pre(kernel_k_to_kernel_u(*snap), cpu_id)) by { reveal(unmap_4k_flush_step_pre); };
    unmap_4k_flushed_step_from_u(kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id, thrd_ptr, ctn_ptr, range, range.len, post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), cpu_set_lock);
    unmap_4k_range_steps_from_flushed(steps, before, start, kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id);
}
} // verus!

use vstd::prelude::*;
use crate::*;
use super::unmap_4k_spec::*;

verus! {
/// The caller write-holding its cpu, thread, process, and container and holding its pagetable in either mode while the range
/// is not fully cleared satisfies the leaf trace precondition and projects its K anchors.
pub proof fn unmap_4k_leaf_trace_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, range: VaRange4K, unmapped: usize,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(lctx.container_lock_map(), krnl.thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        unmapped < range.len,
    ensures
        unmap_4k_leaf_trace_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
{
    reveal(unmap_4k_leaf_trace_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, process_ptr);
}

/// Clearing a still-mapped page of the range under the unmap locks is the leaf step on `pre`/`post`.
pub proof fn unmap_4k_leaf_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr, range: VaRange4K, unmapped: usize, progress: Option<SyscallProgress>,
)
    requires
        unmap_4k_leaf_trace_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].owning_proc == process_ptr,
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        progress == Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }),
        range.view().contains(va),
        pre.process_map.dom().contains(process_ptr),
        pre.process_map[process_ptr].pagetable is Some,
        pre.process_map[process_ptr].pagetable->Some_0.mapping_4k.dom().contains(va),
        pre.thread_map.dom().contains(thread_ptr),
        post == (KernelU {
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { mapping_4k: pre.process_map[process_ptr].pagetable->Some_0.mapping_4k.remove(va), ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: progress, ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures
        unmap_4k_leaf_step_pre(pre, cpu_id, va),
        unmap_4k_leaf_step(pre, post, cpu_id, va),
{ reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); }

/// The caller write-holding its cpu, thread, process, and container and holding its pagetable in either mode after clearing
/// the whole range and before recording the flush satisfies the flush precondition and projects its K anchors.
pub proof fn unmap_4k_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    pcid: Pcid, range: VaRange4K,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
    ensures
        unmap_4k_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_container == container_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
        kernel_k_to_kernel_u(*krnl).process_map[process_ptr].pcid == pcid,
{
    reveal(unmap_4k_flush_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, process_ptr);
}

/// While the caller write-holds its cpu, its held thread, process, and container keep their `entry` objects, and its page
/// table, held in either mode, keeps its `entry` payload (and, while write-held, its lock owner and mappings), the caller's
/// held objects project as each TLB-flush step of the range requires.
pub proof fn unmap_4k_tlb_flush_step_pre_from_k(krnl: &KernelK, entry: &KernelK, lctx: &LocalContext, held: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot)
    requires
        krnl.inv(),
        entry.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_maps_unchanged(held, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.process_lock_map(), entry.thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.container_lock_map(), entry.thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        entry.thr_mp.dom().contains(thread_ptr),
        entry.prc_mp.dom().contains(entry.thr_mp.spec_index(thread_ptr).view().owning_proc),
        entry.prc_mp.spec_index(entry.thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        entry.pt_mp.dom().contains(pagetable),
        !entry.prc_mp.spec_index(entry.thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        held.pagetable_lock_map().dom().contains(pagetable),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        held_threads_unchanged(entry.thr_mp, krnl.thr_mp, held),
        held_processes_unchanged(entry.prc_mp, krnl.prc_mp, held),
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view() == entry.pt_mp.spec_index(pagetable).view(),
        typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& krnl.pt_mp.spec_index(pagetable).locking_thread() == entry.pt_mp.spec_index(pagetable).locking_thread()
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == pagetable_c(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_4k()
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == pagetable_c(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_2m()
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g() == pagetable_c(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_1g()
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.pagetable_window_locks == pagetable_c(entry.pt_mp, entry.pt_lower.view(), pagetable).lower.pagetable_window_locks
        },
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let entry_u = kernel_k_to_kernel_u(*entry);
            let process_ptr = entry.thr_mp.spec_index(thread_ptr).view().owning_proc;
            let container_ptr = entry.thr_mp.spec_index(thread_ptr).view().owning_container;
            &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& u.thread_map.dom().contains(thread_ptr)
            &&& u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
            &&& u.process_map.dom().contains(process_ptr)
            &&& u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
            &&& u.process_map[process_ptr].pagetable is Some
            &&& !(u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> u.process_map[process_ptr].pagetable == entry_u.process_map[process_ptr].pagetable
            &&& u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
            &&& u.container_map.dom().contains(container_ptr)
            &&& u.container_map[container_ptr].lock_state is WriteLocked
            &&& u.kernel_l4_end == entry_u.kernel_l4_end
        }),
{
    let process_ptr = entry.thr_mp.spec_index(thread_ptr).view().owning_proc;
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    kernel_thread_projection_at(krnl, thread_ptr); kernel_thread_projection_at(entry, thread_ptr);
    kernel_process_projection_at(krnl, process_ptr); kernel_process_projection_at(entry, process_ptr);
    kernel_l4_end_projection_at(krnl, pagetable); kernel_l4_end_projection_at(entry, pagetable);
    if typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        assert(pagetable_map_user_view(krnl.pt_mp, krnl.pt_lower.view()).spec_index(pagetable) =~~= pagetable_map_user_view(entry.pt_mp, entry.pt_lower.view()).spec_index(pagetable));
    } else {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    kernel_pagetable_mappings_projection_at(krnl, process_ptr);
}

/// Recording the flush in the progress is the flushed step on `pre`/`post`.
pub proof fn unmap_4k_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, range: VaRange4K, unmapped: usize, progress: Option<SyscallProgress>)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        progress == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: true }),
        pre.thread_map.dom().contains(thread_ptr),
        post == (KernelU { thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: progress, ..pre.thread_map[thread_ptr] }), ..pre }),
    ensures
        unmap_4k_flushed_step(pre, post, cpu_id),
{ reveal(unmap_4k_flushed_step); }

/// A leaf step that clears `va`, pushed after range steps that start at `start`, is a range step: without
/// `va` it removes exactly one key of the range.
pub proof fn unmap_4k_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_leaf_step_pre(pre, cpu_id, va),
        unmap_4k_leaf_step(pre, post, cpu_id, va),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    reveal(unmap_4k_range_step); reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); reveal(unmap_4k_leaf_trace_step);
    let thread = pre.thread_map.spec_index(pre.cpu_array[cpu_id as int].current_thread->Some_0);
    let mapping = pre.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k;
    let kept = mapping.remove(va).dom();
    assert(mapping.remove(va) =~= mapping.restrict(kept));
    assert(mapping.dom().difference(kept) =~= set![va]);
    assert(thread.syscall_progress->Some_0->Unmap4k_range.view().to_set().contains(va));
}

/// TLB flushes of the caller's PCID, recorded after range steps that start at `start` while the caller's held
/// objects keep their projection at `entry`, leave only range steps.
pub proof fn unmap_4k_range_steps_from_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        unmap_4k_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        entry.thread_map[thread_ptr].owning_proc == process_ptr,
        entry.thread_map[thread_ptr].owning_container == container_ptr,
        entry.process_map[process_ptr].pcid == pcid,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[process_ptr].pcid == entry.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); reveal(unmap_4k_flush_step_pre); }

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
pub proof fn unmap_4k_range_steps_from_refund(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, progress: Option<SyscallProgress>)
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
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, container_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == container_ptr
            &&& old_u.thread_map[thread_ptr].owning_proc == process_ptr
            &&& old_u.thread_map[thread_ptr].syscall_progress == progress
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state is WriteLocked
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); reveal(unmap_4k_refund_step_pre); }

/// Clearing `va`, the `unmapped`-th page of the range, from `pre` to `post` under the unmap locks and recording it after
/// range steps that start at `start` leaves only range steps.
pub proof fn unmap_4k_leaf_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, range: VaRange4K, unmapped: usize, va: VAddr,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(lctx.container_lock_map(), pre.thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped, flushed: false }),
        unmapped < range.len,
        range.view().contains(va),
        pre.pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thr_mp: post.thr_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va].present,
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().insert(va, MapEntry { present: false, ..pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va] }),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(pre, post, pagetable, va, thread_ptr);
    unmap_4k_leaf_trace_step_pre_from_k(pre, lctx, cpu_id, process_ptr, thread_ptr, pagetable, range, unmapped);
    unmap_4k_leaf_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, process_ptr, thread_ptr, va, range, unmapped, post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view());
    unmap_4k_range_steps_from_leaf(steps, before, start, kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, va);
}

/// TLB flushes of the caller's PCID recorded from `entry` after range steps that start at `start`, while the caller
/// write-holds its cpu, thread, process, and container and holds its pagetable with the whole range cleared, leave only
/// range steps.
pub proof fn unmap_4k_tlb_flush_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange4K,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        typed_lock_maps_aligned(entry, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        !entry.prc_mp.spec_index(process_ptr).view().zombie,
        entry.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        entry.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        entry.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        entry.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    unmap_4k_flush_step_pre_from_k(entry, lctx, cpu_id, process_ptr, thread_ptr, container_ptr, pagetable, pcid, range);
    unmap_4k_range_steps_from_tlb_flush(steps, before, start, kernel_k_to_kernel_u(*entry), cpu_id, thread_ptr, process_ptr, container_ptr, pcid);
}

/// Recording the flush in the progress from `pre` to `post` after range steps that start at `start`, while the caller
/// write-holds its cpu, thread, process, and container and holds its pagetable with the whole range cleared, leaves only
/// range steps.
pub proof fn unmap_4k_flushed_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange4K,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        lctx.pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: false }),
        *post == (KernelK { thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range, unmapped: range.len, flushed: true }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    kernel_thread_syscall_progress_changed_implies_u_step(pre, post, thread_ptr);
    unmap_4k_flush_step_pre_from_k(pre, lctx, cpu_id, process_ptr, thread_ptr, container_ptr, pagetable, pcid, range);
    unmap_4k_flushed_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, thread_ptr, range, range.len, post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view());
    unmap_4k_range_steps_from_flushed(steps, before, start, kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id);
}
} // verus!

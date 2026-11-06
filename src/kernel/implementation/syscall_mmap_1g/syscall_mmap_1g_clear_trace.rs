use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_spec::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::unmap_4k_spec::unmap_4k_tlb_flush_step;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::unmap_4k_spec::unmap_4k_tlb_flush_step;

verus! {
/// The caller write-holding its cpu, its thread, and the pagetable of the thread's present process with progress before the first page of `range`, while the thread's container exists, satisfies the hide precondition before the flush is recorded, the flush precondition after a hide, and
/// the reclaim precondition after the flush is recorded, and projects its K anchors.
pub(super) proof fn mmap_1g_clear_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    range: VaRange1G, hidden: bool, flushed: bool,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden, flushed }),
    ensures
        !flushed ==> mmap_1g_hide_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        hidden && !flushed ==> mmap_1g_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        flushed ==> mmap_1g_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden, flushed }),
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid,
{
    reveal(mmap_1g_hide_step_pre); reveal(mmap_1g_flush_step_pre); reveal(mmap_1g_reclaim_step_pre);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_u_domains_projection(krnl);
    krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
}

/// Hiding the L3 entry of page `i` of `range` from `pre` to `post`, which drops the windows `removed` under that page's 1G slot and marks the progress hidden, after range steps that start at `start`, leaves only range steps.
pub(super) proof fn mmap_1g_hide_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, range: VaRange1G, i: int, removed: Set<WindowVa>, hidden: bool,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_1g_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }),
        pre.inv(),
        post.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.ctn_mp.dom().contains(ctn_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden, flushed: false }),
        range.wf(),
        0 <= i < range.len,
        forall|w: WindowVa| #![trigger removed.contains(w)] removed.contains(w) ==> spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), 0, 0)) == range.view()[i],
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.remove_keys(removed),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: false }),
    ensures forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
{
    kernel_pagetable_l3_hidden_and_progress_changed_implies_u_step(pre, post, pagetable, removed, thrd_ptr);
    mmap_1g_clear_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range, hidden, false);
    assert(mmap_1g_range_step(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }, cpu_id)) by {
        reveal(mmap_1g_range_step); reveal(mmap_1g_hide_step);
    };
}

/// TLB flushes of the caller's PCID recorded from `entry` after range steps that start at `start`, while the caller write-holds its cpu, its thread, and the pagetable of the thread's present process with a hidden L3 entry before the flush is recorded and the thread's container exists,
/// leave only range steps.
pub(super) proof fn mmap_1g_tlb_flush_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, pcid: Pcid, range: VaRange1G,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_1g_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        typed_lock_maps_aligned(entry, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        entry.prc_mp.dom().contains(prc_ptr),
        entry.ctn_mp.dom().contains(ctn_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: false }),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*entry);
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(cpu_id), ..old_u.container_map[ctn_ptr] }), ..old_u };
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
    ensures forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
{
    mmap_1g_clear_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range, true, false);
    reveal(mmap_1g_range_step); reveal(mmap_1g_flush_step_pre); reveal(unmap_4k_tlb_flush_step);
}

/// Recording the flush in the progress and releasing this cpu's read hold on the cpu set of the thread's container is the flushed step on `pre`/`post`.
pub(super) proof fn mmap_1g_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, range: VaRange1G)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: false }),
        pre.thread_map[thrd_ptr].owning_container == ctn_ptr,
        pre.thread_map.dom().contains(thrd_ptr),
        pre.container_map[ctn_ptr].cpu_set_lock.read_held_by(cpu_id),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: true }), ..pre.thread_map[thrd_ptr]
            }),
            container_map: pre.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: pre.container_map[ctn_ptr].cpu_set_lock.without_reader(cpu_id), ..pre.container_map[ctn_ptr] }),
            ..pre
        }),
    ensures mmap_1g_flushed_step(pre, post, cpu_id),
{ reveal(mmap_1g_flushed_step); }

/// Recording the flush in the progress from `pre` to `post` after range steps that start at `start`, where `pre` extends the step's start `snap` by page-table ghost state and by this cpu's released read hold on the cpu set of its container, while the caller write-holds its cpu, its
/// thread, and the pagetable of the thread's present process with a hidden L3 entry, leaves only range steps.
pub(super) proof fn mmap_1g_flushed_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, snap: &KernelK, pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, range: VaRange1G,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_1g_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: kernel_k_to_kernel_u(*snap), new_u: kernel_k_to_kernel_u(*post) }),
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: false }),
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
        snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().read_held_by(cpu_id),
        pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u()
            == snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().without_reader(cpu_id),
        *post == (KernelK { thrd_mp: post.thrd_mp, ..*pre }),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: true }),
    ensures forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
{
    let ghost_tables = KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*snap };
    reveal(kernel_cpu_nonlock_fields_unchanged); kernel_u_domains_projection(snap); kernel_container_projection_at(snap, ctn_ptr);
    kernel_cpu_tlb_updated_implies_u_step(snap, &ghost_tables);
    kernel_cpu_set_lock_mode_changed_implies_u_step(&ghost_tables, pre, ctn_ptr);
    kernel_thread_syscall_progress_changed_implies_u_step(pre, post, thrd_ptr);
    mmap_1g_clear_step_pre_from_k(pre, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range, true, false);
    assert(mmap_1g_flush_step_pre(kernel_k_to_kernel_u(*snap), cpu_id)) by { reveal(mmap_1g_flush_step_pre); };
    mmap_1g_flushed_step_from_u(kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id, thrd_ptr, ctn_ptr, range);
    reveal(mmap_1g_range_step);
}

/// A container 4K quota credit to the container `ctn_ptr` of the caller's current thread `thrd_ptr`, recorded from `entry`'s projection while the caller write-holds its cpu, its thread, and its pagetable after the flush was recorded, after range steps that start at `start` leaves only
/// range steps.
pub(super) proof fn mmap_1g_reclaim_range_steps_from_k(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, range: VaRange1G,
)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_1g_range_step(before[j], cpu_id),
        steps.view().len() == before.len() + 1,
        steps.view().drop_last() == before,
        steps.view().last().old_u == kernel_k_to_kernel_u(*entry),
        kernel_u_container_quota_4k_increased(steps.view().last().old_u, steps.view().last().new_u, ctn_ptr),
        typed_lock_maps_aligned(entry, lctx),
        entry.thrd_mp.dom().contains(thrd_ptr),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        entry.prc_mp.dom().contains(prc_ptr),
        entry.ctn_mp.dom().contains(ctn_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: true }),
    ensures
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
{
    vstd::assert_seqs_equal!(steps.view() == before.push(steps.view().last()));
    mmap_1g_clear_step_pre_from_k(entry, lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range, true, true);
    reveal(mmap_1g_range_step); reveal(mmap_1g_reclaim_step_pre);
}
} // verus!

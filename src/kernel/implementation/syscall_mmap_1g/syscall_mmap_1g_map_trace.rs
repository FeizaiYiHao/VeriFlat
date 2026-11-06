use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_spec::*;

verus! {
/// Publishing `va`, page `mapped` of `range`, as a present, writable, executable 1G leaf of the `Owned1g` page staged in `pre` for the thread's container, while the caller write-holds its cpu, its thread, and the pagetable of the thread's process, is the leaf step from `pre`'s projection
/// to `post`'s.
pub(super) proof fn mmap_1g_leaf_step_from_k(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    range: VaRange1G, mapped: usize, directory: bool, hidden: bool, flushed: bool,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..*pre }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_1g: post.thrd_mp.spec_index(thrd_ptr).view().quota_1g, temp_alloc_cache_1g: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() == pre.pt_mp.spec_index(pagetable_ptr).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(va),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        spec_va_1g_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        page_ptr_valid(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).addr),
        pre.pg_arr.spec_index(page_ptr2page_index(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).addr)).view().view().state is Owned1g,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped, directory, hidden, flushed }),
        mapped < range.len,
        range.view()[mapped as int] == va,
        post.thrd_mp.spec_index(thrd_ptr).view().quota_1g == pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g - 1,
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_1g_progress_after_leaf(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).write,
        !whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).execute_disable,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).owning_container.view() == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
    ensures
        mmap_1g_leaf_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        mmap_1g_leaf_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    kernel_thread_quota_1g_progress_and_1g_mapping_added_pagetable_wlocked_implies_u_step(pre, post, lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr, va);
    reveal(mmap_1g_leaf_step_pre); reveal(mmap_1g_leaf_step);
}

/// A leaf step pushed after range steps that start at `start` leaves only range steps after `start` and keeps the earlier steps.
pub(super) proof fn mmap_1g_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_1g_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        mmap_1g_leaf_step_pre(steps.view().last().old_u, cpu_id),
        mmap_1g_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_1g_range_step); }

/// A directory step pushed after range steps that start at `start` leaves only range steps after `start` and keeps the earlier steps.
pub(super) proof fn mmap_1g_range_steps_from_directory(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> mmap_1g_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        mmap_1g_directory_step_pre(steps.view().last().old_u, cpu_id),
        mmap_1g_directory_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
{ reveal(mmap_1g_range_step); }
} // verus!

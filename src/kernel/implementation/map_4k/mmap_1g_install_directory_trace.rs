use vstd::prelude::*;
use crate::*;
use super::mmap_1g_install_directory::*;

verus! {
/// The running thread's 1G mmap progress installs one L3 directory page under the big write lock of its table, which creates no window. The transition is one 1G mmap directory step.
pub(super) proof fn mmap_1g_directory_step_from_k(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
    pagetable_ptr: RwLockPageTableRoot)
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
            quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k, temp_alloc_cache_4k: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.prc_mp.dom().contains(prc_ptr) && pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is Some && pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0 is Mmap1g,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap1g_mapped < pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap1g_range.len,
        !pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap1g_directory,
        kernel_thread_quota_4k_changed(pre, post, thrd_ptr, -1),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_1g_progress_after_directory(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()),
    ensures
        mmap_1g_directory_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        mmap_1g_directory_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(mmap_1g_directory_step_pre); reveal(mmap_1g_directory_step); reveal(kernel_thread_quota_4k_changed);
    kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre, post, lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr);
    process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, prc_ptr); kernel_process_projection_at(pre, prc_ptr);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let owner = pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr;
    if pre_u.process_map.dom().contains(owner) && pre_u.process_map[owner].pagetable is Some {
        assert(pre_u.process_map.insert(owner, ProcessU {
            pagetable: Some(PageTableU { pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..pre_u.process_map[owner].pagetable->Some_0 }),
            ..pre_u.process_map[owner]
        }) =~= pre_u.process_map);
    }
}
} // verus!

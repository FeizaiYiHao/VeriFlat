use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure_spec::*;

verus! {
/// The running thread's mmap progress installs one directory page under either big-lock mode of its table; the transition is
/// one mmap directory step.
pub(super) proof fn mmap_4k_directory_step_from_k(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    pagetable_ptr: RwLockPageTableRoot, level: MissingPageTableLevel, write_held: bool)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        write_held ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        !write_held ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some && pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped < pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.len,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3,
        !(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill)
            ==> mmap_4k_directory_rank(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level)),
        kernel_thread_quota_4k_changed(pre, post, thread_ptr, -1),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), level),
    ensures
        mmap_4k_directory_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        mmap_4k_directory_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); reveal(kernel_thread_quota_4k_changed);
    if write_held { kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre, post, lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr); }
    else { kernel_thread_quota_4k_and_progress_changed_pagetable_rlocked_implies_u_step(pre, post, lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr); }
}
} // verus!

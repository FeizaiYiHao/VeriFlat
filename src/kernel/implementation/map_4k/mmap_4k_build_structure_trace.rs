use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure_spec::*;

verus! {
/// The running thread's mmap progress installs one directory page under either big-lock mode of its table; a new L2 page under
/// L3 entry `(l4i, l3i)` adds its windows with `lo..=hi`, the recorded range's windows there, held. The transition is one mmap
/// directory step.
pub(super) proof fn mmap_4k_directory_step_from_k(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
    pagetable_ptr: RwLockPageTableRoot, level: MissingPageTableLevel, write_held: bool, l4i: L4Index, l3i: L3Index, lo: L2Index, hi: L2Index)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        write_held ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        !write_held ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
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
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is Some && pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped < pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.len,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3,
        !(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill)
            ==> mmap_4k_directory_rank(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level)),
        kernel_thread_quota_4k_changed(pre, post, thrd_ptr, -1),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), level),
        KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i),
        level is L3 ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == Map::new(
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((l4i, l3i, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
            |w: WindowVa| if whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) { whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks[w] }
                else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked } else { LockStateU::Unlocked }),
        level is L3 ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((l4i, l3i, 0usize, 0usize)) }),
        level is L3 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range).contains(w)]
            w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i
                ==> va_range_2m_windows(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range).contains(w) == (lo <= spec_v2l2index(w.va) <= hi),
        !(level is L3) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
    ensures
        mmap_4k_directory_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        mmap_4k_directory_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); reveal(kernel_thread_quota_4k_changed);
    broadcast use spec_index2va_2m_valid, Set::lemma_map_by_contains;
    if write_held { kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre, post, lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr); }
    else { kernel_thread_quota_4k_and_progress_changed_pagetable_rlocked_implies_u_step(pre, post, lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr); }
    process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, prc_ptr); kernel_process_projection_at(pre, prc_ptr);
    if level is L3 {
        let old_windows = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks;
        let range = pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range;
        assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks =~= pagetable_window_locks_after_new_l2_page(old_windows, l4i, l3i, range));
    }
}
} // verus!

use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_range::mmap_4k_map_leaf_range;
use super::mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
/// With `cpu_id` write-held and Running since the entry snapshot: write-locks its current thread unless that thread is being
/// killed, and returns the current process, thread, and container, the container's 4K allocator, the process pagetable, the
/// thread's 4K quota, and the thread and cpu perms. If the thread is being killed, releases the cpu and finishes the call
/// without recording a step.
pub(super) fn mmap_4k_lock_current_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize,
    Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: Option<(RwLockProcessPtr, RwLockThreadPtr, RwLockContainerPtr, RwLockPageAllocatorPtr, RwLockPageTableRoot, usize, Tracked<LockPerm>, Tracked<LockPerm>)>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.inv(),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ret is None ==> {
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& final(steps).view() == old(steps).view()
            &&& final(steps).nonlock_view() == old(steps).nonlock_view()
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& RetValueType::ErrorThreadKilled == mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range)
        },
        ret is Some ==> {
            let (process_ptr, thread_ptr, container_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, thread_lock_perm, cpu_perm) = ret.unwrap();
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let thread = final(krnl).thr_mp.spec_index(thread_ptr);
            &&& *final(steps) == *old(steps)
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr)
            &&& wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), thread, old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), final(lctx), thread_lock_perm.view())
            &&& cpu_perm.view() == cpu_lock_perm
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& final(krnl).ctn_mp.dom().contains(container_ptr)
            &&& final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
            &&& final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k)
            &&& final(krnl).prc_mp.dom().contains(process_ptr)
            &&& !final(krnl).prc_mp.spec_index(process_ptr).view().zombie
            &&& final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
            &&& final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
            &&& final(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
            &&& final(krnl).pt_mp.dom().contains(pagetable_ptr)
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_container == container_ptr
            &&& thread.view().owning_proc == process_ptr
            &&& thread.view().proc_pagetable_ptr == pagetable_ptr
            &&& thread.view().quota_4k == quota_4k
            &&& thread.view().free_quota_pending_clean()
            &&& thread.view().temp_alloc_clean()
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.view_ghost().exited
            &&& !(thread.view().quota_4k >= 4 * range) ==> RetValueType::ErrorNoQuota == mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range)
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).thread_lock_map().dom() =~= set![thread_ptr]
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).container_lock_map().dom().is_empty()
            &&& final(lctx).process_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_cache_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_cache_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_1g_lock_map().dom().is_empty()
            &&& final(lctx).allocator_cache_1g_lock_map().dom().is_empty()
            &&& final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
        },
{
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
        &&& cpu.current_process() is Some
        &&& cpu.current_thread() is Some
        &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
        &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
        &&& !krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().zombie
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().container_depth == cpu.view().container_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().process_depth == cpu.view().process_depth
    }) by {
        container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();

    let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thread_ptr), None, None, None);
            mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorThreadKilled);
        }
        return None;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();

    assert(krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); };
    let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
    let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let pagetable_ptr = thread.proc_pagetable_ptr;
    let quota_4k = thread.quota_4k;

    assert({
        &&& krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
        &&& krnl.pt_mp.dom().contains(pagetable_ptr)
        &&& krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
        &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
    }) by {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
    };
    proof { if quota_4k < 4 * range { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorNoQuota); } }
    Some((process_ptr, thread_ptr, container_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)))
}

/// With `cpu_id`, its current `thread_ptr`, and, if `pagetable_lock_perm` is given, `pagetable_ptr` write-held since the entry
/// snapshot and otherwise unchanged: releases them all and finishes the call without recording a step.
pub(super) fn mmap_4k_unlock_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, pagetable_lock_perm: Option<Tracked<LockPerm>>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        match pagetable_lock_perm {
            Some(perm) => {
                &&& old(krnl).pt_mp.dom().contains(pagetable_ptr)
                &&& old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable_ptr)
                &&& wlock_ensures(old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr), old(krnl).pt_mp.spec_index(pagetable_ptr), old(steps).snapshot_k().pt_mp.lock_id_by_key(pagetable_ptr), old(lctx), perm.view())
                &&& pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable_ptr, old(krnl).pt_mp.spec_index(pagetable_ptr).view())
                &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().leaves_present()
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
                &&& old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr]
            },
            None => old(krnl).pt_mp == old(steps).snapshot_k().pt_mp && old(lctx).pagetable_lock_map().dom().is_empty(),
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).snapshot_k() == *final(krnl),
{
    let ghost table = if pagetable_lock_perm is Some { Some(pagetable_ptr) } else { None };
    if let Some(perm) = pagetable_lock_perm { krnl.wunlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), perm); }
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thread_ptr), None, table, None); }
}

/// With `cpu_id`, its current `thread_ptr`, and the process pagetable `pagetable_ptr` write-held since the entry snapshot
/// `entry_lctx` was aligned with, and `va_range` checked free: records the progress, enters the kernel step, maps every page,
/// clears the progress, releases all three locks, and records the exiting step.
pub(super) fn mmap_4k_map_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        va_range.len > 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable_ptr),
        wlock_ensures(old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr), old(krnl).pt_mp.spec_index(pagetable_ptr), old(steps).snapshot_k().pt_mp.lock_id_by_key(pagetable_ptr), old(lctx), pagetable_lock_perm),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable_ptr, old(krnl).pt_mp.spec_index(pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().leaves_present(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(va_range.start),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_empty(va_range.start, va_range.view().spec_index((va_range.len - 1) as int)),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_buildable(va_range),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_range_empty(spec_va2index(va), spec_va2index(va_range.view()[range - 1])),
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> {
            let idx = spec_va2index(va_range.view()[j]);
            &&& !old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            &&& !old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
            &&& !old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va_range.view()[j])
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        range + 2 <= final(steps).nonlock_view().len() <= 4 * range + 2,
        mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        mmap_4k_syscall_range_mapped(final(krnl).pt_mp.spec_index(pagetable_ptr).view(), va, range),
        RetValueType::Success == mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range),
{
    proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Success); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Mmap4k { range: *va_range, mapped: 0, directory: Mmap4kDirectory::None })), Tracked(&*lctx), Tracked(&thread_lock_perm));
    proof {
        let ghost entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(mmap_4k_trace_after_enter(steps.view(), cpu_id, *va_range)) by {
            reveal(PageTable::spec_mapping_4k_va_range_empty); va_range.va_range_lemma();
            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&old(steps).snapshot_k(), &entered_k, &entry_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr);
            mmap_4k_enter_step_pre_from_k(&old(steps).snapshot_k(), cpu_id, process_ptr, thread_ptr);
            mmap_4k_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, process_ptr, thread_ptr, *va_range);
            mmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *va_range);
        };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.prc_mp.dom().contains(process_ptr) && !krnl.prc_mp.spec_index(process_ptr).view().zombie) by {
            container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        };
        assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); };
    }
    let ghost entered = steps.view();
    mmap_4k_map_leaf_range(krnl, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm));
    proof {
        assert(mmap_4k_trace_after_range(steps.view(), cpu_id, *va_range)) by { mmap_4k_trace_range_steps(&*steps, entered, cpu_id, *va_range); };
        assert(mmap_4k_syscall_range_mapped(krnl.pt_mp.spec_index(pagetable_ptr).view(), va, range)) by { va_range.va_range_lemma(); };
    }
    mmap_4k_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, thread_ptr, process_ptr, pagetable_ptr, Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(cpu_lock_perm));
}

/// With `cpu_id`, its current `thread_ptr`, and the process pagetable `pagetable_ptr` write-held and the whole `va_range`
/// mapped and recorded: clears the progress, releases all three locks, and records the exiting step.
pub(super) fn mmap_4k_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, Tracked(thread_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        mmap_4k_trace_after_range(old(steps).view(), cpu_id, *va_range),
        range + 1 <= old(steps).nonlock_view().len() <= 4 * range + 1,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *va_range, mapped: range, directory: Mmap4kDirectory::None }),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable_ptr, old(krnl).pt_mp.spec_index(pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().leaves_present(),
        mmap_4k_syscall_range_mapped(old(krnl).pt_mp.spec_index(pagetable_ptr).view(), va, range),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        mmap_4k_syscall_range_mapped(final(krnl).pt_mp.spec_index(pagetable_ptr).view(), va, range),
{
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_lock_perm));
    krnl.wunlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost exit_k = *krnl;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
        assert(mmap_4k_syscall_trace(steps.view(), cpu_id, va, range)) by {
            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(old(krnl), &exit_k, old(lctx), cpu_id, thread_ptr, process_ptr, pagetable_ptr);
            mmap_4k_exit_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(exit_k), cpu_id, process_ptr, thread_ptr);
            va_range.va_range_lemma();
            mmap_4k_trace_exit_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(exit_k), cpu_id, va, range);
        };
    }
}
/// With `cpu_id` and its current `thread_ptr` write-held since the entry snapshot `entry_lctx` was aligned with and the
/// thread's quota sufficient: write-locks the process pagetable `pagetable_ptr`, and maps `va_range` and finishes with the
/// recorded steps if it is free, or otherwise releases every lock and finishes without recording a step.
pub(super) fn mmap_4k_lock_pagetable_and_map(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        va_range.len > 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret == mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range),
        ret is Success ==> range + 2 <= final(steps).nonlock_view().len() <= 4 * range + 2,
        !(ret is Success) ==> final(steps).view() == old(steps).view() && final(steps).nonlock_view() == old(steps).nonlock_view(),
        ret is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
        ret is Success ==> final(krnl).pt_mp.dom().contains(pagetable_ptr) && mmap_4k_syscall_range_mapped(final(krnl).pt_mp.spec_index(pagetable_ptr).view(), va, range),
{
    let Tracked(pagetable_lock_perm) = krnl.wlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
    let precheck = mmap_4k_precheck(krnl, va_range, pagetable_ptr, Tracked(&*lctx), Tracked(&pagetable_lock_perm));
    if let Mmap4kPrecheck::Ready = precheck {
        mmap_4k_map_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, pagetable_ptr,
            Ghost(entry_lctx), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(cpu_lock_perm));
        return RetValueType::Success;
    }
    let ret = if let Mmap4kPrecheck::Invalid = precheck {
        proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Error); }
        RetValueType::Error
    } else {
        proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorVaInUse); }
        RetValueType::ErrorVaInUse
    };
    mmap_4k_unlock_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, pagetable_ptr, Some(Tracked(pagetable_lock_perm)), Tracked(thread_lock_perm), Tracked(cpu_lock_perm));
    ret
}
} // verus!

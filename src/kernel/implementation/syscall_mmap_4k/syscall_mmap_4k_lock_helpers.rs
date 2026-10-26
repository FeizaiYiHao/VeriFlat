use vstd::prelude::*;
use crate::*;
use super::mmap_4k_read_enter::mmap_4k_try_read_enter;
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
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
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
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, final(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl))
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
            &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
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

    let thread_res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thread_ptr), None, None, None);
            mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorThreadKilled, None, None);
        }
        return None;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }

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
    proof { if quota_4k < 4 * range { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorNoQuota, None, None); } }
    Some((process_ptr, thread_ptr, container_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)))
}

/// With `cpu_id` and its current `thread_ptr` write-held since the entry snapshot and otherwise unchanged: releases both and
/// finishes the call without recording a step.
fn mmap_4k_unlock_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
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
        old(lctx).pagetable_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
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
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).snapshot_k() == *final(krnl),
{
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thread_ptr), None, None, None); }
}

/// Write-locks `cpu_id` while it runs a live thread, then that thread, and with enough quota maps `va_range` through
/// `mmap_4k_try_read_enter`, which keeps both locks to fill when reading finds a 2M window of the range missing. Returns the
/// result and the state of the section that decided it.
pub(super) fn mmap_4k_attempt(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
) -> (ret: (RetValueType, Ghost<KernelU>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        va_range.len > 0,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret.0 == mmap_4k_syscall_result(ret.1@, cpu_id, va, range),
        !(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is Success)
            && !(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorVaInUse) ==> ret.1@ == kernel_k_to_kernel_u(*old(krnl)),
        ret.0 is Success ==> range + 2 <= final(steps).nonlock_view().len() <= 4 * range + 3,
        ret.0 is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Read) && ret.1@ == final(steps).view()[0].old_u
            || mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Fill) && ret.1@ == final(steps).view()[1].old_u,
        ret.0 is Success ==> mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range),
        !(ret.0 is Success) ==> final(steps).nonlock_view().len() == 0,
        !(ret.0 is Success) ==> final(steps).view().len() == 0 || mmap_4k_syscall_failure_trace(final(steps).view(), cpu_id, va, range) && ret.1@ == final(steps).view()[1].old_u,
{
    let ghost entry_lctx = *lctx;
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof { mmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::CpuIdle, None, None); }
        return (RetValueType::CpuIdle, Ghost(kernel_k_to_kernel_u(*old(krnl))));
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let locked = mmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, Tracked(cpu_lock_perm));
    if locked.is_none() { return (RetValueType::ErrorThreadKilled, Ghost(kernel_k_to_kernel_u(*old(krnl)))); }
    let (process_ptr, thread_ptr, container_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)) = locked.unwrap();
    if quota_4k < 4 * range {
        mmap_4k_unlock_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, Tracked(thread_lock_perm), Tracked(cpu_lock_perm));
        return (RetValueType::ErrorNoQuota, Ghost(kernel_k_to_kernel_u(*old(krnl))));
    }
    mmap_4k_try_read_enter(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, pagetable_ptr,
        Ghost(entry_lctx), Tracked(thread_lock_perm), Tracked(cpu_lock_perm))
}
} // verus!

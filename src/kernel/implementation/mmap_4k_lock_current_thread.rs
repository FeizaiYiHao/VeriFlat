use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_seqs_equal_internal, assert_sets_equal, assert_sets_equal_internal};
use crate::*;

verus! {
/// With `cpu_id` write-held and Running: write-locks its current thread and returns its process, thread, container, 4K allocator,
/// pagetable, 4K quota, and thread and cpu perms; if the thread is being killed, releases the cpu and finishes without a step.
pub fn mmap_4k_lock_current_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: Option<(RwLockProcessPtr, RwLockThreadPtr, RwLockContainerPtr, RwLockPageAllocatorPtr, RwLockPageTableRoot, usize, Tracked<LockPerm>, Tracked<LockPerm>)>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(krnl).cpu_arr.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
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
        {
            let snap = old(steps).snapshot_k();
            let cpu = snap.cpu_arr.spec_index(cpu_id).value;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            &&& cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& snap.thrd_mp.dom().contains(thrd_ptr) && snap.prc_mp.dom().contains(snap.thrd_mp.spec_index(thrd_ptr).view().owning_proc)
            &&& ret is None ==> snap.thrd_mp.spec_index(thrd_ptr).being_killed()
            &&& ret is Some ==> ret.unwrap().1 == thrd_ptr && !snap.thrd_mp.spec_index(thrd_ptr).being_killed() && snap.thrd_mp.spec_index(thrd_ptr).view().quota_4k == ret.unwrap().5
        },
        ret is None ==> {
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& final(steps).view() == old(steps).view()
            &&& final(steps).snapshot_k() == *final(krnl)
        },
        ret is Some ==> {
            let (prc_ptr, thrd_ptr, ctn_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, thread_lock_perm, cpu_perm) = ret.unwrap();
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let thread = final(krnl).thrd_mp.spec_index(thrd_ptr);
            &&& *final(steps) == *old(steps)
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& *final(krnl) == (KernelK { thrd_mp: final(krnl).thrd_mp, ..*old(krnl) })
            &&& final(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr)
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, final(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl))
            &&& wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), thread, old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), final(lctx), thread_lock_perm.view())
            &&& cpu_perm.view() == cpu_lock_perm
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& final(krnl).ctn_mp.dom().contains(ctn_ptr)
            &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
            &&& final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k)
            &&& final(krnl).prc_mp.dom().contains(prc_ptr)
            &&& !final(krnl).prc_mp.spec_index(prc_ptr).view().zombie
            &&& final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr
            &&& final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr
            &&& final(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr
            &&& final(krnl).pt_mp.dom().contains(pagetable_ptr)
            &&& final(krnl).thrd_mp.dom().contains(thrd_ptr)
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_container == ctn_ptr
            &&& thread.view().owning_proc == prc_ptr
            &&& thread.view().proc_pagetable_ptr == pagetable_ptr
            &&& thread.view().quota_4k == quota_4k
            &&& thread.view().free_quota_pending_clean()
            &&& thread.view().temp_alloc_clean()
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.view().exited.view()
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).thread_lock_map().dom() =~= set![thrd_ptr]
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
        &&& krnl.thrd_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thrd_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thrd_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thrd_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.thrd_mp.spec_index(cpu.current_thread().unwrap()).view().container_depth == cpu.view().container_depth
        &&& krnl.thrd_mp.spec_index(cpu.current_thread().unwrap()).view().process_depth == cpu.view().process_depth
    }) by {
        container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let prc_ptr = cpu.current_process().unwrap();
    let thrd_ptr = cpu.current_thread().unwrap();
    let ctn_ptr = cpu.owning_container();

    let thread_res = krnl.wlock_current_running_thread_unless_killed(thrd_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert_seqs_equal!(krnl.cpu_op.view().view(), old(steps).snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, None, None);
        }
        return None;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }

    assert(krnl.ctn_mp.view().spec_index(ctn_ptr).is_init() && krnl.ctn_mp.view().spec_index(ctn_ptr).addr() == ctn_ptr) by { container_perms_wf_at(krnl.ctn_mp, ctn_ptr); };
    let container_ro = krnl.ctn_mp.borrow_rodata(ctn_ptr);
    let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
    let thread = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let pagetable_ptr = thread.proc_pagetable_ptr;
    let quota_4k = thread.quota_4k;

    assert({
        &&& krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
        &&& krnl.pt_mp.dom().contains(pagetable_ptr)
        &&& krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr
        &&& krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr
    }) by {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    };
    Some((prc_ptr, thrd_ptr, ctn_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)))
}

/// With `cpu_id` and its current `thrd_ptr` write-held since the entry snapshot and otherwise unchanged: releases both and
/// finishes the call without recording a step.
pub fn mmap_4k_unlock_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        cpu_id == old(lctx).cpu_id(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_lock_perm),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view().exited.view(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
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
        final(steps).snapshot_k() == *final(krnl),
{
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, None, None);
    }
}

/// With `cpu_id` and its current `thrd_ptr` write-held since the entry snapshot and `pagetable_ptr` read-held by
/// `pagetable_lock_perm` with no window held and the table's window locks as in that snapshot: releases all three and finishes
/// the call without recording a step.
pub fn mmap_4k_unlock_read_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable_ptr),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_lock_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).wlocked(),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locked_by_thread(old(lctx).thread_id()),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
            reader_map: (if old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread() is Read { old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map } else { Map::empty() })
                .insert(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        }),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).view(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).being_killed(),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_1g(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks
            == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view().exited.view(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
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
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
{
    proof {
        if old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread() is Read {
            assert_maps_equal!(old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.insert(lctx.thread_id(), pagetable_lock_perm.lock_id())
                .remove(lctx.thread_id()), old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map);
        } else {
            assert_sets_equal!(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom(), Set::empty());
        }
    }
    krnl.runlock_pagetable(cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable_ptr), None);
    }
}

/// The L2 bounds `(lo, hi)` of the 2M windows of `range` below the L3 entry of its page `cur_va`: such a window covers `range`
/// exactly when its L2 index lies in `lo..=hi`.
pub fn mmap_4k_range_l2_bounds(range: &VaRange4K, cur_va: VAddr, cur: (L4Index, L3Index, L2Index, L1Index), start_indices: (L4Index, L3Index, L2Index, L1Index),
    end_indices: (L4Index, L3Index, L2Index, L1Index)) -> (ret: (L2Index, L2Index))
    requires
        range.wf(),
        range.len > 0,
        spec_va_4k_valid(cur_va),
        range.start <= cur_va <= range.view()[range.len - 1],
        cur == spec_va2index(cur_va),
        start_indices == spec_va2index(range.start),
        end_indices == spec_va2index(range.view()[range.len - 1]),
    ensures
        ret.0 == (if cur.0 == start_indices.0 && cur.1 == start_indices.1 { start_indices.2 } else { 0usize }),
        ret.1 == (if cur.0 == end_indices.0 && cur.1 == end_indices.1 { end_indices.2 } else { 511usize }),
        pei_valid(ret.0) && pei_valid(ret.1),
        ret.0 <= cur.2 <= ret.1,
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)] w.wf() && spec_v2l4index(w.va) == cur.0 && spec_v2l3index(w.va) == cur.1
            ==> va_range_2m_windows(*range).contains(w) == (ret.0 <= spec_v2l2index(w.va) <= ret.1),
{
    let lo = if cur.0 == start_indices.0 && cur.1 == start_indices.1 { start_indices.2 } else { 0 };
    let hi = if cur.0 == end_indices.0 && cur.1 == end_indices.1 { end_indices.2 } else { 511 };
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        spec_va_4k_valid_index_roundtrip(cur_va); spec_va_4k_valid_index_roundtrip(range.start); spec_va_4k_valid_index_roundtrip(range.view()[range.len - 1]);
        spec_index2va_le_implies_4k_indices_lex_le(start_indices, cur); spec_index2va_le_implies_4k_indices_lex_le(cur, end_indices);
    }
    (lo, hi)
}
} // verus!

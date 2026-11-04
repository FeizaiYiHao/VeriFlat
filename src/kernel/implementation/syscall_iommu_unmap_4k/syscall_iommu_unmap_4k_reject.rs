use vstd::prelude::*;
use crate::*;

verus! {
/// With cpu `cpu_id` and its running thread's container, process, and thread write-held since the entry snapshot and nothing
/// else held: releases all four and finishes the call without recording a step.
pub(super) fn iommu_unmap_4k_unlock_thread_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(container_perm): Tracked<LockPerm>,
    Tracked(process_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thrd_mp: old(krnl).thrd_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, ctn_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, prc_ptr),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() })
            &&& post.view().view() == pre.view().view()
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        ({
            let pre = old(steps).snapshot_k().ctn_mp.spec_index(ctn_ptr);
            let post = old(krnl).ctn_mp.spec_index(ctn_ptr);
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: container_perm.lock_id() })
            &&& post.lock_process_owner_u() == Some(LockOwnerId::Some(old(steps).snapshot_k().prc_mp.spec_index(prc_ptr).view_rodata().view().depth))
            &&& post.view() == pre.view()
            &&& post.view_rodata() == pre.view_rodata()
            &&& post.view_ghost() == pre.view_ghost()
            &&& post.being_killed() == pre.being_killed()
            &&& container_perm.state() is WriteLock
            &&& container_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(prc_ptr), old(krnl).prc_mp.spec_index(prc_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(prc_ptr), old(lctx), process_perm),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(ctn_ptr) && !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).prc_mp.dom().contains(prc_ptr) && !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running,
        old(krnl).thrd_mp.dom().contains(thrd_ptr) && !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean() && old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id] && old(lctx).container_lock_map().dom() =~= set![ctn_ptr],
        old(lctx).process_lock_map().dom() =~= set![prc_ptr] && old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty() && old(lctx).iommu_table_lock_map().dom().is_empty() && old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty() && old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).cpu_set_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
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
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(prc_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(ctn_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(ctn_ptr), Some(prc_ptr), Some(thrd_ptr), None, None, None);
    }
}

/// With cpu `cpu_id`, its running thread's container, process, and thread, and the process's IOMMU table `iommu_table`
/// write-held since the entry snapshot and nothing else held: releases all five and finishes the call without recording a step.
pub(super) fn iommu_unmap_4k_unlock_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, iommu_table: RwLockPageTableRoot, Tracked(cpu_perm): Tracked<LockPerm>,
    Tracked(container_perm): Tracked<LockPerm>, Tracked(process_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(iommu_table_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thrd_mp: old(krnl).thrd_mp, it_mp: old(krnl).it_mp,
            ..old(steps).snapshot_k()
        }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, ctn_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, prc_ptr),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).it_mp.unchanged_except(&old(steps).snapshot_k().it_mp, iommu_table),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() })
            &&& post.view().view() == pre.view().view()
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        ({
            let pre = old(steps).snapshot_k().ctn_mp.spec_index(ctn_ptr);
            let post = old(krnl).ctn_mp.spec_index(ctn_ptr);
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: container_perm.lock_id() })
            &&& post.lock_process_owner_u() == Some(LockOwnerId::Some(old(steps).snapshot_k().prc_mp.spec_index(prc_ptr).view_rodata().view().depth))
            &&& post.view() == pre.view()
            &&& post.view_rodata() == pre.view_rodata()
            &&& post.view_ghost() == pre.view_ghost()
            &&& post.being_killed() == pre.being_killed()
            &&& container_perm.state() is WriteLock
            &&& container_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(prc_ptr), old(krnl).prc_mp.spec_index(prc_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(prc_ptr), old(lctx), process_perm),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        wlock_ensures(old(steps).snapshot_k().it_mp.spec_index(iommu_table), old(krnl).it_mp.spec_index(iommu_table), old(steps).snapshot_k().it_mp.lock_id_by_key(iommu_table), old(lctx), iommu_table_perm),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(ctn_ptr) && !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).prc_mp.dom().contains(prc_ptr) && !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running,
        old(krnl).thrd_mp.dom().contains(thrd_ptr) && !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean() && old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).it_mp.dom().contains(iommu_table) && old(krnl).it_mp.spec_index(iommu_table).view().leaves_present(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id] && old(lctx).container_lock_map().dom() =~= set![ctn_ptr],
        old(lctx).process_lock_map().dom() =~= set![prc_ptr] && old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table],
        old(lctx).pagetable_lock_map().dom().is_empty() && old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty() && old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).cpu_set_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
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
    krnl.wunlock_iommu_table(iommu_table, Tracked(&mut *lctx), Tracked(iommu_table_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(prc_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(ctn_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks_with_iommu_table(&*krnl, &*lctx, cpu_id, Some(ctn_ptr), Some(prc_ptr), Some(thrd_ptr), None, None, None, Some(iommu_table));
    }
}
} // verus!

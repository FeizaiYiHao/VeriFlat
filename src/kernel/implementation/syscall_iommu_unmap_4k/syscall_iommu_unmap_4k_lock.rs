use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_unmap_4k_spec::*;
use super::syscall_iommu_unmap_4k_trace::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::locker_unlocker::u_sys_exit_eof;

verus! {
pub(super) struct IommuUnmap4kLocked {
    pub container_ptr: RwLockContainerPtr, pub process_ptr: RwLockProcessPtr, pub thread_ptr: RwLockThreadPtr,
    pub cpu_lock_perm: Tracked<LockPerm>, pub container_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>, pub thread_lock_perm: Tracked<LockPerm>,
}

/// Write-locks cpu `cpu_id`, its container, process, and running thread, rejecting an idle or killed cpu, a killed or zombie
/// container, and a killed process or thread with every lock released and no step; otherwise returns the four locks held.
pub(super) fn iommu_unmap_4k_lock_running_thread(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, iova: VAddr, range: usize)
    -> (ret: Result<IommuUnmap4kLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(iova) || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range)),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ret is Err ==> ({
            &&& ret->Err_0 == iommu_unmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, iova, range)
            &&& !(ret->Err_0 is Success)
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(steps).view() == old(steps).view()
            &&& final(steps).nonlock_view() == old(steps).nonlock_view()
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl))
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let thread = final(krnl).thr_mp.spec_index(e.thread_ptr).view();
            &&& *final(steps) == *old(steps)
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.thread_ptr]
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ2m)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), e.container_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.process_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.thread_ptr, TypedLockMode::Write)
            &&& e.cpu_lock_perm.view().state() is WriteLock && e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: e.cpu_lock_perm.view().lock_id() })
            &&& !old(krnl).cpu_arr.spec_index(cpu_id).view().locked()
            &&& cpu == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view_ghost() == Some(cpu_id)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
            &&& !old(krnl).ctn_mp.spec_index(e.container_ptr).locked()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: e.container_lock_perm.view().lock_id() })
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(final(krnl).prc_mp.spec_index(e.process_ptr).view_rodata().view().depth))
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).view() == old(krnl).ctn_mp.spec_index(e.container_ptr).view()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(e.container_ptr).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(e.container_ptr).being_killed()
            &&& e.container_lock_perm.view().state() is WriteLock
            &&& e.container_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& wlock_ensures(old(krnl).prc_mp.spec_index(e.process_ptr), final(krnl).prc_mp.spec_index(e.process_ptr), old(krnl).prc_mp.lock_id_by_key(e.process_ptr), final(lctx), e.process_lock_perm.view())
            &&& wlock_ensures(old(krnl).thr_mp.spec_index(e.thread_ptr), final(krnl).thr_mp.spec_index(e.thread_ptr), old(krnl).thr_mp.lock_id_by_key(e.thread_ptr), final(lctx), e.thread_lock_perm.view())
            &&& cpu.state is Running && !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.thread_ptr) && cpu.owning_container == e.container_ptr
            &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
            &&& final(krnl).ctn_mp.dom().contains(e.container_ptr) && !final(krnl).ctn_mp.spec_index(e.container_ptr).being_killed() && !final(krnl).ctn_mp.spec_index(e.container_ptr).view().zombie
            &&& !final(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost().owned_processes.view().is_empty()
            &&& final(krnl).prc_mp.dom().contains(e.process_ptr) && !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed() && !final(krnl).prc_mp.spec_index(e.process_ptr).view().zombie
            &&& final(krnl).thr_mp.dom().contains(e.thread_ptr) && !final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == e.container_ptr
            &&& thread.syscall_progress.view() is None && thread.free_quota_pending_clean() && thread.temp_alloc_clean()
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).view_ghost().exited
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view().state.view() is Running
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, e.container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.thread_ptr)
        }),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof { iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::CpuIdle); }
        return Err(RetValueType::CpuIdle);
    }
    let Tracked(cpu_perm) = cpu_lock_res.unwrap();
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
        &&& cpu.current_process() is Some
        &&& cpu.current_thread() is Some
        &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
        &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().owned_threads.view().len() != 0
        &&& !krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().zombie
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_rodata().view().depth == cpu.view().container_depth
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().container_depth == cpu.view().container_depth
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().depth == cpu.view().process_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().container_depth == cpu.view().container_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().process_depth == cpu.view().process_depth
    }) by {
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
        container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, cpu.owning_container, cpu.current_process.unwrap()); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, cpu.current_thread.unwrap());
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, cpu.current_process.unwrap());
    };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    let requested = LockOwnerId::Some(cpu.process_depth());
    let container_res = krnl.wlock_container_unless_killed(container_ptr, requested, Tracked(&mut *lctx));
    let Tracked(container_perm) = match container_res {
        DynamicWLockResult::Acquired(perm) => perm,
        DynamicWLockResult::Killed(_) => {
            proof {
                let ghost pre = *krnl;
                let ghost pre_lctx = *lctx;
                krnl.u_sys_exit(lctx);
                u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
            }
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
                iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorContainerKilled);
            }
            return Err(RetValueType::ErrorContainerKilled);
        },
        DynamicWLockResult::DepthConflict { .. } => {
            proof {
                let ghost pre = *krnl;
                let ghost pre_lctx = *lctx;
                krnl.u_sys_exit(lctx);
                u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
            }
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
                iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorContainerLockOrderConflict);
            }
            return Err(RetValueType::ErrorContainerLockOrderConflict);
        },
    };
    let container = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_perm));
    if container.zombie {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorContainerZombie);
        }
        return Err(RetValueType::ErrorContainerZombie);
    }
    assert(!krnl.prc_mp.spec_index(process_ptr).being_killed() ==> typed_lock_map_ids_lt(lctx.container_lock_map(), krnl.prc_mp.lock_id_by_key(process_ptr))) by { process_perms_wf_at(krnl.prc_mp, process_ptr); };
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), None, None, None, None);
            iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorProcessKilled);
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(process_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorThreadKilled);
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(thread_perm) = thread_res.unwrap();
    Ok(IommuUnmap4kLocked {
        container_ptr, process_ptr, thread_ptr, cpu_lock_perm: Tracked(cpu_perm), container_lock_perm: Tracked(container_perm), process_lock_perm: Tracked(process_perm),
        thread_lock_perm: Tracked(thread_perm),
    })
}
} // verus!

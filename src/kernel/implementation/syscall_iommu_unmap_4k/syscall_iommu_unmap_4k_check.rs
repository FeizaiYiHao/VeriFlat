use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_unmap_4k_spec::*;
use super::syscall_iommu_unmap_4k_trace::*;
use super::syscall_iommu_unmap_4k_lock::*;

verus! {
/// Validates the arguments, write-locks cpu `cpu_id`, its running thread's container, process, and thread, and the process's
/// IOMMU table, and checks that every iova of the range is a present user 4K leaf of it. A rejected call releases every lock,
/// records no step, and returns `iommu_unmap_4k_syscall_result` of the entry state; otherwise the five locks are held, nothing
/// else changed, and the result is Success.
pub(super) fn iommu_unmap_4k_lock_and_check(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, iova: VAddr, range: usize)
    -> (ret: Result<(IommuUnmap4kLocked, RwLockPageTableRoot, Tracked<LockPerm>), RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
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
            &&& final(steps).view().len() == 0
            &&& final(steps).nonlock_view().len() == 0
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl))
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0.0;
            let iommu_table = ret->Ok_0.1;
            let iommu_table_perm = ret->Ok_0.2.view();
            let iova_range = iommu_unmap_4k_iova_range(iova, range);
            let table = final(krnl).it_mp.spec_index(iommu_table);
            &&& RetValueType::Success == iommu_unmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, iova, range)
            &&& *final(steps) == *old(steps)
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.thread_ptr]
            &&& final(lctx).iommu_table_lock_map().dom() =~= set![iommu_table]
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
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
            &&& typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write)
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view().iommu_table == Some(iommu_table)
            &&& final(krnl).it_mp.dom().contains(iommu_table)
            &&& table.view().leaves_present()
            &&& table.view() == old(krnl).it_mp.spec_index(iommu_table).view()
            &&& iommu_table_perm.state() is WriteLock
            &&& iommu_table_perm.thread_id() == final(lctx).thread_id()
            &&& iommu_table_perm.lock_id() == table.locking_thread()->Write_lock_id
            &&& forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range
                ==> table.view().mapping_4k().dom().contains(iova_range.view()[j]) && table.view().mapping_4k()[iova_range.view()[j]].present
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(e.process_ptr)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(e.thread_ptr)
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view().owning_proc == e.process_ptr
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view().owning_container == e.container_ptr
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view().syscall_progress.view() is None
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, it_mp: final(krnl).it_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, e.container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.thread_ptr)
            &&& final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table)
            &&& wlock_ensures(old(krnl).cpu_arr.spec_index(cpu_id).view(), final(krnl).cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.lock_id_by_index(cpu_id), final(lctx), e.cpu_lock_perm.view())
            &&& wlock_ensures(old(krnl).ctn_mp.spec_index(e.container_ptr), final(krnl).ctn_mp.spec_index(e.container_ptr), old(krnl).ctn_mp.lock_id_by_key(e.container_ptr), final(lctx), e.container_lock_perm.view())
            &&& wlock_ensures(old(krnl).prc_mp.spec_index(e.process_ptr), final(krnl).prc_mp.spec_index(e.process_ptr), old(krnl).prc_mp.lock_id_by_key(e.process_ptr), final(lctx), e.process_lock_perm.view())
            &&& wlock_ensures(old(krnl).thr_mp.spec_index(e.thread_ptr), final(krnl).thr_mp.spec_index(e.thread_ptr), old(krnl).thr_mp.lock_id_by_key(e.thread_ptr), final(lctx), e.thread_lock_perm.view())
            &&& wlock_ensures(old(krnl).it_mp.spec_index(iommu_table), table, old(krnl).it_mp.lock_id_by_key(iommu_table), final(lctx), iommu_table_perm)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view().temp_alloc_clean()
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).view_ghost().exited
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& !final(krnl).ctn_mp.spec_index(e.container_ptr).being_killed() && !final(krnl).ctn_mp.spec_index(e.container_ptr).view().zombie
            &&& !final(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost().owned_processes.view().is_empty()
            &&& !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed() && final(krnl).prc_mp.spec_index(e.process_ptr).view().state.view() is Running
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& final(krnl).cpu_published[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& !final(krnl).prc_mp.spec_index(e.process_ptr).view().zombie
        }),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(iova) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return Err(RetValueType::Error);
    }
    let span = range * 4096usize;
    if iova >= usize::MAX - span || !va_4k_range_valid(iova, range) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return Err(RetValueType::Error);
    }
    let locked = match iommu_unmap_4k_lock_running_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, iova, range) {
        Ok(e) => e,
        Err(r) => { return Err(r); },
    };
    let Tracked(cpu_perm) = locked.cpu_lock_perm;
    let Tracked(container_perm) = locked.container_lock_perm;
    let Tracked(process_perm) = locked.process_lock_perm;
    let Tracked(thread_perm) = locked.thread_lock_perm;
    let (container_ptr, process_ptr, thread_ptr) = (locked.container_ptr, locked.process_ptr, locked.thread_ptr);
    proof { process_perms_wf_map(krnl.prc_mp); }
    let iommu_table_opt = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_perm)).iommu_table;
    proof { process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr); }
    if iommu_table_opt.is_none() {
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorPciNoIommuTable);
        }
        return Err(RetValueType::ErrorPciNoIommuTable);
    }
    let iommu_table = iommu_table_opt.unwrap();
    let Tracked(iommu_table_perm) = krnl.wlock_iommu_table(iommu_table, Tracked(&mut *lctx));
    let iova_range = VaRange4K::new(iova, range);
    proof {
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table);
        assert(iova_range == iommu_unmap_4k_iova_range(iova, range)) by { iova_range.va_range_lemma(); };
    }
    let present = va2index(iova).0 >= krnl.dflt_pt.borrow().kernel_l4_end && {
        let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(&iommu_table_perm));
        it.mapping_4k_va_range_present(&iova_range)
    };
    if !present {
        krnl.wunlock_iommu_table(iommu_table, Tracked(&mut *lctx), Tracked(iommu_table_perm));
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            steps.end_kernel_step_restored_locks_with_iommu_table(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None, Some(iommu_table));
            iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::ErrorIommuIovaNotMapped);
        }
        return Err(RetValueType::ErrorIommuIovaNotMapped);
    }
    proof { iommu_unmap_4k_result_from_k(&*old(krnl), cpu_id, iova, range, RetValueType::Success); }
    Ok((IommuUnmap4kLocked {
        container_ptr, process_ptr, thread_ptr, cpu_lock_perm: Tracked(cpu_perm), container_lock_perm: Tracked(container_perm), process_lock_perm: Tracked(process_perm),
        thread_lock_perm: Tracked(thread_perm),
    }, iommu_table, Tracked(iommu_table_perm)))
}
} // verus!

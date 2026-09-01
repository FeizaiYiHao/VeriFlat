use vstd::prelude::*;
use crate::*;
verus! {

    pub open spec fn kernel_objects_unlocked_except(
        krnl: &KernelK,
        thread_id: LockThreadId,
        cpu_exception: Option<CpuId>,
        scheduler_exception: Option<RwLockSchedulerPtr>,
        process_exception: Option<RwLockProcessPtr>,
        thread_exception: Option<RwLockThreadPtr>,
        endpoint_exception: Option<RwLockEndpointPtr>,
    ) -> bool {
        &&& match cpu_exception {
            Some(c) => cpu_objects_unlocked_except(
                krnl.cpu_arr, thread_id, set![c]),
            None => cpu_objects_unlocked(krnl.cpu_arr, thread_id),
        }
        &&& container_objects_unlocked(krnl.ctn_mp, thread_id)
        &&& match scheduler_exception {
            Some(s) => scheduler_objects_unlocked_except(
                krnl.sched_mp, thread_id, set![s]),
            None => scheduler_objects_unlocked(krnl.sched_mp, thread_id),
        }
        &&& match process_exception {
            Some(p) => process_objects_unlocked_except(
                krnl.prc_mp, thread_id, set![p]),
            None => process_objects_unlocked(krnl.prc_mp, thread_id),
        }
        &&& match thread_exception {
            Some(t) => thread_objects_unlocked_except(
                krnl.thr_mp, thread_id, set![t]),
            None => thread_objects_unlocked(krnl.thr_mp, thread_id),
        }
        &&& page_objects_unlocked(krnl.pg_arr, thread_id)
        &&& match endpoint_exception {
            Some(e) => endpoint_objects_unlocked_except(
                krnl.ep_mp, thread_id, set![e]),
            None => endpoint_objects_unlocked(krnl.ep_mp, thread_id),
        }
        &&& pagetable_objects_unlocked(krnl.pt_mp, thread_id)
        &&& iommu_table_objects_unlocked(krnl.it_mp, thread_id)
        &&& pcid_allocator_objects_unlocked(krnl.pcid_allc_mp, thread_id)
        &&& allocator_objects_unlocked(krnl.allc_4k_mp, thread_id)
        &&& allocator_objects_unlocked(krnl.allc_2m_mp, thread_id)
        &&& allocator_objects_unlocked(krnl.allc_1g_mp, thread_id)
    }

    /// Commit path: allocate 4k page, create thread, release all locks.
    pub fn release_cpu_and_finish_syscall(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            lctx.kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(&lctx),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(lctx).cpu_process_thread_lock_scope(set![cpu_id], Set::<RwLockProcessPtr>::empty(), Set::<RwLockThreadPtr>::empty()),
            kernel_objects_unlocked_except(
                old(krnl), old(lctx).thread_id(), Some(cpu_id),
                None, None, None, None),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            !final(krnl).cpu_arr.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();

        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }

    /// Release process + cpu when the current thread cannot be locked.
    pub fn release_cpu_and_process_and_finish_syscall(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        process_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            lctx.kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(&lctx),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == lctx.thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(&lctx),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            old(lctx).cpu_process_thread_lock_scope(set![cpu_id], set![process_ptr], Set::<RwLockThreadPtr>::empty()),
            kernel_objects_unlocked_except(
                old(krnl), old(lctx).thread_id(), Some(cpu_id),
                None, Some(process_ptr), None, None),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            !final(krnl).cpu_arr.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(krnl).prc_mp.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
    {
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }
    pub fn release_cpu_and_process_and_thread_and_finish_syscall(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        thread_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            !(old(krnl).thr_mp.spec_index(thread_ptr).view().state
                is IPC_ENDPOINT_TRANSIT),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id()
                == old(krnl).cpu_arr.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(krnl).prc_mp.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(lctx).cpu_process_thread_lock_scope(set![cpu_id], set![process_ptr], set![thread_ptr]),
            kernel_objects_unlocked_except(
                old(krnl), old(lctx).thread_id(), Some(cpu_id),
                None, Some(process_ptr), Some(thread_ptr), None),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            !final(krnl).cpu_arr.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(krnl).prc_mp.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            !final(krnl).thr_mp.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
    {
        let tracked thread_lock_perm = thread_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(
            process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
        );
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }

}

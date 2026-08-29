use vstd::prelude::*;
use crate::*;
verus! {

    pub open spec fn kernel_objects_unlocked_except(
        kernel: &KernelK,
        thread_id: LockThreadId,
        cpu_exception: Option<CpuId>,
        scheduler_exception: Option<RwLockSchedulerPtr>,
        process_exception: Option<RwLockProcessPtr>,
        thread_exception: Option<RwLockThreadPtr>,
        endpoint_exception: Option<RwLockEndpointPtr>,
    ) -> bool {
        &&& match cpu_exception {
            Some(c) => cpu_objects_unlocked_except(
                kernel.cpu_array, thread_id, set![c]),
            None => cpu_objects_unlocked(kernel.cpu_array, thread_id),
        }
        &&& container_objects_unlocked(kernel.container_map, thread_id)
        &&& match scheduler_exception {
            Some(s) => scheduler_objects_unlocked_except(
                kernel.scheduler_map, thread_id, set![s]),
            None => scheduler_objects_unlocked(kernel.scheduler_map, thread_id),
        }
        &&& match process_exception {
            Some(p) => process_objects_unlocked_except(
                kernel.process_map, thread_id, set![p]),
            None => process_objects_unlocked(kernel.process_map, thread_id),
        }
        &&& match thread_exception {
            Some(t) => thread_objects_unlocked_except(
                kernel.thread_map, thread_id, set![t]),
            None => thread_objects_unlocked(kernel.thread_map, thread_id),
        }
        &&& page_objects_unlocked(kernel.page_array, thread_id)
        &&& match endpoint_exception {
            Some(e) => endpoint_objects_unlocked_except(
                kernel.endpoint_map, thread_id, set![e]),
            None => endpoint_objects_unlocked(kernel.endpoint_map, thread_id),
        }
        &&& pagetable_objects_unlocked(kernel.pagetable_map, thread_id)
        &&& iommu_table_objects_unlocked(kernel.iommu_table_map, thread_id)
        &&& pcid_allocator_objects_unlocked(kernel.pcid_allocator_map, thread_id)
        &&& allocator_objects_unlocked(kernel.allocator_4k_map, thread_id)
        &&& allocator_objects_unlocked(kernel.allocator_2m_map, thread_id)
        &&& allocator_objects_unlocked(kernel.allocator_1g_map, thread_id)
    }

    /// Commit path: allocate 4k page, create thread, release all locks.
    pub fn release_cpu_and_finish_syscall(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(kernel).inv(),
            lctx.kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            lctx.lock_id_set() =~= set![
                (old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id)),
            ],
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(kernel).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
            old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
            kernel_objects_unlocked_except(
                old(kernel), old(lctx).thread_id(), Some(cpu_id),
                None, None, None, None),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            lock_id_aligned(final(kernel), final(lctx)),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).all_objects_unlocked(final(lctx)),
            final(lctx).lock_id_set() ==
                old(lctx).lock_id_set()
                    .remove((old(kernel).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id))),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();

        kernel.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
            steps.end_kernel_step(&*kernel, &*lctx);
        }
    }

    /// Release process + cpu when the current thread cannot be locked.
    pub fn release_cpu_and_process_and_finish_syscall(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        process_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(kernel).inv(),
            lctx.kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            lctx.lock_id_set() =~= set![
                (old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id)),
                (old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr)),
            ],
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(kernel).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
            old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == lctx.thread_id(),
            process_lock_perm.view().lock_id() == old(kernel).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(kernel).process_map.dom().contains(process_ptr),
            old(kernel).process_map.spec_index(process_ptr).wlocked_by(&lctx),
            old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
            kernel_objects_unlocked_except(
                old(kernel), old(lctx).thread_id(), Some(cpu_id),
                None, Some(process_ptr), None, None),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            lock_id_aligned(final(kernel), final(lctx)),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).all_objects_unlocked(final(lctx)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
    {
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        kernel.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        kernel.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
            steps.end_kernel_step(&*kernel, &*lctx);
        }
    }
    pub fn release_cpu_and_process_and_thread_and_finish_syscall(
        kernel: &mut KernelK,
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
            old(kernel).inv(),
            old(kernel).process_map.dom().contains(process_ptr),
            old(kernel).thread_map.dom().contains(thread_ptr),
            !(old(kernel).thread_map.spec_index(thread_ptr).view().state
                is IPC_ENDPOINT_TRANSIT),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            old(lctx).lock_id_set() =~= set![
                (old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id)),
                (old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr)),
                (old(kernel).thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr)),
            ],
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id()
                == old(kernel).cpu_array.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
            old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(kernel).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(kernel).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(kernel).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            kernel_objects_unlocked_except(
                old(kernel), old(lctx).thread_id(), Some(cpu_id),
                None, Some(process_ptr), Some(thread_ptr), None),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            lock_id_aligned(final(kernel), final(lctx)),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).all_objects_unlocked(final(lctx)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
    {
        let tracked thread_lock_perm = thread_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        kernel.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        kernel.wunlock_process(
            process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
        );
        kernel.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
            steps.end_kernel_step(&*kernel, &*lctx);
        }
    }

}

use vstd::prelude::*;
use vstd::calc;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use crate::*;
verus! {

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
            lock_id_aligned(old(kernel), old(lctx)),
            typed_lock_sets_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            lock_id_aligned(final(kernel), final(lctx)),
            typed_lock_sets_aligned(final(kernel), final(lctx)),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            typed_lock_sets_removed(
                old(lctx), final(lctx), KernelObjId::Cpu(cpu_id)),
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
            lock_id_aligned(old(kernel), old(lctx)),
            typed_lock_sets_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            lock_id_aligned(final(kernel), final(lctx)),
            typed_lock_sets_aligned(final(kernel), final(lctx)),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(lctx).page_lock_set() == old(lctx).page_lock_set(),
            final(lctx).cpu_lock_set() == old(lctx).cpu_lock_set().remove(cpu_id),
            final(lctx).container_lock_set() == old(lctx).container_lock_set(),
            final(lctx).process_lock_set()
                == old(lctx).process_lock_set().remove(process_ptr),
            final(lctx).thread_lock_set() == old(lctx).thread_lock_set(),
            final(lctx).endpoint_lock_set() == old(lctx).endpoint_lock_set(),
            final(lctx).scheduler_lock_set() == old(lctx).scheduler_lock_set(),
            final(lctx).pcid_allocator_lock_set()
                == old(lctx).pcid_allocator_lock_set(),
            final(lctx).pagetable_lock_set() == old(lctx).pagetable_lock_set(),
            final(lctx).iommu_table_lock_set() == old(lctx).iommu_table_lock_set(),
            final(lctx).allocator_quota_lock_set()
                == old(lctx).allocator_quota_lock_set(),
            final(lctx).allocator_cache_lock_set()
                == old(lctx).allocator_cache_lock_set(),
            final(lctx).allocator_global_pool_lock_set()
                == old(lctx).allocator_global_pool_lock_set(),
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
            lock_id_aligned(old(kernel), old(lctx)),
            typed_lock_sets_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            lock_id_aligned(final(kernel), final(lctx)),
            typed_lock_sets_aligned(final(kernel), final(lctx)),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(lctx).page_lock_set() == old(lctx).page_lock_set(),
            final(lctx).cpu_lock_set() == old(lctx).cpu_lock_set().remove(cpu_id),
            final(lctx).process_lock_set()
                == old(lctx).process_lock_set().remove(process_ptr),
            final(lctx).thread_lock_set()
                == old(lctx).thread_lock_set().remove(thread_ptr),
            final(lctx).container_lock_set() == old(lctx).container_lock_set(),
            final(lctx).endpoint_lock_set() == old(lctx).endpoint_lock_set(),
            final(lctx).scheduler_lock_set() == old(lctx).scheduler_lock_set(),
            final(lctx).pcid_allocator_lock_set()
                == old(lctx).pcid_allocator_lock_set(),
            final(lctx).pagetable_lock_set() == old(lctx).pagetable_lock_set(),
            final(lctx).iommu_table_lock_set() == old(lctx).iommu_table_lock_set(),
            final(lctx).allocator_quota_lock_set()
                == old(lctx).allocator_quota_lock_set(),
            final(lctx).allocator_cache_lock_set()
                == old(lctx).allocator_cache_lock_set(),
            final(lctx).allocator_global_pool_lock_set()
                == old(lctx).allocator_global_pool_lock_set(),
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

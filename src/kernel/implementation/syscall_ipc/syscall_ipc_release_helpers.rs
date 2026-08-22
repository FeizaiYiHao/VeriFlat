use vstd::prelude::*;
use vstd::calc;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use crate::*;
verus! {

    // TODO(AGENTS): Replace the legacy range/tree assert-forall bridges in this
    // module with direct producer postconditions or narrow fold lemmas.

    #[verifier::opaque]
    pub open spec fn new_thread_other_objects_unlocked(
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

    impl KernelK {
        /// Commit path: allocate 4k page, create thread, release all locks.
        pub fn release_cpu_and_finish(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            cpu_lock_perm: Tracked<LockPerm>,
        )
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                lctx.lock_id_set() =~= set![
                    (old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id)),
                ],
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                new_thread_other_objects_unlocked(
                    old(self), old(lctx).thread_id(), Some(cpu_id),
                    None, None, None, None),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).kernel_view_locking_state() is Release,
                lock_id_aligned(final(self), final(lctx)),
                !final(self).cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(final(lctx).thread_id()),
                final(self).all_objects_unlocked(final(lctx)),
                final(lctx).lock_id_set() ==
                    old(lctx).lock_id_set()
                        .remove((old(self).cpu_array.lock_id_by_index(cpu_id),
                            KernelObjId::Cpu(cpu_id))),
                final(steps).steps == old(steps).steps,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
        {
            let tracked cpu_lock_perm = cpu_lock_perm.get();

            proof {
                assert(
                    cpu_objects_unlocked_except(
                        self.cpu_array, lctx.thread_id(), set![cpu_id])
                ) by {
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                assert(self.all_objects_unlocked(&*lctx)) by {
                    reveal(new_thread_other_objects_unlocked);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
                steps.end_kernel_step(&*self, &*lctx);
            }
        }

        /// Release process + cpu when the current thread cannot be locked.
        pub fn release_cpu_and_process_and_finish(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            process_ptr: RwLockProcessPtr,
            process_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
        )
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                lctx.lock_id_set() =~= set![
                    (old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id)),
                    (old(self).process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr)),
                ],
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == lctx.thread_id(),
                process_lock_perm.view().lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                new_thread_other_objects_unlocked(
                    old(self), old(lctx).thread_id(), Some(cpu_id),
                    None, Some(process_ptr), None, None),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).kernel_view_locking_state() is Release,
                lock_id_aligned(final(self), final(lctx)),
                !final(self).cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(final(lctx).thread_id()),
                !final(self).process_map.spec_index(process_ptr)
                    .locked_by_thread(final(lctx).thread_id()),
                final(self).all_objects_unlocked(final(lctx)),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                final(steps).steps == old(steps).steps,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
        {
            let tracked process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            proof {
                assert(
                    cpu_objects_unlocked_except(
                        self.cpu_array, lctx.thread_id(), set![cpu_id])
                    && process_objects_unlocked_except(
                        self.process_map, lctx.thread_id(), set![process_ptr])
                ) by {
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                assert(self.all_objects_unlocked(&*lctx)) by {
                    reveal(new_thread_other_objects_unlocked);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
                steps.end_kernel_step(&*self, &*lctx);
            }
        }
        pub fn release_cpu_and_process_and_thread_and_finish(
            &mut self,
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
                old(self).inv(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).thread_map.dom().contains(thread_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                old(lctx).lock_id_set() =~= set![
                    (old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id)),
                    (old(self).process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr)),
                    (old(self).thread_map.lock_id_by_key(thread_ptr),
                        KernelObjId::Thread(thread_ptr)),
                ],
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
                cpu_lock_perm.view().lock_id()
                    == old(self).cpu_array.spec_index(cpu_id).view()
                        .locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == old(lctx).thread_id(),
                process_lock_perm.view().lock_id()
                    == old(self).process_map.spec_index(process_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                thread_lock_perm.view().state() is WriteLock,
                thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
                thread_lock_perm.view().lock_id()
                    == old(self).thread_map.spec_index(thread_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
                old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
                old(self).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
                old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                new_thread_other_objects_unlocked(
                    old(self), old(lctx).thread_id(), Some(cpu_id),
                    None, Some(process_ptr), Some(thread_ptr), None),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).kernel_view_locking_state() is Release,
                lock_id_aligned(final(self), final(lctx)),
                !final(self).cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(final(lctx).thread_id()),
                !final(self).process_map.spec_index(process_ptr)
                    .locked_by_thread(final(lctx).thread_id()),
                !final(self).thread_map.spec_index(thread_ptr)
                    .locked_by_thread(final(lctx).thread_id()),
                final(self).all_objects_unlocked(final(lctx)),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                final(steps).steps == old(steps).steps,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
        {
            let tracked thread_lock_perm = thread_lock_perm.get();
            let tracked process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            proof {
                assert(
                    cpu_objects_unlocked_except(
                        self.cpu_array, lctx.thread_id(), set![cpu_id])
                    && process_objects_unlocked_except(
                        self.process_map, lctx.thread_id(), set![process_ptr])
                    && thread_objects_unlocked_except(
                        self.thread_map, lctx.thread_id(), set![thread_ptr])
                ) by {
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            self.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
            self.wunlock_process(
                process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
            );
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(self.all_objects_unlocked(&*lctx)) by {
                    reveal(new_thread_other_objects_unlocked);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
                steps.end_kernel_step(&*self, &*lctx);
            }
        }

    }
}

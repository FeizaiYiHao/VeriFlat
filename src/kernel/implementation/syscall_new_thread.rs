use vstd::prelude::*;
use vstd::calc;
use crate::*;
verus! {
    impl KernelK {
        /// syscall_new_thread: create a new thread in the running process on
        /// `cpu_id`. Lock order: cpu -> scheduler -> process.
        #[verifier::spinoff_prover]
        pub fn syscall_new_thread(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
        ) -> (ret: RetValueType)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(lctx).lock_id_set() =~= Set::<LockId>::empty(),
                old(self).cpu_array[cpu_id]@.locked_by(old(lctx)) == false,
                {
                    let process_ptr =
                        old(self).cpu_array[cpu_id]@@.current_process->Some_0;
                    let container_ptr =
                        old(self).process_map.spec_index(process_ptr)
                            .view_rodata().view().owning_container;
                    let scheduler_ptr =
                        old(self).container_map.spec_index(container_ptr)
                            .view_rodata().view().scheduler;
                    &&& old(self).process_map.spec_index(process_ptr)
                        .locked_by(old(lctx)) == false
                    &&& old(self).scheduler_map.spec_index(scheduler_ptr)
                        .locked_by(old(lctx)) == false
                },
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                old(self).locked_objects_match_lctx(old(lctx)),
                old(lctx).wf(),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(steps).steps.len() == 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).wf(),
                final(lctx).lock_id_set() =~= Set::<LockId>::empty(),
                // Error paths are user-view no-ops.
                !(ret is Success) ==> final(steps).steps.last().old_u == final(steps).steps.last().new_u,
                ret is Success ==> {
                    let process_ptr = old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& kernel_u_new_thread_changed(
                            final(steps).steps.last().old_u,
                            final(steps).steps.last().new_u,
                            process_ptr,
                        )
                },
                ret is Success
                    || ret is ErrorProcessKilled
                    || ret is ErrorNoQuota,
        {
            proof {
                assert(
                    self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                ) by {
                    reveal(cpu_array_wf);
                    reveal(process_cpu_wf);
                };
            }
            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut *lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();

            proof {
                assert(self.process_map.dom().contains(process_ptr)) by {
                    reveal(process_cpu_wf);
                };
                assert(self.process_map.perms_wf()) by {
                    reveal(process_perms_wf);
                };
            }
            let proc_container = self.process_map.borrow_rodata(process_ptr).borrow().owning_container;
            proof {
                assert(self.container_map.dom().contains(proc_container)) by {
                    reveal(container_process_wf);
                };
                assert(self.container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
            }
            let scheduler_ptr = self.container_map.borrow_rodata(proc_container).borrow().scheduler;

            proof {
                assert(self.scheduler_map.dom().contains(scheduler_ptr)) by { reveal(container_scheduler_wf); }
                let sched_lock_id = self.scheduler_map.lock_id_by_key(scheduler_ptr);
                assert(sched_lock_id.major == SCHEDULER_LOCK_MAJOR) by {
                    reveal(scheduler_perms_wf);
                };
                assert(sched_lock_id.spec_gt(self.cpu_array.lock_id_by_index(cpu_id))) by {
                    reveal(cpu_locked_match_lctx);
                };
                assert(lctx.lock_id_acyclic(sched_lock_id)) by {
                    reveal(LocalContext::lock_id_acyclic);
                };
            }
            proof {
                let process_lock_id = self.process_map.lock_id_by_key(process_ptr);
                assert(process_lock_id.spec_gt(self.cpu_array.lock_id_by_index(cpu_id))) by {
                    reveal(container_cpu_wf);
                    reveal(process_cpu_wf);
                    reveal(container_process_wf);
                    reveal(cpu_locked_match_lctx);
                };
                assert(lctx.lock_id_acyclic(process_lock_id)) by {
                    reveal(LocalContext::lock_id_acyclic);
                };
            }
            let Tracked(scheduler_lock_perm) = self.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));
            proof {
                let process_lock_id = self.process_map.lock_id_by_key(process_ptr);
                assert(process_lock_id.major == PROCESS_LOCK_MAJOR) by {
                    reveal(process_perms_wf);
                };
                assert(
                    {
                        &&& self.process_map.dom().contains(process_ptr)
                        &&& self.process_map.spec_index(process_ptr).locked_by(&*lctx) == false
                    }
                ) by {
                    reveal(process_cpu_wf);
                };
                assert(process_lock_id.spec_gt(self.scheduler_map.lock_id_by_key(scheduler_ptr))) by {
                    reveal(scheduler_locked_match_lctx);
                };
                assert(lctx.lock_id_acyclic(process_lock_id)) by {
                    reveal(LocalContext::lock_id_acyclic);
                };
            }
            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(&mut *lctx));
            if let (false, _) = process_res {
                self.release_cpu_and_finish(
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    scheduler_ptr,
                    Tracked(cpu_lock_perm),
                    Tracked(scheduler_lock_perm),
                );
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();

            let process_ref = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            if process_ref.quota_4k < 1 {
                self.release_cpu_and_process_and_finish(
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    scheduler_ptr,
                    process_ptr,
                    Tracked(process_lock_perm),
                    Tracked(cpu_lock_perm),
                    Tracked(scheduler_lock_perm),
                );
                return RetValueType::ErrorNoQuota;
            }

            // ===== QUOTA SUFFICIENT =====
            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            }
            self.add_new_thread_to_proc_container_and_scheduler(
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                cpu_id,
                process_ptr,
                proc_container,
                scheduler_ptr,
                Tracked(process_lock_perm),
                Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm),
            );
            return RetValueType::Success;
        }

        /// Commit path: allocate 4k page, create thread, release all locks.
        #[verifier::spinoff_prover]
        fn add_new_thread_to_proc_container_and_scheduler(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            process_ptr: RwLockProcessPtr,
            container_ptr: RwLockContainerPtr,
            scheduler_ptr: RwLockSchedulerPtr,
            process_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
            scheduler_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).process_map.dom().contains(process_ptr),
                old(self).container_map.dom().contains(container_ptr),
                lctx.lock_id_set() =~= set![
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                    old(self).process_map.lock_id_by_key(process_ptr),
                ],
                lctx.wf(),
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                scheduler_lock_perm@.state() is WriteLock,
                scheduler_lock_perm@.thread_id() == lctx.thread_id(),
                scheduler_lock_perm@.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(self).container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                old(self).process_map.spec_index(process_ptr).view().quota_4k >= 1,
                old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                old(self).cpu_array.lock_id_by_index(cpu_id).major == CPU_LOCK_MAJOR_RUNNING,
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr).major == SCHEDULER_LOCK_MAJOR,
                old(self).process_map.lock_id_by_key(process_ptr).major == PROCESS_LOCK_MAJOR,
                old(self).locked_objects_match_lctx(&lctx),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).wf(),
                final(lctx).lock_id_set() =~= Set::<LockId>::empty(),
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // Full U-change.
                kernel_u_new_thread_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                ),
        {
            let tracked mut process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();

            proof {
                assert(self.container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
            }
            let alloc_ptr_4k = self.container_map.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;

            proof {
                assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                    reveal(container_allocator_wf);
                };
                assert forall|held_lock_id: LockId|
                    #![trigger lctx.lock_id_set().contains(held_lock_id)]
                    lctx.lock_id_set().contains(held_lock_id)
                    implies held_lock_id.major <= PROCESS_LOCK_MAJOR by {
                    reveal(cpu_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                };
                assert(lctx.lock_id_acyclic(
                    self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[cpu_id].lock_id()
                )) by {
                    reveal(LocalContext::lock_id_acyclic);
                    reveal(allocator_perms_wf);
                    reveal(LockId::spec_gt);
                    reveal(LockOwnerId::spec_eq);
                    reveal(LockOwnerId::spec_gt);
                };
            }

            let (page_ptr, Tracked(page_lock_perm)) = self.allocate_free_4k_page(
                alloc_ptr_4k, process_ptr, container_ptr, cpu_id, scheduler_ptr,
                Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&process_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);

            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }

            let (thread_ptr, Tracked(thread_lock_perm)) = self.create_thread_from_staged_page_merged(
                page_ptr, process_ptr, container_ptr, scheduler_ptr,
                Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(&process_lock_perm), Tracked(&scheduler_lock_perm),
            );

            self.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
            self.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            proof {
                assert(lctx.lock_id_set() =~= set![
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                    old(self).process_map.lock_id_by_key(process_ptr),
                ]) by {
                    reveal(thread_perms_wf);
                    reveal(page_array_wf);
                };
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }
            self.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            assert(lctx.lock_id_set() =~= set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).process_map.lock_id_by_key(process_ptr),
            ]) by {
                reveal(scheduler_perms_wf);
            };
            assert(self.process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr)) by {
                reveal(process_perms_wf);
            };
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            assert(lctx.lock_id_set() =~= set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
            ]) by {
                reveal(process_perms_wf);
            };
            assert(
                self.cpu_array[cpu_id]@.wlocked_by(&*lctx)
                && cpu_lock_perm.lock_id()
                    == self.cpu_array[cpu_id]@
                        .locking_thread()->Write_lock_id
            ) by {
                reveal(cpu_array_wf);
            };
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                assert(lctx.lock_id_set() =~= Set::<LockId>::empty()) by {
                    reveal(cpu_array_wf);
                };
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
                assert(kernel_u_new_thread_changed(
                    steps.steps.last().old_u,
                    steps.steps.last().new_u,
                    process_ptr,
                )) by {
                    reveal(kernel_u_new_thread_changed);
                    reveal(kernel_k_to_kernel_u);
                    assert(
                        steps.steps.last().new_u.cpu_array
                            =~= steps.steps.last().old_u.cpu_array
                    ) by {
                        assert forall|i: int|
                            0 <= i < NUM_CPUS
                            implies steps.steps.last().new_u.cpu_array[i]
                                == steps.steps.last().old_u.cpu_array[i] by {
                            reveal(kernel_k_to_kernel_u);
                        };
                    };
                    assert forall|p: RwLockProcessPtr|
                        #![trigger steps.steps.last().new_u.process_map[p]]
                        steps.steps.last().old_u.process_map.dom().contains(p)
                            && p != process_ptr
                        implies steps.steps.last().new_u.process_map[p]
                            == steps.steps.last().old_u.process_map[p] by {
                        reveal(kernel_k_to_kernel_u);
                        reveal(KernelK::get_process_pagetable);
                        assert(
                            steps.steps.last().new_u.process_map[p].pagetable
                                == steps.steps.last().old_u.process_map[p].pagetable
                        ) by {
                            reveal(kernel_k_to_kernel_u);
                            reveal(KernelK::get_process_pagetable);
                        };
                    };
                };
            }
        }

        /// Release scheduler + cpu on the process-killed path.
        #[verifier::spinoff_prover]
        fn release_cpu_and_finish(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            scheduler_ptr: RwLockSchedulerPtr,
            cpu_lock_perm: Tracked<LockPerm>,
            scheduler_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                lctx.lock_id_set() =~= set![
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                ],
                lctx.wf(),
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array[cpu_id]@.wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                scheduler_lock_perm.view().state() is WriteLock,
                scheduler_lock_perm.view().thread_id() == lctx.thread_id(),
                scheduler_lock_perm.view().lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(self).locked_objects_match_lctx(&lctx),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).lock_id_set() =~=
                    old(lctx).lock_id_set()
                        .remove(old(self).cpu_array.lock_id_by_index(cpu_id))
                        .remove(old(self).scheduler_map.lock_id_by_key(scheduler_ptr)),
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();

            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }

            self.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }
        }

        /// Release scheduler + process + cpu on the no-quota path.
        #[verifier::spinoff_prover]
        fn release_cpu_and_process_and_finish(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            scheduler_ptr: RwLockSchedulerPtr,
            process_ptr: RwLockProcessPtr,
            process_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
            scheduler_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                lctx.lock_id_set() =~= set![
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                    old(self).process_map.lock_id_by_key(process_ptr),
                ],
                lctx.wf(),
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array[cpu_id]@.wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                scheduler_lock_perm@.state() is WriteLock,
                scheduler_lock_perm@.thread_id() == lctx.thread_id(),
                scheduler_lock_perm@.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                old(self).locked_objects_match_lctx(&lctx),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).lock_id_set() =~=
                    old(lctx).lock_id_set()
                        .remove(old(self).cpu_array.lock_id_by_index(cpu_id))
                        .remove(old(self).scheduler_map.lock_id_by_key(scheduler_ptr))
                        .remove(old(self).process_map.lock_id_by_key(process_ptr)),
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();
            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }

            self.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }
        }

        /// Create a thread from a staged 4k page: retype, wire into
        /// scheduler/process/container, re-establish inv().
        pub fn create_thread_from_staged_page(
            &mut self,
            page_ptr: PagePtr,
            process_ptr: RwLockProcessPtr,
            container_ptr: RwLockContainerPtr,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(page_lock_perm): Tracked<&LockPerm>,
            Tracked(process_lock_perm): Tracked<&LockPerm>,
            Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
        ) -> (ret: (RwLockThreadPtr, Tracked<LockPerm>))
            requires
                old(self).inv(),
                page_ptr_valid(page_ptr),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                forall|i: int| #![auto] 0 <= i < old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view().len()
                    ==> old(self).container_map.dom().contains(old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view()[i]),
                old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view().no_duplicates(),
                !old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view().contains(container_ptr),
                old(self).process_map.spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX,
                old(self).scheduler_map.spec_index(scheduler_ptr).view().queue.view().len() < usize::MAX,
                old(self).thread_map.dom().contains(page_ptr) == false,
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == old(lctx).thread_id(),
                process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                scheduler_lock_perm.state() is WriteLock,
                scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
                scheduler_lock_perm.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= Set::<PagePtr>::empty().insert(page_ptr),
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m.view().len() == 0,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g.view().len() == 0,
                old(self).process_map.spec_index(process_ptr).view().quota_4k >= 1,
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(old(lctx)),
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Owned4k{ process_ptr }),
                page_lock_perm.state() is WriteLock,
                page_lock_perm.thread_id() == old(lctx).thread_id(),
                page_lock_perm.lock_id() == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                final(self).inv(),
                ret.0 == page_ptr,
                final(self).thread_map.dom().contains(page_ptr),
                final(self).thread_map.spec_index(page_ptr).wlocked_by(final(lctx)),
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(self).thread_map.spec_index(page_ptr).locking_thread()->Write_lock_id,
                final(self).thread_map.spec_index(page_ptr).view().free_quota_pending_clean(),
                final(self).thread_map.spec_index(page_ptr).being_killed() == false,
                final(self).process_map.dom().contains(process_ptr),
                final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(self).process_map.spec_index(process_ptr).being_killed() == false,
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                final(self).process_map.lock_id_by_key(process_ptr)
                    == old(self).process_map.lock_id_by_key(process_ptr),
                kernel_u_new_thread_changed(
                    kernel_k_to_kernel_u(*old(self)),
                    kernel_k_to_kernel_u(*final(self)),
                    process_ptr,
                ),
                process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                final(self).scheduler_map.dom().contains(scheduler_ptr),
                final(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
                final(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                scheduler_lock_perm.lock_id() == final(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(final(lctx)),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                page_lock_perm.lock_id() == final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                final(self).locked_objects_match_lctx(final(lctx)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                final(self).pagetable_map == old(self).pagetable_map,
                final(self).process_map.unchanged_except(
                    &old(self).process_map, process_ptr),
                final(self).cpu_array == old(self).cpu_array,
                final(self).page_array.unchanged_except(
                    &old(self).page_array, page_ptr2page_index(page_ptr)),
                final(lctx).wf(),
                final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                    final(self).thread_map.lock_id_by_key(page_ptr)),
        {
            proof {
                assert(old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view().len()
                    == old(self).container_map.spec_index(container_ptr).view_rodata().view().depth) by {
                    reveal(container_perms_wf);
                    reveal(container_tree_fields_wf);
                };
                assert(page_array_wf(self.page_array)) by {
                    reveal(page_array_wf);
                };
                assert(self.page_array.inv()) by {
                    reveal(page_array_wf);
                };
                assert(self.page_array.spec_index(page_ptr2page_index(page_ptr)).view().inv()) by {
                    reveal(page_array_wf);
                };
                assert(self.container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
                assert(self.process_map.perms_wf()) by {
                    reveal(process_perms_wf);
                };
                assert(self.thread_map.perms_wf()) by {
                    reveal(thread_perms_wf);
                };
            }
            let Tracked(thread_perm) = self.retype_staged_page_to_thread(
                page_ptr, process_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(page_lock_perm), Tracked(process_lock_perm),
            );

            proof {
                assert(self.container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
                add_thread_to_container_sets(
                    &mut self.container_map, container_ptr, page_ptr,
                    old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view(),
                );
            }

            proof {
                assert(old(self).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) == false) by {
                    reveal(process_thread_wf);
                    if old(self).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) {
                        assert(old(self).thread_map.spec_index(page_ptr).view().owning_proc == process_ptr) by {
                            reveal(process_thread_wf);
                        };
                    }
                }
            }
            let thread_mut = self.thread_map.borrow_mut(page_ptr, Tracked(&*lctx), Tracked(&thread_perm));
            let (node_addr, mut node_perm) = thread_mut.proc_linkedlist_node.take();
            node_update_value(node_addr, &mut node_perm, page_ptr);
            let process_mut = self.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
            proof {
                assert(
                    process_mut.owned_threads.wf()
                    && process_mut.owned_threads.length != usize::MAX
                ) by {
                    reveal(process_perms_wf);
                    reveal(LinkedList::wf_value_list);
                };
            }
            process_mut.owned_threads.push_tail(node_addr, node_perm);

            let (sched_node_addr, mut sched_node_perm) = thread_mut.scheduler_linkedlist_node.take();
            node_update_value(sched_node_addr, &mut sched_node_perm, page_ptr);
            proof {
                assert(
                    self.scheduler_map.perms_wf()
                    && self.scheduler_map.spec_index(scheduler_ptr).is_init()
                ) by {
                    reveal(scheduler_perms_wf);
                };
            }
            let scheduler_mut = self.scheduler_map.borrow_mut(scheduler_ptr, Tracked(&*lctx), Tracked(scheduler_lock_perm));
            proof {
                assert(
                    scheduler_mut.queue.wf()
                    && scheduler_mut.queue.length != usize::MAX
                ) by {
                    reveal(scheduler_perms_wf);
                    reveal(LinkedList::wf_value_list);
                };
                assert(!scheduler_mut.queue.view().contains(page_ptr)) by {
                    reveal(container_thread_scheduler_wf);
                };
            }
            scheduler_mut.queue.push_tail(sched_node_addr, sched_node_perm);
            thread_mut.state = ThreadState::SCHEDULED;

            proof {
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    reveal(cpu_array_wf);
                    reveal(container_perms_wf);
                    reveal(container_tree_fields_wf);
                    reveal(process_perms_wf);
                    reveal(process_temp_alloc_empty_unless_wlocked);
                    reveal(allocator_perms_wf);
                    reveal(thread_perms_wf);
                    reveal(threads_inv);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    reveal(page_array_wf);
                    reveal(scheduler_perms_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                        allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                        allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_uppertree_seq_wf);
                        container_process_allocator_quota_wf_preserved_on_thread_add(
                            *old(self), *self, container_ptr, page_ptr,
                            old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view(),
                        );
                    };
                    assert(container_allocator_wf(
                        self.container_map,
                        self.allocator_4k_map,
                        self.allocator_2m_map,
                        self.allocator_1g_map,
                    )) by {
                        reveal(container_allocator_wf);
                    };
                    assert(self.allocator_free_pages_wf()) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                        reveal(process_pagetable_match);
                    };
                    assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                    assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                        reveal(page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                        reveal(pagetable_perms_wf); reveal(pagetables_inv); page_ptr_lemma1();
                    };
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by {
                        reveal(pagetable_pages_wf);
                    };
                    assert(thread_pages_wf(self.thread_map, self.page_array)) by {
                        reveal(thread_pages_wf);
                    };
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_4k_wf);
                        process_staged_pages_2m_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                        process_staged_pages_1g_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                    };
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf);
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                        page_ptr_lemma1();
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf);
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                        page_ptr_lemma1();
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf);
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                        page_ptr_lemma1();
                    };
                };
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map)) by {
                        container_no_change_to_tree_fields_imply_wf(self.root_container, old(self).container_map, self.container_map);
                    };
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(per_container_process_tree_wf); reveal(container_process_wf);
                        per_container_process_tree_wf_preserved_for_tree_fields_eq(self.container_map, old(self).process_map, self.process_map);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by {
                        reveal(thread_endpoint_ref_counter_wf);
                    };
                    assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by {
                        reveal(thread_endpoint_queue_wf);
                    };
                    assert(container_thread_endpoint_wf(
                        self.container_map,
                        self.thread_map,
                        self.endpoint_map,
                    )) by {
                        reveal(container_endpoint_wf);
                        reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf);
                        reveal(container_thread_endpoint_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_scheduler_wf);
                        reveal(container_thread_wf);
                        reveal(container_scheduler_wf);
                        assert(
                            old(self).scheduler_map.spec_index(scheduler_ptr).view().queue.wf()
                        ) by {
                            reveal(scheduler_perms_wf);
                        };
                        seq_push_lemma::<RwLockThreadPtr>();
                    };
                    assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by {
                        reveal(thread_cpu_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        container_thread_wf_preserved_on_thread_add(
                            old(self).container_map, self.container_map, old(self).thread_map, self.thread_map,
                            container_ptr, page_ptr,
                            old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view(),
                        );
                    };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by {
                        assert(
                            old(self).process_map.spec_index(process_ptr).view().owned_threads.wf()
                        ) by {
                            reveal(process_perms_wf);
                        };
                        process_thread_wf_preserved_on_thread_add(
                            old(self).process_map,
                            self.process_map,
                            old(self).thread_map,
                            self.thread_map,
                            process_ptr,
                            page_ptr,
                            node_addr,
                        );
                    };
                };
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                };
                assert(self.inv()) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                    reveal(tlb_wf_spec);
                };
            }
            proof {
                let pre_u = kernel_k_to_kernel_u(*old(self));
                let post_u = kernel_k_to_kernel_u(*self);
                assert(kernel_u_new_thread_changed(pre_u, post_u, process_ptr)) by {
                    reveal(kernel_u_new_thread_changed);
                    reveal(kernel_k_to_kernel_u);
                    assert(post_u.process_map[process_ptr].owned_threads.subrange(
                        0, pre_u.process_map[process_ptr].owned_threads.len() as int)
                        == pre_u.process_map[process_ptr].owned_threads) by {
                        reveal(kernel_k_to_kernel_u);
                    };
                };
            }
            (page_ptr, Tracked(thread_perm))
        }

        /// Merged version: retype + wiring + inv rebuild in one function.
        /// Eliminates retype's ~100-line intermediate ensures.
        #[verifier::spinoff_prover]
        pub fn create_thread_from_staged_page_merged(
            &mut self,
            page_ptr: PagePtr,
            process_ptr: RwLockProcessPtr,
            container_ptr: RwLockContainerPtr,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(page_lock_perm): Tracked<&LockPerm>,
            Tracked(process_lock_perm): Tracked<&LockPerm>,
            Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
        ) -> (ret: (RwLockThreadPtr, Tracked<LockPerm>))
            requires
                old(self).inv(),
                page_ptr_valid(page_ptr),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                old(self).container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == old(lctx).thread_id(),
                process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
                scheduler_lock_perm.state() is WriteLock,
                scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
                scheduler_lock_perm.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= Set::<PagePtr>::empty().insert(page_ptr),
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m.view().len() == 0,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g.view().len() == 0,
                old(self).process_map.spec_index(process_ptr).view().quota_4k >= 1,
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Owned4k{ process_ptr }),
                page_lock_perm.state() is WriteLock,
                page_lock_perm.thread_id() == old(lctx).thread_id(),
                page_lock_perm.lock_id() == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                old(self).page_array[page_ptr2page_index(page_ptr)]@
                    .wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Release,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                ret.0 == page_ptr,
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(self).thread_map.spec_index(page_ptr).locking_thread()->Write_lock_id,
                final(self).thread_map.dom().contains(page_ptr),
                final(self).thread_map.spec_index(page_ptr).wlocked_by(final(lctx)),
                final(self).thread_map.spec_index(page_ptr).view().free_quota_pending_clean(),
                final(self).thread_map.spec_index(page_ptr).being_killed() == false,
                final(self).process_map.dom().contains(process_ptr),
                final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(self).process_map.spec_index(process_ptr).being_killed() == false,
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                final(self).process_map.lock_id_by_key(process_ptr)
                    == old(self).process_map.lock_id_by_key(process_ptr),
                kernel_u_new_thread_changed(
                    kernel_k_to_kernel_u(*old(self)),
                    kernel_k_to_kernel_u(*final(self)),
                    process_ptr,
                ),
                process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                final(self).scheduler_map.dom().contains(scheduler_ptr),
                final(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
                final(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                scheduler_lock_perm.lock_id() == final(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                final(self).page_array[page_ptr2page_index(page_ptr)]@
                    .wlocked_by(final(lctx)),
                page_lock_perm.lock_id() == final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                final(self).pagetable_map == old(self).pagetable_map,
                final(self).process_map.unchanged_except(
                    &old(self).process_map, process_ptr),
                final(self).cpu_array == old(self).cpu_array,
                final(self).page_array.unchanged_except(
                    &old(self).page_array, page_ptr2page_index(page_ptr)),
                final(lctx).wf(),
                final(lctx).lock_id_set() =~=
                    old(lctx).lock_id_set()
                        .insert(final(self).thread_map.lock_id_by_key(page_ptr))
                        .remove(old(self).page_array.lock_id_by_index(
                            page_ptr2page_index(page_ptr)))
                        .insert(final(self).page_array.lock_id_by_index(
                            page_ptr2page_index(page_ptr))),
        {
            proof {
                assert(
                    self.process_map.perms_wf()
                    && self.process_map.dom().contains(process_ptr)
                    && self.process_map.spec_index(process_ptr).is_init()
                    && self.process_map.spec_index(process_ptr).wlocked_by(&*lctx)
                ) by {
                    reveal(process_perms_wf);
                    reveal(process_locked_match_lctx);
                };
                assert(
                    self.container_map.perms_wf()
                    && self.container_map.dom().contains(container_ptr)
                ) by {
                    reveal(container_perms_wf);
                    reveal(container_process_wf);
                };
                assert(container_perms_wf(self.container_map)) by {
                    reveal(KernelK::inv);
                    reveal(KernelK::subsystems_inv);
                };
                assert(container_tree_wf(
                    self.root_container,
                    self.container_map,
                )) by {
                    reveal(KernelK::inv);
                    reveal(KernelK::process_management_inv);
                };
                assert(container_tree_fields_wf(self.container_map)) by {
                    reveal(container_perms_wf);
                };
                assert(
                    self.scheduler_map.perms_wf()
                    && self.scheduler_map.dom().contains(scheduler_ptr)
                    && self.scheduler_map.spec_index(scheduler_ptr).is_init()
                    && self.scheduler_map.spec_index(scheduler_ptr).wlocked_by(&*lctx)
                ) by {
                    reveal(scheduler_perms_wf);
                    reveal(scheduler_locked_match_lctx);
                };
                assert(
                    self.thread_map.perms_wf()
                    && !self.thread_map.dom().contains(page_ptr)
                    && lctx.obj_id_fresh(KernelObjId::Thread(page_ptr))
                ) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(thread_perms_wf);
                    reveal(thread_pages_wf);
                    reveal(thread_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert forall|i: int|
                    #![auto]
                    0 <= i < self.container_map.spec_index(
                        container_ptr
                    ).view().uppertree_seq.view().len()
                    ==> self.container_map.dom().contains(
                        self.container_map.spec_index(
                            container_ptr
                        ).view().uppertree_seq.view()[i]
                    ) by {
                    reveal(container_tree_fields_wf);
                    reveal(container_uppertree_seq_wf);
                    reveal(container_tree_wf);
                    if 0 <= i < self.container_map.spec_index(
                        container_ptr
                    ).view().uppertree_seq.view().len() {
                        self.container_map.spec_index(
                            container_ptr
                        ).view().uppertree_seq.view().lemma_index_contains(i);
                    }
                };
                assert(
                    self.container_map.spec_index(
                        container_ptr
                    ).view().uppertree_seq.view().no_duplicates()
                    && !self.container_map.spec_index(
                        container_ptr
                    ).view().uppertree_seq.view().contains(container_ptr)
                ) by {
                    reveal(container_uppertree_seq_wf);
                    reveal(container_tree_wf);
                    reveal(container_tree_fields_wf);
                };
                assert(
                    self.process_map.spec_index(
                        process_ptr
                    ).view().owned_threads.view().len() < usize::MAX
                ) by {
                    let threads = self.process_map.spec_index(
                        process_ptr
                    ).view().owned_threads.view();
                    assert(threads.no_duplicates()) by {
                        reveal(process_perms_wf);
                        reveal(LinkedList::wf_value_list);
                        reveal(LinkedList::value_list_unique);
                    };
                    assert forall|t: RwLockThreadPtr|
                        threads.contains(t) implies self.thread_map.dom().contains(t) by {
                        assert(
                            self.thread_map.dom().contains(t)
                            && self.thread_map.spec_index(t).view().owning_proc
                                == process_ptr
                        ) by {
                            reveal(process_thread_wf);
                        };
                    };
                    lemma_thread_ptr_seq_len_bounded(&*self, threads);
                };
                assert(
                    self.scheduler_map.spec_index(
                        scheduler_ptr
                    ).view().queue.view().len() < usize::MAX
                ) by {
                    let threads = self.scheduler_map.spec_index(
                        scheduler_ptr
                    ).view().queue.view();
                    assert(threads.no_duplicates()) by {
                        reveal(scheduler_perms_wf);
                        reveal(LinkedList::wf_value_list);
                        reveal(LinkedList::value_list_unique);
                    };
                    assert forall|t: RwLockThreadPtr|
                        threads.contains(t) implies self.thread_map.dom().contains(t) by {
                        reveal(container_thread_scheduler_wf);
                    };
                    lemma_thread_ptr_seq_len_bounded(&*self, threads);
                };
                let page_index = page_ptr2page_index(page_ptr);
                assert(
                    page_index_wf(page_index)
                    && self.page_array.inv()
                    && self.page_array.spec_index(page_index).view().is_init()
                    && self.page_array.spec_index(page_index).view().wlocked_by(&*lctx)
                    && self.page_array.spec_index(
                        page_index
                    ).view().view().perm_4k@.is_some()
                    && self.page_array.spec_index(
                        page_index
                    ).view().view().addr == page_ptr
                ) by {
                    reveal(page_array_wf);
                    reveal(page_locked_match_lctx);
                    page_ptr_lemma1();
                };
            }

            // ---- Inlined retype: create thread, flip page state, insert into thread_map ----
            let container_rodata = self.container_map.borrow_rodata(container_ptr);
            let container_ro = container_rodata.borrow();
            let container_depth = container_ro.depth;

            let process_rodata = self.process_map.borrow_rodata(process_ptr);
            let process_ro = process_rodata.borrow();
            let process_depth = process_ro.depth;
            let proc_pagetable = process_ro.pagetable;

            let thread_value = Thread::new_fresh(
                container_ptr,
                container_depth,
                process_ptr,
                process_depth,
                proc_pagetable,
                Ghost(self.container_map.spec_index(container_ptr).view().uppertree_seq.view()),
            );

            let page_index = page_ptr2page_index(page_ptr);
            let page_mut = self.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(page_lock_perm));
            let Tracked(page_perm) = take_perm_4k(page_mut);
            page_mut.state = PageState::Allocated4k{ state: Allocated4KPageState::AsThread };
            proof {
                assert(lctx.lock_map_contains(KernelObjId::Page(page_index))) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(LocalContext::lock_map_contains);
                };
                lctx.update_lock_id(
                    KernelObjId::Page(page_index),
                    self.page_array.lock_id_by_index(page_index),
                );
            }

            let (Tracked(thread_rwlock_perm), Tracked(thread_perm)) = retype_page_perm_to_thread(
                page_ptr, thread_value, Tracked(page_perm),
                Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)),
            );

            self.thread_map.insert_with_perm(
                page_ptr,
                Tracked(thread_rwlock_perm),
                (),
                Ghost(()),
                Ghost(()),
            );

            {
                let process_mut = self.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
                process_mut.temp_alloc_cache_4k = Ghost(process_mut.temp_alloc_cache_4k@.remove(page_ptr));
                process_mut.quota_4k = process_mut.quota_4k - 1;
            }
            // ---- End inlined retype ----

            proof {
                assert(self.container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
                add_thread_to_container_sets(
                    &mut self.container_map, container_ptr, page_ptr,
                    old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view(),
                );
            }

            proof {
                assert(old(self).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) == false) by {
                    reveal(process_thread_wf);
                    if old(self).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) {
                        assert(old(self).thread_map.spec_index(page_ptr).view().owning_proc == process_ptr) by {
                            reveal(process_thread_wf);
                        };
                    }
                }
            }
            let thread_mut = self.thread_map.borrow_mut(page_ptr, Tracked(&*lctx), Tracked(&thread_perm));
            let (node_addr, mut node_perm) = thread_mut.proc_linkedlist_node.take();
            node_update_value(node_addr, &mut node_perm, page_ptr);
            let process_mut = self.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
            proof {
                assert(
                    process_mut.owned_threads.wf()
                    && process_mut.owned_threads.length != usize::MAX
                ) by {
                    reveal(process_perms_wf);
                    reveal(LinkedList::wf_value_list);
                };
            }
            process_mut.owned_threads.push_tail(node_addr, node_perm);

            let (sched_node_addr, mut sched_node_perm) = thread_mut.scheduler_linkedlist_node.take();
            node_update_value(sched_node_addr, &mut sched_node_perm, page_ptr);
            proof {
                assert(
                    self.scheduler_map.perms_wf()
                    && self.scheduler_map.spec_index(scheduler_ptr).is_init()
                ) by {
                    reveal(scheduler_perms_wf);
                };
            }
            let scheduler_mut = self.scheduler_map.borrow_mut(scheduler_ptr, Tracked(&*lctx), Tracked(scheduler_lock_perm));
            proof {
                assert(
                    scheduler_mut.queue.wf()
                    && scheduler_mut.queue.length != usize::MAX
                ) by {
                    reveal(scheduler_perms_wf);
                    reveal(LinkedList::wf_value_list);
                };
                assert(!scheduler_mut.queue.view().contains(page_ptr)) by {
                    reveal(container_thread_scheduler_wf);
                };
            }
            scheduler_mut.queue.push_tail(sched_node_addr, sched_node_perm);
            thread_mut.state = ThreadState::SCHEDULED;

            proof {
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    reveal(cpu_array_wf);
                    reveal(container_perms_wf);
                    reveal(container_tree_fields_wf);
                    reveal(process_perms_wf);
                    reveal(process_temp_alloc_empty_unless_wlocked);
                    reveal(allocator_perms_wf);
                    reveal(thread_perms_wf);
                    reveal(threads_inv);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    reveal(page_array_wf);
                    reveal(scheduler_perms_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                        allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                        allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_uppertree_seq_wf);
                        container_process_allocator_quota_wf_preserved_on_thread_add(
                            *old(self), *self, container_ptr, page_ptr,
                            old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view(),
                        );
                    };
                    assert(container_allocator_wf(
                        self.container_map,
                        self.allocator_4k_map,
                        self.allocator_2m_map,
                        self.allocator_1g_map,
                    )) by {
                        reveal(container_allocator_wf);
                    };
                    assert(self.allocator_free_pages_wf()) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                        reveal(process_pagetable_match);
                    };
                    assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                    assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                        reveal(page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                        reveal(pagetable_perms_wf); reveal(pagetables_inv); page_ptr_lemma1();
                    };
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by {
                        reveal(pagetable_pages_wf);
                    };
                    assert(thread_pages_wf(self.thread_map, self.page_array)) by {
                        reveal(thread_pages_wf);
                    };
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_4k_wf);
                        process_staged_pages_2m_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                        process_staged_pages_1g_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                    };
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf);
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                        page_ptr_lemma1();
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf);
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                        page_ptr_lemma1();
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf);
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                        page_ptr_lemma1();
                    };
                };
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map)) by {
                        container_no_change_to_tree_fields_imply_wf(self.root_container, old(self).container_map, self.container_map);
                    };
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(per_container_process_tree_wf); reveal(container_process_wf);
                        per_container_process_tree_wf_preserved_for_tree_fields_eq(self.container_map, old(self).process_map, self.process_map);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by {
                        reveal(thread_endpoint_ref_counter_wf);
                    };
                    assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by {
                        reveal(thread_endpoint_queue_wf);
                    };
                    assert(container_thread_endpoint_wf(
                        self.container_map,
                        self.thread_map,
                        self.endpoint_map,
                    )) by {
                        reveal(container_endpoint_wf);
                        reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf);
                        reveal(container_thread_endpoint_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_scheduler_wf);
                        reveal(container_thread_wf);
                        reveal(container_scheduler_wf);
                        assert(
                            old(self).scheduler_map.spec_index(scheduler_ptr).view().queue.wf()
                        ) by {
                            reveal(scheduler_perms_wf);
                        };
                        seq_push_lemma::<RwLockThreadPtr>();
                    };
                    assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by {
                        reveal(thread_cpu_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        container_thread_wf_preserved_on_thread_add(
                            old(self).container_map, self.container_map, old(self).thread_map, self.thread_map,
                            container_ptr, page_ptr,
                            old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view(),
                        );
                    };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by {
                        assert(
                            old(self).process_map.spec_index(process_ptr).view().owned_threads.wf()
                        ) by {
                            reveal(process_perms_wf);
                        };
                        process_thread_wf_preserved_on_thread_add(
                            old(self).process_map,
                            self.process_map,
                            old(self).thread_map,
                            self.thread_map,
                            process_ptr,
                            page_ptr,
                            node_addr,
                        );
                    };
                };
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                };
                assert(self.inv()) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                    reveal(tlb_wf_spec);
                };
            }
            proof {
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
            }
            (page_ptr, Tracked(thread_perm))
        }

        /// TCB: reinterpret a staged 4k page as a fresh Thread object.
        /// Flips page state, unstages, initializes thread, grows thread_map.
        pub fn retype_staged_page_to_thread(
            &mut self,
            page_ptr: PagePtr,
            process_ptr: RwLockProcessPtr,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(page_lock_perm): Tracked<&LockPerm>,
            Tracked(process_lock_perm): Tracked<&LockPerm>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                page_ptr_valid(page_ptr),
                old(self).thread_map.dom().contains(page_ptr) == false,
                old(self).process_map.dom().contains(process_ptr),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.perms_wf(),
                old(self).process_map.perms_wf(),
                old(self).thread_map.perms_wf(),
                old(self).page_array.inv(),
                page_array_wf(old(self).page_array),
                old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view().len()
                    == old(self).container_map.spec_index(container_ptr).view_rodata().view().depth,
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(old(lctx)),
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().is_init(),
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Owned4k{ process_ptr }),
                page_lock_perm.state() is WriteLock,
                page_lock_perm.thread_id() == old(lctx).thread_id(),
                page_lock_perm.lock_id() == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == old(lctx).thread_id(),
                process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
                old(self).process_map.spec_index(process_ptr).view().quota_4k >= 1,
                old(self).locked_objects_match_lctx(old(lctx)),
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k@.is_some(),
            ensures
                final(self).page_array.inv(),
                final(self).page_array.unchanged_except(&old(self).page_array, page_ptr2page_index(page_ptr)),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Allocated4k{ state: Allocated4KPageState::AsThread }),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k@.is_none(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed()
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container,
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().addr
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().addr,

                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
                final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k - 1,
                final(self).process_map.spec_index(process_ptr).view().pcid
                    == old(self).process_map.spec_index(process_ptr).view().pcid,
                final(self).process_map.spec_index(process_ptr).view().ioid
                    == old(self).process_map.spec_index(process_ptr).view().ioid,
                final(self).process_map.spec_index(process_ptr).view().iommu_table
                    == old(self).process_map.spec_index(process_ptr).view().iommu_table,
                final(self).process_map.spec_index(process_ptr).view().pagetable
                    == old(self).process_map.spec_index(process_ptr).view().pagetable,
                final(self).process_map.spec_index(process_ptr).view().quota_2m
                    == old(self).process_map.spec_index(process_ptr).view().quota_2m,
                final(self).process_map.spec_index(process_ptr).view().quota_1g
                    == old(self).process_map.spec_index(process_ptr).view().quota_1g,
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                    == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m,
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                    == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g,
                final(self).process_map.spec_index(process_ptr).view().parent_linkedlist_node
                    == old(self).process_map.spec_index(process_ptr).view().parent_linkedlist_node,
                final(self).process_map.spec_index(process_ptr).view().children
                    == old(self).process_map.spec_index(process_ptr).view().children,
                final(self).process_map.spec_index(process_ptr).view().uppertree_seq
                    == old(self).process_map.spec_index(process_ptr).view().uppertree_seq,
                final(self).process_map.spec_index(process_ptr).view().subtree_set
                    == old(self).process_map.spec_index(process_ptr).view().subtree_set,
                final(self).process_map.spec_index(process_ptr).view().owned_threads
                    == old(self).process_map.spec_index(process_ptr).view().owned_threads,
                final(self).process_map.spec_index(process_ptr).view_rodata()
                    == old(self).process_map.spec_index(process_ptr).view_rodata(),
                final(self).process_map.spec_index(process_ptr).view().inv(),
                final(self).process_map.spec_index(process_ptr).is_init(),
                final(self).process_map.spec_index(process_ptr).locking_thread()
                    == old(self).process_map.spec_index(process_ptr).locking_thread(),
                final(self).process_map.spec_index(process_ptr).being_killed()
                    == old(self).process_map.spec_index(process_ptr).being_killed(),
                final(self).process_map.perms_wf(),

                final(self).thread_map.dom() =~= old(self).thread_map.dom().insert(page_ptr),
                forall|t:RwLockThreadPtr|
                    #![auto]
                    old(self).thread_map.dom().contains(t)
                    ==>
                    final(self).thread_map[t] == old(self).thread_map[t],
                final(self).thread_map.dom().contains(page_ptr),
                final(self).thread_map.spec_index(page_ptr).is_init(),
                final(self).thread_map.spec_index(page_ptr).being_killed() == false,
                final(self).thread_map.spec_index(page_ptr).wlocked_by(final(lctx)),
                final(self).thread_map.spec_index(page_ptr).locking_thread() == (RwLockState::Write {
                    thread_id: final(lctx).thread_id(),
                    lock_id: ret@.lock_id(),
                }),
                final(self).thread_map.lock_id_by_key(page_ptr) == (LockId{
                    container: final(self).thread_map.spec_index(page_ptr).view().container_depth(),
                    process: final(self).thread_map.spec_index(page_ptr).view().process_depth(),
                    major: final(self).thread_map.spec_index(page_ptr).view().current_lock_major(),
                    minor: page_ptr,
                }),
                final(self).thread_map.perms_wf(),

                final(self).thread_map.spec_index(page_ptr).view().inv(),
                final(self).thread_map.spec_index(page_ptr).view().owning_proc == process_ptr,
                final(self).thread_map.spec_index(page_ptr).view().owning_container == container_ptr,
                final(self).thread_map.spec_index(page_ptr).view().container_depth
                    == old(self).container_map.spec_index(container_ptr).view_rodata().view().depth,
                final(self).thread_map.spec_index(page_ptr).view().upper_container_seq
                    == old(self).container_map.spec_index(container_ptr).view().uppertree_seq,
                final(self).thread_map.spec_index(page_ptr).view().process_depth
                    == old(self).process_map.spec_index(process_ptr).view_rodata().view().depth,
                final(self).thread_map.spec_index(page_ptr).view().proc_pagetable_ptr
                    == old(self).process_map.spec_index(process_ptr).view().pagetable,
                final(self).thread_map.spec_index(page_ptr).view().proc_linkedlist_node.is_init(),
                final(self).thread_map.spec_index(page_ptr).view().scheduler_linkedlist_node.is_init(),
                (final(self).thread_map.spec_index(page_ptr).view().state is BLOCKED) == false,
                (final(self).thread_map.spec_index(page_ptr).view().state is SCHEDULED) == false,
                final(self).thread_map.spec_index(page_ptr).view().free_quota_pending_clean(),
                forall|edp_index: EndpointIdx| #![auto]
                    final(self).thread_map.spec_index(page_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is None,

                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                ret.view().state() is WriteLock,
                ret.view().thread_id() == final(lctx).thread_id(),
                ret.view().lock_id() == final(self).thread_map.spec_index(page_ptr).locking_thread()->Write_lock_id,
                final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(self).page_array[page_ptr2page_index(page_ptr)]@
                    .wlocked_by(final(lctx)),

                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Acquire,
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                final(lctx).wf(),
                final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                    final(self).thread_map.lock_id_by_key(page_ptr)),
                final(self).locked_objects_match_lctx(final(lctx)),
        {
            let container_rodata = self.container_map.borrow_rodata(container_ptr);
            let container_ro = container_rodata.borrow();
            let container_depth = container_ro.depth;

            let process_rodata = self.process_map.borrow_rodata(process_ptr);
            let process_ro = process_rodata.borrow();
            let process_depth = process_ro.depth;
            let proc_pagetable = process_ro.pagetable;

            let thread_value = Thread::new_fresh(
                container_ptr,
                container_depth,
                process_ptr,
                process_depth,
                proc_pagetable,
                Ghost(self.container_map.spec_index(container_ptr).view().uppertree_seq.view()),
            );

            let page_index = page_ptr2page_index(page_ptr);
            proof {
                assert(old(lctx).obj_id_fresh(KernelObjId::Thread(page_ptr))) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert(page_index_wf(page_index)) by {
                    page_ptr_lemma1();
                };
                assert(self.page_array.spec_index(page_index).view().view().addr == page_ptr) by {
                    reveal(page_array_wf);
                    page_ptr_lemma1();
                };
            }
            let page_mut = self.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(page_lock_perm));
            let Tracked(page_perm) = take_perm_4k(page_mut);
            page_mut.state = PageState::Allocated4k{ state: Allocated4KPageState::AsThread };

            let (Tracked(thread_rwlock_perm), Tracked(thread_lock_perm)) = retype_page_perm_to_thread(
                page_ptr, thread_value, Tracked(page_perm),
                Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)),
            );

            self.thread_map.insert_with_perm(
                page_ptr,
                Tracked(thread_rwlock_perm),
                (),
                Ghost(()),
                Ghost(()),
            );

            {
                let process_mut = self.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
                process_mut.temp_alloc_cache_4k = Ghost(process_mut.temp_alloc_cache_4k@.remove(page_ptr));
                process_mut.quota_4k = process_mut.quota_4k - 1;
            }

            proof {
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                };
            }
            Tracked(thread_lock_perm)
        }
    }

    proof fn lemma_thread_ptr_seq_len_bounded(k: &KernelK, threads: Seq<RwLockThreadPtr>)
        requires
            k.inv(),
            threads.no_duplicates(),
            forall|t: RwLockThreadPtr| threads.contains(t) ==> k.thread_map.dom().contains(t),
        ensures
            threads.len() <= NUM_PAGES,
    {
        assert forall|t: RwLockThreadPtr|
            k.thread_map.dom().contains(t)
            implies page_ptr_valid(t) by {
            reveal(thread_pages_wf);
        };
        page_ptr_lemma1();

        let thread_dom = k.thread_map.dom();
        let indices = thread_dom.map(|t: RwLockThreadPtr| page_ptr2page_index(t));
        assert(thread_dom.injective_on(
            |t: RwLockThreadPtr| page_ptr2page_index(t),
        )) by {
            assert forall|t1: RwLockThreadPtr, t2: RwLockThreadPtr|
                thread_dom.contains(t1)
                    && thread_dom.contains(t2)
                    && page_ptr2page_index(t1) == page_ptr2page_index(t2)
                implies t1 == t2 by {
            };
        };
        vstd::set_lib::lemma_map_size(
            thread_dom,
            indices,
            |t: RwLockThreadPtr| page_ptr2page_index(t),
        );

        let page_indices = Set::<usize>::range(0, NUM_PAGES);
        assert(indices.subset_of(page_indices)) by {
            broadcast use Set::lemma_map_contains;
            broadcast use vstd::set_lib::range_set_properties;
            assert forall|i: usize| indices.contains(i)
                implies page_indices.contains(i) by {
                let t = choose|t: RwLockThreadPtr|
                    thread_dom.contains(t) && i == page_ptr2page_index(t);
            };
        };
        vstd::set_lib::lemma_len_subset(indices, page_indices);
        broadcast use vstd::set_lib::range_set_properties;

        threads.unique_seq_to_set();
        assert(threads.to_set().subset_of(thread_dom)) by {
            assert forall|t: RwLockThreadPtr| threads.to_set().contains(t)
                implies thread_dom.contains(t) by {
            };
        };
        vstd::set_lib::lemma_len_subset(threads.to_set(), thread_dom);
    }

    /// Predicate: post_cm = pre_cm with t_ptr added to dc + ancestors' ghost sets.
    pub open spec fn container_map_gained_thread(
        pre_cm: ContainerLockedMap,
        post_cm: ContainerLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    ) -> bool {
        &&& post_cm.dom() == pre_cm.dom()
        // Direct container: owned_threads gained t_ptr; everything else of dc's view unchanged.
        &&& post_cm.spec_index(dc).view_user_ghost().owned_threads.view()
            =~= pre_cm.spec_index(dc).view_user_ghost().owned_threads.view().insert(t_ptr)
        // Every container OTHER than dc keeps its owned_threads (user-ghost).
        &&& forall|c: RwLockContainerPtr|
            #![trigger post_cm.spec_index(c).view_user_ghost().owned_threads]
            pre_cm.dom().contains(c) && c != dc
            ==>
            post_cm.spec_index(c).view_user_ghost().owned_threads
                == pre_cm.spec_index(c).view_user_ghost().owned_threads
        // Ancestor containers: each gained t_ptr in owned_indirect_threads.
        &&& forall|c: RwLockContainerPtr|
            #![trigger post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            uppers.contains(c)
            ==>
            post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads.view()
                =~= pre_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr)
        // Every container NOT an ancestor keeps its owned_indirect_threads (kernel-ghost).
        &&& forall|c: RwLockContainerPtr|
            #![trigger post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            pre_cm.dom().contains(c) && !uppers.contains(c)
            ==>
            post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads
                == pre_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads
    }

    /// Add t_ptr to dc's owned_threads + ancestors' owned_indirect_threads.
    pub proof fn add_thread_to_container_sets(
        tracked container_map: &mut ContainerLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            old(container_map).perms_wf(),
            old(container_map).dom().contains(dc),
            forall|i: int| #![auto] 0 <= i < uppers.len() ==> old(container_map).dom().contains(uppers[i]),
            uppers.no_duplicates(),
            !uppers.contains(dc),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            container_map_gained_thread(*old(container_map), *final(container_map), dc, t_ptr, uppers),
            // Only the ghost sets moved: each container's payload + rodata + lock state is held.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                    && final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                    && final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                    && final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                    && final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
    {
        container_map.update_user_ghost(dc, ContainerGhostU { owned_threads: Ghost(container_map.spec_index(dc).view_user_ghost().owned_threads.view().insert(t_ptr)) });
        add_thread_to_ancestor_sets(container_map, dc, t_ptr, uppers);
    }

    /// Recursive helper: insert t_ptr into ancestors' owned_indirect_threads.
    pub proof fn add_thread_to_ancestor_sets(
        tracked container_map: &mut ContainerLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            old(container_map).perms_wf(),
            forall|i: int| #![auto] 0 <= i < uppers.len() ==> old(container_map).dom().contains(uppers[i]),
            uppers.no_duplicates(),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            // Each ancestor gained t_ptr in owned_indirect_threads.
            forall|c: RwLockContainerPtr| #![auto]
                uppers.contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view()
                        =~= old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr),
            // Every container NOT in uppers keeps its kernel-view ghost.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) && !uppers.contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost() == old(container_map).spec_index(c).view_kernel_ghost(),
            // Only owned_indirect_threads (kernel-ghost) moves: every container's user-ghost is held.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view_user_ghost() == old(container_map).spec_index(c).view_user_ghost(),
            // Ghost-only updates: every container's payload + rodata + lock state is held.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                    && final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                    && final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                    && final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                    && final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
        decreases uppers.len(),
    {
        if uppers.len() > 0 {
            let c0 = uppers[0];
            container_map.update_kernel_ghost(c0, ContainerGhostK { owned_indirect_threads: Ghost(container_map.spec_index(c0).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr)) });
            add_thread_to_ancestor_sets(container_map, dc, t_ptr, uppers.drop_first());
            assert(!uppers.drop_first().contains(c0)) by {
                if uppers.drop_first().contains(c0) {
                    let k = choose|k: int| 0 <= k < uppers.drop_first().len() && uppers.drop_first()[k] == c0;
                }
            };
            assert forall|c: RwLockContainerPtr| #![auto] uppers.contains(c) implies c == c0 || uppers.drop_first().contains(c) by {
                if c != c0 {
                    let i = choose|i: int| 0 <= i < uppers.len() && uppers[i] == c;
                    if i == 0 {
                        assert(c == c0) by {
                            calc! {
                                (==)
                                c; {}
                                uppers[i]; {}
                                uppers[0]; {}
                                c0;
                            }
                        };
                    }
                    assert(uppers.drop_first()[i - 1] == c) by {
                        calc! {
                            (==)
                            uppers.drop_first()[i - 1]; {}
                            uppers[i]; {}
                            c;
                        }
                    };
                }
            };
            assert forall|c: RwLockContainerPtr| #![auto] uppers.drop_first().contains(c) implies uppers.contains(c) by {
                let k = choose|k: int| 0 <= k < uppers.drop_first().len() && uppers.drop_first()[k] == c;
            };
        }
    }

    /// Re-establish container_thread_wf after adding a thread.
    pub proof fn container_thread_wf_preserved_on_thread_add(
        pre_cm: ContainerLockedMap,
        post_cm: ContainerLockedMap,
        pre_tm: ThreadLockedMap,
        post_tm: ThreadLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            container_thread_wf(pre_cm, pre_tm),
            container_map_gained_thread(pre_cm, post_cm, dc, t_ptr, uppers),
            // thread_map grew by exactly t_ptr; pre-existing threads unchanged.
            post_tm.dom() =~= pre_tm.dom().insert(t_ptr),
            pre_tm.dom().contains(t_ptr) == false,
            forall|t: RwLockThreadPtr| #![auto] pre_tm.dom().contains(t) ==> post_tm.spec_index(t) == pre_tm.spec_index(t),
            // Container map non-set fields agree where wf reads them (rodata's
            // depth AND view()'s uppertree_seq; only the ghost sets moved).
            forall|c: RwLockContainerPtr| #![auto] pre_cm.dom().contains(c) ==>
                post_cm.spec_index(c).view_rodata() == pre_cm.spec_index(c).view_rodata()
                && post_cm.spec_index(c).view() == pre_cm.spec_index(c).view(),
            // The fresh thread is consistent with its direct container dc and ancestors.
            pre_cm.dom().contains(dc),
            forall|i: int| #![auto] 0 <= i < uppers.len() ==> pre_cm.dom().contains(uppers[i]),
            post_tm.spec_index(t_ptr).view().owning_container == dc,
            post_tm.spec_index(t_ptr).view().container_depth == post_cm.spec_index(dc).view_rodata().view().depth,
            post_tm.spec_index(t_ptr).view().upper_container_seq == post_cm.spec_index(dc).view().uppertree_seq,
            post_tm.spec_index(t_ptr).view().upper_container_seq.view() == uppers,
        ensures
            container_thread_wf(post_cm, post_tm),
    {
        assert(container_thread_wf(post_cm, post_tm)) by {
            reveal(container_thread_wf);
        };
    }

    /// Preserve process/thread ownership after inserting one fresh thread into
    /// its process's linked list. The caller supplies only the concrete map and
    /// linked-list frames produced by `retype_staged_page_to_thread` and
    /// `LinkedList::push_tail`.
    pub proof fn process_thread_wf_preserved_on_thread_add(
        pre_pm: ProcessLockedMap,
        post_pm: ProcessLockedMap,
        pre_tm: ThreadLockedMap,
        post_tm: ThreadLockedMap,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        node_addr: usize,
    )
        requires
            process_thread_wf(pre_pm, pre_tm),
            pre_pm.dom().contains(process_ptr),
            !pre_tm.dom().contains(thread_ptr),
            post_pm.unchanged_except(&pre_pm, process_ptr),
            post_tm.dom() =~= pre_tm.dom().insert(thread_ptr),
            forall|t: RwLockThreadPtr| #![auto]
                pre_tm.dom().contains(t) ==> post_tm.spec_index(t) == pre_tm.spec_index(t),
            post_pm.spec_index(process_ptr).view().owned_threads.view()
                =~= pre_pm.spec_index(process_ptr).view().owned_threads.view().push(thread_ptr),
            post_pm.spec_index(process_ptr).view().owned_threads.map()
                =~= pre_pm.spec_index(process_ptr).view().owned_threads.map().insert(
                    node_addr,
                    thread_ptr,
                ),
            !pre_pm.spec_index(process_ptr).view().owned_threads.map().dom().contains(node_addr),
            post_pm.spec_index(process_ptr).view().pagetable
                == pre_pm.spec_index(process_ptr).view().pagetable,
            post_tm.spec_index(thread_ptr).view().owning_proc == process_ptr,
            post_tm.spec_index(thread_ptr).view().proc_pagetable_ptr
                == post_pm.spec_index(process_ptr).view().pagetable,
            post_tm.spec_index(thread_ptr).view().proc_linkedlist_node.addr() == node_addr,
        ensures
            process_thread_wf(post_pm, post_tm),
    {
        seq_push_lemma::<RwLockThreadPtr>();
        assert(process_thread_wf(post_pm, post_tm)) by {
            reveal(process_thread_wf);
        };
    }

    /// Conservation law preserved across creating one thread.
    pub proof fn container_process_allocator_quota_wf_preserved_on_thread_add(
        pre: KernelK,
        post: KernelK,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            container_process_allocator_quota_wf(
                pre.container_map, pre.process_map, pre.thread_map,
                pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map,
            ),
            container_process_wf(pre.container_map, pre.process_map),
            container_thread_wf(pre.container_map, pre.thread_map),
            pre.container_map.dom().contains(dc),
            container_map_gained_thread(pre.container_map, post.container_map, dc, t_ptr, uppers),
            forall|c: RwLockContainerPtr| #![auto]
                pre.container_map.dom().contains(c) ==>
                    post.container_map.spec_index(c).view() == pre.container_map.spec_index(c).view()
                    && post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
            post.allocator_4k_map == pre.allocator_4k_map,
            post.allocator_2m_map == pre.allocator_2m_map,
            post.allocator_1g_map == pre.allocator_1g_map,
            post.process_map.dom() == pre.process_map.dom(),
            forall|p: RwLockProcessPtr|
                #![trigger post.process_map.spec_index(p).view()]
                post.process_map.dom().contains(p) ==>
                    process_effective_quota_4k(post.process_map.spec_index(p)) == process_effective_quota_4k(pre.process_map.spec_index(p))
                    && process_effective_quota_2m(post.process_map.spec_index(p)) == process_effective_quota_2m(pre.process_map.spec_index(p))
                    && process_effective_quota_1g(post.process_map.spec_index(p)) == process_effective_quota_1g(pre.process_map.spec_index(p)),
            post.thread_map.dom() =~= pre.thread_map.dom().insert(t_ptr),
            pre.thread_map.dom().contains(t_ptr) == false,
            forall|t: RwLockThreadPtr| #![auto] pre.thread_map.dom().contains(t) ==> post.thread_map.spec_index(t) == pre.thread_map.spec_index(t),
            post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view() == 0,
            post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view() == 0,
            post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view() == 0,
            forall|c: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c).view_rodata().view().depth]
                uppers.contains(c) ==>
                    post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c).view_rodata().view().depth as int) == 0
                    && post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c).view_rodata().view().depth as int) == 0
                    && post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c).view_rodata().view().depth as int) == 0,
        ensures
            container_process_allocator_quota_wf(
                post.container_map, post.process_map, post.thread_map,
                post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
            ),
    {
        assert(
            container_process_allocator_quota_4k_wf(
                pre.container_map, pre.process_map, pre.thread_map,
                pre.allocator_4k_map,
            )
            && container_process_allocator_quota_2m_wf(
                pre.container_map, pre.process_map, pre.thread_map,
                pre.allocator_2m_map,
            )
            && container_process_allocator_quota_1g_wf(
                pre.container_map, pre.process_map, pre.thread_map,
                pre.allocator_1g_map,
            )
            && container_process_wf(pre.container_map, pre.process_map)
            && container_thread_wf(pre.container_map, pre.thread_map)
        ) by {
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
            reveal(container_process_wf);
            reveal(container_thread_wf);
        };

        // 4k.
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
            post.container_map.dom().contains(c_ptr)
        implies
            post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.process_map.spec_index(p_ptr)))
                + post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().direct_free_quota_pending_4k.view())
                + post.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
                + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
        by {
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_wf);
            reveal(container_thread_wf);
            let s_p = post.container_map.spec_index(c_ptr).view().owned_processes.view();
            let d = post.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
            lemma_process_effective_quota_4k_fold_eq(s_p, pre.process_map, post.process_map);
            let s_d_pre = pre.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view();
            if c_ptr == dc {
                lemma_thread_direct_pending_4k_fold_insert_zero(s_d_pre, pre.thread_map, post.thread_map, t_ptr);
            } else {
                lemma_thread_direct_pending_4k_fold_eq(s_d_pre, pre.thread_map, post.thread_map);
            }
            let s_i_pre = pre.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view();
            if uppers.contains(c_ptr) {
                lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(s_i_pre, pre.thread_map, post.thread_map, t_ptr, d);
            } else {
                lemma_thread_indirect_pending_4k_fold_eq_at_depth(s_i_pre, pre.thread_map, post.thread_map, d);
            }
        };

        // 2m.
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
            post.container_map.dom().contains(c_ptr)
        implies
            post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.process_map.spec_index(p_ptr)))
                + post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().direct_free_quota_pending_2m.view())
                + post.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
                + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
        by {
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_wf);
            reveal(container_thread_wf);
            let s_p = post.container_map.spec_index(c_ptr).view().owned_processes.view();
            let d = post.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
            lemma_process_effective_quota_2m_fold_eq(s_p, pre.process_map, post.process_map);
            let s_d_pre = pre.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view();
            if c_ptr == dc {
                lemma_thread_direct_pending_2m_fold_insert_zero(s_d_pre, pre.thread_map, post.thread_map, t_ptr);
            } else {
                lemma_thread_direct_pending_2m_fold_eq(s_d_pre, pre.thread_map, post.thread_map);
            }
            let s_i_pre = pre.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view();
            if uppers.contains(c_ptr) {
                lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(s_i_pre, pre.thread_map, post.thread_map, t_ptr, d);
            } else {
                lemma_thread_indirect_pending_2m_fold_eq_at_depth(s_i_pre, pre.thread_map, post.thread_map, d);
            }
        };

        // 1g.
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
            post.container_map.dom().contains(c_ptr)
        implies
            post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.process_map.spec_index(p_ptr)))
                + post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().direct_free_quota_pending_1g.view())
                + post.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
                + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
        by {
            reveal(container_process_allocator_quota_1g_wf);
            reveal(container_process_wf);
            reveal(container_thread_wf);
            let s_p = post.container_map.spec_index(c_ptr).view().owned_processes.view();
            let d = post.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
            lemma_process_effective_quota_1g_fold_eq(s_p, pre.process_map, post.process_map);
            let s_d_pre = pre.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view();
            if c_ptr == dc {
                lemma_thread_direct_pending_1g_fold_insert_zero(s_d_pre, pre.thread_map, post.thread_map, t_ptr);
            } else {
                lemma_thread_direct_pending_1g_fold_eq(s_d_pre, pre.thread_map, post.thread_map);
            }
            let s_i_pre = pre.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view();
            if uppers.contains(c_ptr) {
                lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(s_i_pre, pre.thread_map, post.thread_map, t_ptr, d);
            } else {
                lemma_thread_indirect_pending_1g_fold_eq_at_depth(s_i_pre, pre.thread_map, post.thread_map, d);
            }
        };
        assert(container_process_allocator_quota_wf(
            post.container_map, post.process_map, post.thread_map,
            post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
        )) by {
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
        };
    }

    /// User-view change predicate for successful new_thread.
    pub open spec fn kernel_u_new_thread_changed(
        old_u: KernelU,
        new_u: KernelU,
        process_ptr: RwLockProcessPtr,
    ) -> bool {
        &&& new_u.cpu_array == old_u.cpu_array
        &&& new_u.process_map.dom() == old_u.process_map.dom()
        &&& old_u.process_map.dom().contains(process_ptr)
        // The targeted process: quota_4k decreased by 1, owned_threads grew by 1.
        &&& new_u.process_map[process_ptr].quota_4k as int
                == old_u.process_map[process_ptr].quota_4k as int - 1
        &&& new_u.process_map[process_ptr].owned_threads.len()
                == old_u.process_map[process_ptr].owned_threads.len() + 1
        &&& new_u.process_map[process_ptr].owned_threads.subrange(
                0, old_u.process_map[process_ptr].owned_threads.len() as int)
                == old_u.process_map[process_ptr].owned_threads
        // Every other field of the targeted process preserved.
        &&& new_u.process_map[process_ptr].pagetable      == old_u.process_map[process_ptr].pagetable
        &&& new_u.process_map[process_ptr].quota_2m       == old_u.process_map[process_ptr].quota_2m
        &&& new_u.process_map[process_ptr].quota_1g       == old_u.process_map[process_ptr].quota_1g
        &&& new_u.process_map[process_ptr].parent         == old_u.process_map[process_ptr].parent
        &&& new_u.process_map[process_ptr].children       == old_u.process_map[process_ptr].children
        &&& new_u.process_map[process_ptr].depth          == old_u.process_map[process_ptr].depth
        &&& new_u.process_map[process_ptr].uppertree_seq  == old_u.process_map[process_ptr].uppertree_seq
        &&& new_u.process_map[process_ptr].subtree_set    == old_u.process_map[process_ptr].subtree_set
        &&& new_u.process_map[process_ptr].killed         == old_u.process_map[process_ptr].killed
        // Every other process: projection unchanged.
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map[p]]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map[p] == old_u.process_map[p]
    }
}

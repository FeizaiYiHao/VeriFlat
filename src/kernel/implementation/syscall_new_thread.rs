use vstd::prelude::*;
use crate::*;
verus! {
    impl KernelK {
        /// syscall_new_thread: create a new thread in the running process on
        /// `cpu_id`. Returns an error if the process is being torn down or
        /// lacks at least one 4k page of quota.
        ///
        /// Lock order (deadlock-free; ascending LockId): cpu -> process.
        ///
        /// CURRENT STATUS (work in progress):
        ///  - cpu + process lock acquisition and 4k-quota check: done.
        ///  - thread allocation / scheduler wiring: not yet implemented;
        ///    the quota-sufficient path releases both locks and returns Error.
        #[verifier::spinoff_prover]
        pub fn syscall_new_thread(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
        ) -> (ret: RetValueType)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                old(self).all_objects_unlocked(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                lctx.lock_map() == Map::<KernelObjId, LockId>::empty(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            ensures
                final(steps).steps.len() == 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
                ret is ErrorProcessKilled
                    || ret is ErrorNoQuota
                    || ret is Error,
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(KernelK::thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
                assert(self.cpu_array.inv());
                assert(self.container_map.perms_wf());
                assert(self.allocator_4k_map.perms_wf());
                assert(self.process_map.perms_wf());
                reveal(cpu_objects_unlocked);
                reveal(container_objects_unlocked);
                reveal(allocator_objects_unlocked);
                reveal(process_objects_unlocked);
            }

            assert(
                {
                    &&&
                    self.container_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().owning_container)
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    &&&
                    self.process_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().process_depth
                        == self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().depth
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().container_depth
                        == self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                    &&&
                    self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().container_depth
                        == self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                }
            ) by {
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };

            let ghost entry_lctx = lctx@;

            // ---- Lock #1: the running cpu. ----
            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();

            // ---- Lock #2: the running process (kill-aware). ----
            assert(
                {
                    &&& self.process_map.dom().contains(process_ptr)
                    &&& self.process_map.spec_index(process_ptr).locked_by(&lctx@) == false
                }
            ) by {
                reveal(process_objects_unlocked);
                reveal(KernelK::all_objects_unlocked);
                assert(self.process_map.spec_index(process_ptr) == old(self).process_map.spec_index(process_ptr));
                assert(old(self).all_objects_unlocked(&entry_lctx));
            };
            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(&mut lctx));
            if let (false, _) = process_res {
                // ===== PROCESS KILLED =====
                assert(self.process_map.spec_index(process_ptr).being_killed() == true);
                proof {
                    assert(lctx@.lock_map().dom() =~= set![ KernelObjId::Cpu(cpu_id) ]);
                }
                self.release_cpu_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id,
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();

            proof {
                assert(lctx@.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Process(process_ptr),
                ]);
            }

            // ---- Quota check: the process needs at least one 4k page. ----
            let process_ref = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            if process_ref.quota_4k < 1 {
                self.release_cpu_and_process_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id,
                    process_ptr,
                    Tracked(process_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorNoQuota;
            }

            // ===== QUOTA SUFFICIENT — thread creation not yet implemented. =====
            self.release_cpu_and_process_and_finish(
                Tracked(lctx.get()),
                Tracked(&mut *steps),
                cpu_id,
                process_ptr,
                Tracked(process_lock_perm),
                Tracked(cpu_lock_perm),
            );
            return RetValueType::Error;
        }

        /// Helper: open a user-view step, release process then cpu (reverse of
        /// acquire order), and close the step.
        #[verifier::spinoff_prover]
        fn release_cpu_and_process_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            process_ptr: RwLockProcessPtr,
            process_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Process(process_ptr),
                ],
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Process(process_ptr)],
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).inv(),
                old(self).process_map.perms_wf(),
                // Temp-alloc must be drained before the process is unlocked (the
                // "flushed before wunlock" protocol; required by wunlock_process).
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
            ensures
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();

            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(KernelK::thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            }

            let ghost entry_steps_len = steps.steps.len();

            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            let ghost pre_wunlock_self = *self;
            self.wunlock_process(process_ptr, Tracked(&mut lctx), Tracked(process_lock_perm));

            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == old(self).cpu_array);
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));

            proof {
                assert forall|p_ptr: RwLockProcessPtr|
                    #![trigger self.process_map.spec_index(p_ptr).view()]
                    #![trigger self.process_map.spec_index(p_ptr).view_rodata()]
                    self.process_map.dom().contains(p_ptr)
                implies
                    self.process_map.spec_index(p_ptr).view() == old(self).process_map.spec_index(p_ptr).view()
                    && self.process_map.spec_index(p_ptr).view_rodata() == old(self).process_map.spec_index(p_ptr).view_rodata()
                    && self.process_map.spec_index(p_ptr).being_killed() == old(self).process_map.spec_index(p_ptr).being_killed()
                by {};
                assert(process_perms_wf(self.process_map)) by {
                    assert(self.process_map.perms_wf());
                    assert(self.process_map.spec_index(process_ptr).inv());
                    // lemma_process_perms_wf_preserved_for_process_lock_op(
                    //     pre_wunlock_self.process_map,
                    //     self.process_map,
                    //     process_ptr,
                    // );
                };
                assert(self.thread_perms_wf()) by {
                    reveal(KernelK::thread_perms_wf);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                };
                assert(self.pagetable_map == old(self).pagetable_map);
                assert(self.cpu_array.unchanged_except(&cpu_array_before_unlock, cpu_id));
                assert(self.cpu_array.unchanged_except(&old(self).cpu_array, cpu_id));
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == old(self).cpu_array.spec_index(cpu_id).view().view());
                assert(self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                // lemma_release_with_process_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*old(self))
                    == kernel_k_to_kernel_u(*self));
            }
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }
    }
}

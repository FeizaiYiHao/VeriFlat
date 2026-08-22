use vstd::prelude::*;
use vstd::calc;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use crate::*;
use super::syscall_new_thread_helpers::{
    kernel_u_new_thread_changed,
    new_thread_other_objects_unlocked,
};

verus! {
    impl KernelK {
        /// syscall_new_thread: create a new thread in the running process on
        /// `cpu_id`. Lock order: cpu -> process -> current thread -> scheduler.
        #[verifier::spinoff_prover]
        pub fn syscall_new_thread(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
        ) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(self).inv(),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                old(self).cpu_array.spec_index(cpu_id).view().locked_by(old(lctx)) == false,
                {
                    let process_ptr =
                        old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
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
                lock_id_aligned(old(self), old(lctx)),
                old(self).all_objects_unlocked(old(lctx)),
            ensures
                final(steps).steps.len() <= 1,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                final(self).all_objects_unlocked(final(lctx)),
                !(ret is Success) ==> final(steps).steps.len() == 0,
                ret is Success ==> {
                    let process_ptr = old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& final(steps).steps.len() == 1
                    &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self))
                    &&& kernel_u_new_thread_changed(
                            final(steps).steps.last().old_u,
                            final(steps).steps.last().new_u,
                            process_ptr,
                        )
                },
                ret is Success
                    || ret is ErrorProcessKilled
                    || ret is ErrorThreadKilled
                    || ret is ErrorNoQuota,
        {
            proof {
                assert(
                    self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    && self.cpu_array.spec_index(cpu_id).view().view().current_thread is Some
                ) by {
                    reveal(cpu_array_wf);
                    reveal(process_cpu_wf);
                    reveal(thread_cpu_wf);
                };
            }
            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut *lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();
            let current_thread_ptr = cpu.current_thread.unwrap();

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
                let process_lock_id = self.process_map.lock_id_by_key(process_ptr);
                assert(process_lock_id.spec_gt(self.cpu_array.lock_id_by_index(cpu_id))) by {
                    reveal(container_cpu_wf);
                    reveal(process_cpu_wf);
                    reveal(container_process_wf);
                };
            }
            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(&mut *lctx));
            if let (false, _) = process_res {
                proof {
                    assert(steps.snap_shot == kernel_k_to_kernel_u(*self)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                    assert(new_thread_other_objects_unlocked(
                        self, lctx.thread_id(), Some(cpu_id),
                        None, None, None, None,
                    )) by {
                        reveal(new_thread_other_objects_unlocked);
                    };
                }
                self.release_cpu_and_finish(
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();

            proof {
                assert({
                    &&& self.thread_map.dom().contains(current_thread_ptr)
                    &&& self.thread_map.spec_index(current_thread_ptr).view().owning_proc
                        == process_ptr
                    &&& self.thread_map.spec_index(current_thread_ptr).view().owning_container
                        == proc_container
                    &&& self.thread_map.spec_index(current_thread_ptr).view().container_depth
                        == self.process_map.spec_index(process_ptr).view_rodata().view().container_depth
                    &&& self.thread_map.spec_index(current_thread_ptr).view().process_depth
                        == self.process_map.spec_index(process_ptr).view_rodata().view().depth
                }) by {
                    reveal(thread_cpu_wf);
                    reveal(process_thread_wf);
                };
                assert(self.thread_map.lock_id_by_key(current_thread_ptr)
                    .spec_gt(self.process_map.lock_id_by_key(process_ptr))) by {
                    reveal(process_thread_wf);
                    reveal(process_perms_wf);
                    reveal(thread_perms_wf);
                };
            }
            let thread_res = self.wlock_thread_unless_killed(
                current_thread_ptr, Tracked(&mut *lctx),
            );
            if let (false, _) = thread_res {
                proof {
                    assert(steps.snap_shot == kernel_k_to_kernel_u(*self)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                    assert(new_thread_other_objects_unlocked(
                        self, lctx.thread_id(), Some(cpu_id),
                        None, Some(process_ptr), None, None,
                    )) by {
                        reveal(new_thread_other_objects_unlocked);
                    };
                }
                self.release_cpu_and_process_and_finish(
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    process_ptr,
                    Tracked(process_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();

            let thread_ref = self.thread_map.borrow(
                current_thread_ptr, Tracked(&current_thread_lock_perm),
            );
            if thread_ref.quota_4k < 1 {
                proof {
                    assert(steps.snap_shot == kernel_k_to_kernel_u(*self)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                    assert(new_thread_other_objects_unlocked(
                        self, lctx.thread_id(), Some(cpu_id),
                        None, Some(process_ptr), Some(current_thread_ptr), None,
                    )) by {
                        reveal(new_thread_other_objects_unlocked);
                    };
                }
                self.release_cpu_and_process_and_thread_and_finish(
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    process_ptr,
                    current_thread_ptr,
                    Tracked(current_thread_lock_perm),
                    Tracked(process_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorNoQuota;
            }

            proof {
                assert(self.scheduler_map.dom().contains(scheduler_ptr)) by {
                    reveal(container_scheduler_wf);
                };
                let scheduler_lock_id = self.scheduler_map.lock_id_by_key(scheduler_ptr);
                assert(scheduler_lock_id.major == SCHEDULER_LOCK_MAJOR) by {
                    reveal(scheduler_perms_wf);
                };
                assert(process_lock_perm.ordering_lock_id().major
                    == PROCESS_LOCK_MAJOR) by {
                    reveal(process_perms_wf);
                };
                assert(current_thread_lock_perm.ordering_lock_id().major
                    == THREAD_LOCK_MAJOR) by {
                    reveal(thread_cpu_wf);
                    reveal(thread_perms_wf);
                };
                assert(lctx.held_lock_majors_lt(SCHEDULER_LOCK_MAJOR)) by {
                };
                assert(lctx.lock_id_acyclic(scheduler_lock_id)) by {
                    reveal(scheduler_perms_wf);
                };
            }
            let Tracked(scheduler_lock_perm) = self.wlock_scheduler(
                scheduler_ptr, Tracked(&mut *lctx),
            );

            // ===== QUOTA SUFFICIENT =====
            proof {
                assert({
                    &&& self.thread_map.spec_index(current_thread_ptr).view().owning_proc
                        == process_ptr
                    &&& lctx.lock_entry_contains(
                        self.scheduler_map.lock_id_by_key(scheduler_ptr),
                        KernelObjId::Scheduler(scheduler_ptr),
                    )
                }) by {
                    reveal(thread_cpu_wf);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            proof {
                assert(new_thread_other_objects_unlocked(
                    self, lctx.thread_id(), Some(cpu_id),
                    Some(scheduler_ptr), Some(process_ptr),
                    Some(current_thread_ptr), None,
                )) by {
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            self.add_new_thread_to_proc_container_and_scheduler(
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                cpu_id,
                process_ptr,
                current_thread_ptr,
                proc_container,
                scheduler_ptr,
                Tracked(process_lock_perm),
                Tracked(current_thread_lock_perm),
                Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm),
            );
            return RetValueType::Success;
        }
    }

}

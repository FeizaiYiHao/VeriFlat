use vstd::prelude::*;
use vstd::{assert_seqs_equal, assert_sets_equal};
use crate::*;
use crate::implementation::syscall_new_thread::kernel_u_new_thread_changed;

verus! {

impl KernelK {
    /// Create a thread whose endpoint descriptor 0 aliases descriptor
    /// `endpoint_index` of the thread currently running on `cpu_id`.
    #[verifier::spinoff_prover]
    pub fn syscall_new_thread_with_endpoint(
        &mut self,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
    ) -> (ret: RetValueType)
        requires
            cpu_id_valid(cpu_id),
            edp_idx_valid(endpoint_index),
            old(self).inv(),
            old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
            old(self).cpu_array[cpu_id]@@.current_process is Some,
            old(self).cpu_array[cpu_id]@@.current_thread is Some,
            old(self).process_map.dom().contains(
                old(self).cpu_array[cpu_id]@@.current_process->Some_0,
            ),
            old(self).container_map.dom().contains(
                old(self).process_map.spec_index(
                    old(self).cpu_array[cpu_id]@@.current_process->Some_0,
                ).view_rodata().view().owning_container,
            ),
            {
                let process_ptr = old(self).cpu_array[cpu_id]@@.current_process->Some_0;
                let container_ptr = old(self).process_map.spec_index(process_ptr)
                    .view_rodata().view().owning_container;
                old(self).scheduler_map.dom().contains(
                    old(self).container_map.spec_index(container_ptr)
                        .view_rodata().view().scheduler,
                )
            },
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<LockId>::empty(),
            old(self).cpu_array[cpu_id]@.locked_by(old(lctx)) == false,
            {
                let process_ptr = old(self).cpu_array[cpu_id]@@.current_process->Some_0;
                let container_ptr = old(self).process_map.spec_index(process_ptr)
                    .view_rodata().view().owning_container;
                let scheduler_ptr = old(self).container_map.spec_index(container_ptr)
                    .view_rodata().view().scheduler;
                &&& old(self).cpu_array[cpu_id]@@.current_process is Some
                &&& old(self).cpu_array[cpu_id]@@.current_thread is Some
                &&& old(self).process_map.dom().contains(process_ptr)
                &&& old(self).container_map.dom().contains(container_ptr)
                &&& old(self).scheduler_map.dom().contains(scheduler_ptr)
                &&& old(self).process_map.spec_index(process_ptr).locked_by(old(lctx)) == false
                &&& old(self).scheduler_map.spec_index(scheduler_ptr).locked_by(old(lctx)) == false
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
            !(ret is Success) ==>
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
            ret is Success ==> {
                let process_ptr = old(self).cpu_array.spec_index(cpu_id)
                    .view().view().current_process->Some_0;
                kernel_u_new_thread_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                )
            },
            ret is Success
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorNoQuota
                || ret is Error,
    {
        proof {
            assert(
                self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                && self.cpu_array.spec_index(cpu_id).view().view().current_thread is Some
            ) by { reveal(cpu_array_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
        }
        let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let current_thread_ptr = cpu.current_thread.unwrap();

        proof {
            assert(self.process_map.dom().contains(process_ptr)) by { reveal(process_cpu_wf); };
            assert(self.process_map.perms_wf()) by { reveal(process_perms_wf); };
        }
        let container_ptr = self.process_map.borrow_rodata(process_ptr)
            .borrow().owning_container;
        proof {
            assert(self.container_map.dom().contains(container_ptr)) by { reveal(container_process_wf); };
            assert(self.container_map.perms_wf()) by { reveal(container_perms_wf); };
        }
        let scheduler_ptr = self.container_map.borrow_rodata(container_ptr)
            .borrow().scheduler;

        proof {
            assert(self.scheduler_map.dom().contains(scheduler_ptr)) by { reveal(container_scheduler_wf); };
            assert(self.scheduler_map.lock_id_by_key(scheduler_ptr).major
                == SCHEDULER_LOCK_MAJOR) by { reveal(scheduler_perms_wf); };
            assert(self.scheduler_map.lock_id_by_key(scheduler_ptr)
                .spec_gt(self.cpu_array.lock_id_by_index(cpu_id))) by { reveal(cpu_locked_match_lctx); };
            assert(self.process_map.lock_id_by_key(process_ptr)
                .spec_gt(self.cpu_array.lock_id_by_index(cpu_id))) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); reveal(cpu_locked_match_lctx); };
        }
        let Tracked(scheduler_lock_perm) = self.wlock_scheduler(
            scheduler_ptr, Tracked(&mut *lctx),
        );
        proof {
            assert(self.process_map.lock_id_by_key(process_ptr).major
                == PROCESS_LOCK_MAJOR) by { reveal(process_perms_wf); };
            assert(
                self.process_map.dom().contains(process_ptr)
                && self.process_map.spec_index(process_ptr).locked_by(&*lctx) == false
            ) by { reveal(process_cpu_wf); };
            assert(self.process_map.lock_id_by_key(process_ptr)
                .spec_gt(self.scheduler_map.lock_id_by_key(scheduler_ptr))) by { reveal(scheduler_locked_match_lctx); };
        }
        let process_res = self.wlock_process_unless_killed(
            process_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = process_res {
            self.release_cpu_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr,
                Tracked(cpu_lock_perm), Tracked(scheduler_lock_perm),
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
                    == container_ptr
                &&& self.thread_map.spec_index(current_thread_ptr).view().container_depth
                    == self.process_map.spec_index(process_ptr).view_rodata().view().container_depth
                &&& self.thread_map.spec_index(current_thread_ptr).view().process_depth
                    == self.process_map.spec_index(process_ptr).view_rodata().view().depth
            }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
            assert(self.thread_map.lock_id_by_key(current_thread_ptr)
                .spec_gt(self.process_map.lock_id_by_key(process_ptr))) by { reveal(process_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf); };
        }
        let thread_res = self.wlock_thread_unless_killed(
            current_thread_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = thread_res {
            self.release_cpu_and_process_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr,
                process_ptr, Tracked(process_lock_perm), Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm),
            );
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();

        let thread_ref = self.thread_map.borrow(
            current_thread_ptr, Tracked(&current_thread_lock_perm),
        );
        let endpoint_option = *thread_ref.endpoint_descriptors.get(endpoint_index);
        if let None = endpoint_option {
            self.release_cpu_and_process_and_thread_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr,
                process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm),
                Tracked(process_lock_perm), Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm),
            );
            return RetValueType::Error;
        }
        let endpoint_ptr = endpoint_option.unwrap();

        if thread_ref.quota_4k < 1 {
            self.release_cpu_and_process_and_thread_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr,
                process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm),
                Tracked(process_lock_perm), Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm),
            );
            return RetValueType::ErrorNoQuota;
        }

        proof {
            assert({
                &&& self.endpoint_map.dom().contains(endpoint_ptr)
                &&& self.container_map.dom().contains(
                    self.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                )
                &&& self.endpoint_map.spec_index(endpoint_ptr).view().owning_threads
                    .view().contains((current_thread_ptr, endpoint_index))
            }) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
            assert(
                self.container_map.dom().contains(
                    self.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                )
                && {
                    ||| self.endpoint_map.spec_index(endpoint_ptr).view().owning_container
                        == container_ptr
                    ||| self.container_map.spec_index(
                            self.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                        ).view().subtree_set.view().contains(container_ptr)
                }
            ) by { reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
        self.add_new_thread_with_endpoint(
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr,
            current_thread_ptr, container_ptr, scheduler_ptr, endpoint_ptr,
            endpoint_index, Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm),
            Tracked(scheduler_lock_perm),
        );
        RetValueType::Success
    }

    #[verifier::spinoff_prover]
    fn add_new_thread_with_endpoint(
        &mut self,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx,
        process_lock_perm: Tracked<LockPerm>,
        current_thread_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
        scheduler_lock_perm: Tracked<LockPerm>,
    )
        requires
            cpu_id_valid(cpu_id),
            edp_idx_valid(endpoint_index),
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            old(self).scheduler_map.dom().contains(scheduler_ptr),
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(current_thread_ptr),
            old(self).container_map.dom().contains(container_ptr),
            old(self).endpoint_map.dom().contains(endpoint_ptr),
            old(self).thread_map.spec_index(current_thread_ptr).view()
                .endpoint_descriptors.wf(),
            old(self).container_map.dom().contains(
                old(self).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            ),
            old(self).thread_map.spec_index(current_thread_ptr).view()
                .endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            {
                ||| old(self).endpoint_map.spec_index(endpoint_ptr).view().owning_container
                    == container_ptr
                ||| old(self).container_map.spec_index(
                        old(self).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                    ).view().subtree_set.view().contains(container_ptr)
            },
            old(lctx).lock_id_set() =~= set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
            ],
            old(lctx).wf(),
            cpu_lock_perm@.state() is WriteLock,
            cpu_lock_perm@.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm@.lock_id()
                == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
            old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
            scheduler_lock_perm@.state() is WriteLock,
            scheduler_lock_perm@.thread_id() == old(lctx).thread_id(),
            scheduler_lock_perm@.lock_id()
                == old(self).scheduler_map.spec_index(scheduler_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
            old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
            old(self).container_map.spec_index(container_ptr).view_rodata().view().scheduler
                == scheduler_ptr,
            process_lock_perm@.state() is WriteLock,
            process_lock_perm@.thread_id() == old(lctx).thread_id(),
            process_lock_perm@.lock_id()
                == old(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container
                == container_ptr,
            current_thread_lock_perm@.state() is WriteLock,
            current_thread_lock_perm@.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm@.lock_id()
                == old(self).thread_map.spec_index(current_thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(current_thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(self).thread_map.spec_index(current_thread_ptr).view().owning_container
                == container_ptr,
            old(self).thread_map.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(current_thread_ptr).view().quota_4k >= 1,
            old(self).cpu_array.lock_id_by_index(cpu_id).major == CPU_LOCK_MAJOR_RUNNING,
            old(self).scheduler_map.lock_id_by_key(scheduler_ptr).major == SCHEDULER_LOCK_MAJOR,
            old(self).process_map.lock_id_by_key(process_ptr).major == PROCESS_LOCK_MAJOR,
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
        ensures
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= Set::<LockId>::empty(),
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).steps.last().new_k == *final(self),
            final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
            kernel_u_new_thread_changed(
                final(steps).steps.last().old_u,
                final(steps).steps.last().new_u,
                process_ptr,
            ),
    {
        let tracked mut process_lock_perm = process_lock_perm.get();
        let tracked mut current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked scheduler_lock_perm = scheduler_lock_perm.get();

        proof {
            assert_sets_equal!(lctx.lock_id_set() == set![
                self.cpu_array.lock_id_by_index(cpu_id),
                self.scheduler_map.lock_id_by_key(scheduler_ptr),
                self.process_map.lock_id_by_key(process_ptr),
                self.thread_map.lock_id_by_key(current_thread_ptr),
            ], lock_id => {});
            assert(self.container_map.perms_wf()) by { reveal(container_perms_wf); };
        }
        let alloc_ptr_4k = self.container_map.borrow_rodata(container_ptr)
            .borrow().allocator_ptr_4k;
        proof {
            assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
        }

        let (page_ptr, Tracked(page_lock_perm)) = self.allocate_free_4k_page(
            alloc_ptr_4k, current_thread_ptr, process_ptr, container_ptr, cpu_id,
            scheduler_ptr, Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(&current_thread_lock_perm),
        );
        let page_index = page_ptr2page_index(page_ptr);

        proof {
            assert(
                self.thread_map.spec_index(current_thread_ptr).view()
                    .endpoint_descriptors.spec_index(endpoint_index)
                    == Some(endpoint_ptr)
                && self.endpoint_map.dom().contains(endpoint_ptr)
            ) by { reveal(thread_endpoint_ref_counter_wf); };
            assert(lctx.lock_id_acyclic(
                self.endpoint_map.lock_id_by_key(endpoint_ptr),
            )) by { reveal(LocalContext::lock_id_acyclic); reveal(endpoint_perms_wf); reveal(page_array_wf); };
        }
        let Tracked(endpoint_lock_perm) = self.wlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx),
        );

        proof {
            steps.begin_user_view_step(&*self, &mut *lctx);
            assert(self.container_map.dom().contains(
                self.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            )) by { reveal(container_endpoint_wf); };
            assert({
                ||| self.endpoint_map.spec_index(endpoint_ptr).view().owning_container
                    == container_ptr
                ||| self.container_map.spec_index(
                        self.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                    ).view().subtree_set.view().contains(container_ptr)
            }) by { reveal(container_thread_endpoint_wf); };
        }
        let (new_thread_ptr, Tracked(new_thread_lock_perm)) =
            self.create_thread_from_staged_page_merged(
                page_ptr, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr,
                Tracked(&mut *lctx), Tracked(&page_lock_perm),
                Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm),
                Tracked(&scheduler_lock_perm),
            );

        proof {
            assert(self.container_map.dom().contains(
                self.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            )) by { reveal(container_endpoint_wf); };
            assert(self.thread_map.lock_id_by_key(new_thread_ptr)
                != self.thread_map.lock_id_by_key(current_thread_ptr)) by { reveal(thread_perms_wf); reveal(thread_cpu_wf); };
        }
        self.attach_endpoint_reference_and_unlock(
            new_thread_ptr, endpoint_ptr, cpu_id, scheduler_ptr, process_ptr,
            current_thread_ptr, page_index, Tracked(&mut *lctx),
            Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm),
        );
        proof {
            assert_sets_equal!(lctx.lock_id_set() == set![
                self.cpu_array.lock_id_by_index(cpu_id),
                self.scheduler_map.lock_id_by_key(scheduler_ptr),
                self.process_map.lock_id_by_key(process_ptr),
                self.thread_map.lock_id_by_key(current_thread_ptr),
                self.page_array.lock_id_by_index(page_index),
            ], lock_id => {});
        }
        self.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        self.wunlock_scheduler(
            scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm),
        );
        self.wunlock_thread(
            current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm),
        );
        self.wunlock_process(
            process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
        );
        self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            broadcast use vstd::set::group_set_lemmas;
            assert_sets_equal!(
                lctx.lock_id_set() == Set::<LockId>::empty(),
                lock_id => {}
            );
            steps.end_user_view_step(&*self, &mut *lctx);
            assert(kernel_u_new_thread_changed(
                steps.steps.last().old_u,
                steps.steps.last().new_u,
                process_ptr,
            )) by { reveal(kernel_u_new_thread_changed); reveal(kernel_k_to_kernel_u);
                assert_seqs_equal!(
                    steps.steps.last().new_u.cpu_array
                        == steps.steps.last().old_u.cpu_array,
                    i => {
                        reveal(kernel_k_to_kernel_u);
                    }
                );
            };
        }
    }

    /// Add the first endpoint descriptor and its reverse reference together.
    #[verifier::spinoff_prover]
    fn attach_endpoint_reference_and_unlock(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr,
        cpu_id: CpuId,
        scheduler_ptr: RwLockSchedulerPtr,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        page_index: PageIndex,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
            page_index_wf(page_index),
            old(self).scheduler_map.dom().contains(scheduler_ptr),
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(current_thread_ptr),
            current_thread_ptr != thread_ptr,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).is_init(),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).view().state is SCHEDULED,
            old(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors.wf(),
            old(self).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .endpoint_descriptors.spec_index(0) is None,
            old(self).endpoint_map.dom().contains(endpoint_ptr),
            old(self).endpoint_map.spec_index(endpoint_ptr).is_init(),
            old(self).container_map.dom().contains(
                old(self).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            ),
            {
                ||| old(self).endpoint_map.spec_index(endpoint_ptr).view().owning_container
                    == old(self).thread_map.spec_index(thread_ptr).view().owning_container
                ||| old(self).container_map.spec_index(
                        old(self).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                    ).view().subtree_set.view().contains(
                        old(self).thread_map.spec_index(thread_ptr).view().owning_container,
                    )
            },
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).endpoint_map.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id()
                == old(self).endpoint_map.spec_index(endpoint_ptr)
                    .locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).lock_id_set() =~= set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
                old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                old(self).thread_map.lock_id_by_key(thread_ptr),
            ],
            !set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
            ].contains(old(self).endpoint_map.lock_id_by_key(endpoint_ptr)),
            !set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
                old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
            ].contains(old(self).thread_map.lock_id_by_key(thread_ptr)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
            final(self).endpoint_map.spec_index(endpoint_ptr).view().owning_threads
                .view().contains((thread_ptr, 0)),
            final(self).endpoint_map.spec_index(endpoint_ptr).view().rf_counter
                == old(self).endpoint_map.spec_index(endpoint_ptr).view().rf_counter + 1,
            final(self).thread_map.spec_index(thread_ptr).being_killed()
                == old(self).thread_map.spec_index(thread_ptr).being_killed(),
            final(self).thread_map.spec_index(thread_ptr).view().state
                == old(self).thread_map.spec_index(thread_ptr).view().state,
            final(self).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).locking_thread() is None,
            final(self).endpoint_map.spec_index(endpoint_ptr).locking_thread() is None,
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            final(self).thread_map.spec_index(current_thread_ptr)
                == old(self).thread_map.spec_index(current_thread_ptr),
            final(self).endpoint_map.unchanged_except(&old(self).endpoint_map, endpoint_ptr),
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).page_array == old(self).page_array,
            final(self).cpu_array == old(self).cpu_array,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).process_map == old(self).process_map,
            final(self).allocator_4k_map == old(self).allocator_4k_map,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).default_pagetable == old(self).default_pagetable,
            final(self).cpu_array.lock_id_by_index(cpu_id)
                == old(self).cpu_array.lock_id_by_index(cpu_id),
            final(self).scheduler_map.lock_id_by_key(scheduler_ptr)
                == old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).thread_map.lock_id_by_key(current_thread_ptr)
                == old(self).thread_map.lock_id_by_key(current_thread_ptr),
            final(self).page_array.lock_id_by_index(page_index)
                == old(self).page_array.lock_id_by_index(page_index),
            final(lctx).wf(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set()
                .remove(old(self).thread_map.lock_id_by_key(thread_ptr))
                .remove(old(self).endpoint_map.lock_id_by_key(endpoint_ptr)),
            final(lctx).lock_id_set() =~= set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
            ],
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
    {
        proof {
            assert({
                &&& self.thread_map.perms_wf()
                &&& self.endpoint_map.perms_wf()
                &&& self.thread_map.spec_index(thread_ptr).view()
                    .endpoint_descriptors.wf()
                &&& self.endpoint_map.spec_index(endpoint_ptr).inv()
            }) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); };
            assert(!self.endpoint_map.spec_index(endpoint_ptr).view().owning_threads
                .view().contains((thread_ptr, 0))) by { reveal(thread_endpoint_ref_counter_wf); };
        }
        {
            let thread_mut = self.thread_map.borrow_mut(
                thread_ptr, Tracked(&*lctx), Tracked(&thread_lock_perm),
            );
            thread_mut.endpoint_descriptors.set(0, Some(endpoint_ptr));
        }
        {
            let endpoint_mut = self.endpoint_map.borrow_mut(
                endpoint_ptr, Tracked(&*lctx), Tracked(&endpoint_lock_perm),
            );
            proof {
                assert(endpoint_mut.rf_counter < NUM_PAGES) by { endpoint_ref_counter_bounded(&*endpoint_mut); };
            }
            endpoint_mut.rf_counter = endpoint_mut.rf_counter + 1;
            endpoint_mut.owning_threads = Ghost(
                endpoint_mut.owning_threads@.insert((thread_ptr, 0)),
            );
        }

        proof {
            assert(self.subsystems_inv()) by {
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(threads_inv); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                assert(endpoint_perms_wf(self.endpoint_map)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
                reveal(KernelK::default_pagetable_wf);
            };
            assert(self.memory_management_inv()) by {
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { reveal(thread_pages_wf); };
                assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by { thread_staged_pages_4k_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); thread_staged_pages_2m_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); thread_staged_pages_1g_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { reveal(endpoint_pages_wf); };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(thread_quota_4k_fields_unchanged); reveal(thread_quota_2m_fields_unchanged); reveal(thread_quota_1g_fields_unchanged); container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields_forall(); container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall(); container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall(); };
            };
            assert(self.process_management_inv()) by {
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_ref_counter_wf); };
                assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_queue_fields_unchanged); reveal(endpoint_queue_fields_unchanged); thread_endpoint_queue_wf_preserved_for_queue_fields(old(self).thread_map, self.thread_map, old(self).endpoint_map, self.endpoint_map); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { reveal(endpoint_owning_container_fields_unchanged); thread_endpoint_reference_added_from_single_update(old(self).thread_map, self.thread_map, thread_ptr, endpoint_ptr); container_thread_endpoint_wf_preserved_on_reference_add(self.container_map, old(self).thread_map, self.thread_map, old(self).endpoint_map, self.endpoint_map, thread_ptr, endpoint_ptr); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by { reveal(container_thread_scheduler_wf); };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { reveal(thread_cpu_wf); };
            };
            assert(self.locked_objects_match_lctx(&*lctx)) by { reveal(thread_locked_match_lctx); reveal(endpoint_locked_match_lctx); };
            assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); reveal(page_lock_id_aligned); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            assert(self.endpoint_map.lock_id_by_key(endpoint_ptr)
                == old(self).endpoint_map.lock_id_by_key(endpoint_ptr)) by { lock_id_fields_eq_imply_eq(); };
            assert(self.thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr)) by { lock_id_fields_eq_imply_eq(); };
            assert_sets_equal!(lctx.lock_id_set() == set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
                old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                old(self).thread_map.lock_id_by_key(thread_ptr),
            ], lock_id => {});
        }
        self.wunlock_thread(
            thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm),
        );
        proof {
            broadcast use vstd::set::group_set_lemmas;
            assert_sets_equal!(lctx.lock_id_set() == set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
                old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
            ], lock_id => {});
            assert(self.endpoint_map.lock_id_by_key(endpoint_ptr)
                == old(self).endpoint_map.lock_id_by_key(endpoint_ptr)) by { lock_id_fields_eq_imply_eq(); };
        }
        self.wunlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm),
        );
        proof {
            broadcast use vstd::set::group_set_lemmas;
            assert_sets_equal!(lctx.lock_id_set() == set![
                old(self).cpu_array.lock_id_by_index(cpu_id),
                old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                old(self).process_map.lock_id_by_key(process_ptr),
                old(self).thread_map.lock_id_by_key(current_thread_ptr),
                old(self).page_array.lock_id_by_index(page_index),
            ], lock_id => {});
            assert(self.thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr)) by { lock_id_fields_eq_imply_eq(); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
    }
}

}

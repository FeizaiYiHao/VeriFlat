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
                // Error paths are user-view no-ops; the Success path grows the
                // running process's owned_threads (a real user-view change).
                //@Xiangdong the Success-path `old_u == entry projection` clause is
                // dropped for now: the commit calls `allocate_free_4k_page`, which
                // crosses an internal `kernel_step_boundary`, so the concurrent
                // world can move an UNHELD process's projection before the user-view
                // step opens — the step's `old_u` is the projection at the
                // linearization point (post-alloc), not at syscall entry. Awaiting
                // the linearization-contract decision.
                !(ret is Success) ==> final(steps).steps.last().old_u == final(steps).steps.last().new_u,
                // Success-path: one user-visible atomic step that decreases
                // the running process's quota_4k by 1 and grows owned_threads by 1.
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
                    || ret is ErrorNoQuota
                    || ret is Error,
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
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
            proof {
                crate::kernel::implementation::syscall_alloc_quota::all_unlocked_imply_locked_objects_match_lctx(&*self, &lctx);
            }

            // ---- Lock #1: the running cpu. ----
            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();

            // The process's container + scheduler are fixed by rodata (immutable,
            // lock-free readable): read them before taking the process lock so the
            // scheduler (major 103) can be acquired ahead of the process (105).
            let proc_container = self.process_map.borrow_rodata(process_ptr).borrow().owning_container;
            proof {
                reveal(container_process_wf);
                assert(self.container_map.dom().contains(proc_container));
            }
            let scheduler_ptr = self.container_map.borrow_rodata(proc_container).borrow().scheduler;

            // ---- Lock #2: the container's scheduler (below the process). ----
            proof {
                reveal(container_scheduler_wf);
                assert(self.scheduler_map.dom().contains(scheduler_ptr));
                assert(self.scheduler_map.spec_index(scheduler_ptr).locked_by(&lctx@) == false) by {
                    reveal(scheduler_objects_unlocked);
                    reveal(KernelK::all_objects_unlocked);
                    assert(self.scheduler_map.spec_index(scheduler_ptr) == old(self).scheduler_map.spec_index(scheduler_ptr));
                    assert(old(self).all_objects_unlocked(&entry_lctx));
                    assert(old(self).scheduler_map.spec_index(scheduler_ptr).locked_by(&entry_lctx) == false);
                };
                let sched_lock_id = LockId{
                    container: self.scheduler_map.spec_index(scheduler_ptr).container_depth(),
                    process: self.scheduler_map.spec_index(scheduler_ptr).process_depth(),
                    major: self.scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                    minor: scheduler_ptr,
                };
                assert(sched_lock_id.major == SCHEDULER_LOCK_MAJOR) by { reveal(scheduler_perms_wf); };
                assert(lctx@.obj_id_fresh(KernelObjId::Scheduler(scheduler_ptr)));
                assert(lctx@.lock_id_acyclic(sched_lock_id)) by { reveal(cpu_locked_match_lctx); };
            }
            let Tracked(scheduler_lock_perm) = self.wlock_scheduler(scheduler_ptr, Tracked(&mut lctx));

            // ---- Lock #3: the running process (kill-aware). ----
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
                    reveal(scheduler_perms_wf);
                    assert(lctx@.lock_map().dom() =~= set![ KernelObjId::Cpu(cpu_id), KernelObjId::Scheduler(scheduler_ptr) ]);
                }
                self.release_cpu_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id,
                    scheduler_ptr,
                    Tracked(cpu_lock_perm),
                    Tracked(scheduler_lock_perm),
                );
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();

            proof {
                assert(lctx@.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Scheduler(scheduler_ptr),
                    KernelObjId::Process(process_ptr),
                ]);
            }

            // ---- Quota check: the process needs at least one 4k page. ----
            let process_ref = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            if process_ref.quota_4k < 1 {
                proof { reveal(scheduler_perms_wf); }
                self.release_cpu_and_process_and_finish(
                    Tracked(lctx.get()),
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

            // ===== QUOTA SUFFICIENT — allocate a page, retype it into a thread, ====
            // ===== wire it in, release all locks, and close the user-view step. ====
            // Locking cpu + scheduler + process changed only lock state, so the
            // user-view projection is unchanged from entry: the snap_shot the
            // commit needs still equals the current projection.
            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            }
            self.add_new_thread_to_proc_container_and_scheduler(
                Tracked(lctx.get()),
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

        /// Commit a new thread on the success path: allocate a 4k page from the
        /// process's container allocator (the page comes back staged Owned4k +
        /// still write-locked, riding across alloc's internal boundary), open a
        /// user-view step, `create_thread_from_staged_page` (retype + wire into
        /// scheduler / process / container sets — the real user-view change),
        /// release every lock (thread, page, scheduler, process, cpu), and close
        /// the step.
        ///
        /// Entry holds cpu + scheduler + process (the scheduler, major 103, was
        /// acquired ahead of the process so it sits BELOW the staged page — major
        /// FREE_PAGE_LOCK_MAJOR — which is locked inside `allocate_free_4k_page`).
        #[verifier::spinoff_prover]
        fn add_new_thread_to_proc_container_and_scheduler(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
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
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Scheduler(scheduler_ptr),
                    KernelObjId::Process(process_ptr),
                ],
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(self).cpu_array.inv(),
                scheduler_lock_perm@.state() is WriteLock,
                scheduler_lock_perm@.thread_id() == lctx.thread_id(),
                scheduler_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Scheduler(scheduler_ptr)],
                scheduler_lock_perm@.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Process(process_ptr)],
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                old(self).process_map.spec_index(process_ptr).view().quota_4k >= 1,
                old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                cpu_lock_perm@.lock_id().major == CPU_LOCK_MAJOR_RUNNING,
                scheduler_lock_perm@.lock_id().major == SCHEDULER_LOCK_MAJOR,
                process_lock_perm@.lock_id().major == PROCESS_LOCK_MAJOR,
                old(self).locked_objects_match_lctx(&lctx),
            ensures
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // User-visible change: quota_4k decreased, owned_threads grew.
                final(steps).steps.last().new_u.process_map[process_ptr].quota_4k
                    == final(steps).steps.last().old_u.process_map[process_ptr].quota_4k - 1,
                final(steps).steps.last().new_u.process_map[process_ptr].owned_threads.len()
                    == final(steps).steps.last().old_u.process_map[process_ptr].owned_threads.len() + 1,
                // Full U-change description.
                kernel_u_new_thread_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                ),
        {
            let tracked mut process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();
            let ghost entry_steps_len = steps.steps.len();
            let ghost entry_self = *self;

            proof { reveal(container_perms_wf); }
            let alloc_ptr_4k = self.container_map.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;

            // ---- allocate_free_4k_page preconditions ----
            proof {
                reveal(container_process_wf);
                reveal(container_allocator_wf);
                assert(self.container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr));
                assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k));
                assert(process_effective_quota_4k(self.process_map.spec_index(process_ptr)) >= 1);
                crate::kernel::implementation::allocate_free_4k_page::lemma_effective_quota_ge_1_imply_total_free_pages_pos(self, container_ptr, alloc_ptr_4k, process_ptr);
                assert forall|obj_id: KernelObjId| #![auto]
                    lctx.lock_map().dom().contains(obj_id)
                    implies {
                        &&& obj_id is AllocatorCache == false
                        &&& obj_id is AllocatorGlobalPoll == false
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[0].lock_id().spec_gt(lctx.lock_map().spec_index(obj_id))
                    } by {
                    reveal(allocator_perms_wf);
                    let held = lctx.lock_map()[obj_id];
                    let cache_id = self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[0].lock_id();
                    assert(cache_id.major == ALLOCATOR_CACHE_MAJOR);
                };
            }

            // Allocate: stage a fresh 4k page, leaving its slot write-locked (major
            // FREE_PAGE_LOCK_MAJOR, above the scheduler — hence the scheduler was
            // taken earlier). The perm rides back so we can retype without re-locking.
            let (page_ptr, Tracked(page_lock_perm)) = self.allocate_free_4k_page(
                alloc_ptr_4k, process_ptr, container_ptr, cpu_id,
                Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&process_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);

            // Open the user-view step (the retype below is the real U-change; alloc
            // staged the page but that projects to nothing).
            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                // old_u is the U projection of the K state at begin time.
                assert(steps.steps.last().old_u == kernel_k_to_kernel_u(*self));
            }

            // ---- create_thread_from_staged_page preconditions ----
            // The container's rodata (scheduler ptr) is immutable, so it survives
            // alloc's internal boundary — the entry `container.rodata.scheduler ==
            // scheduler_ptr` still holds; the tree-shape facts are re-derived from
            // post-alloc inv().
            proof {
                reveal(container_uppertree_seq_wf);
                reveal(container_tree_wf);
                reveal(container_tree_fields_wf);
                assert(self.container_map.dom().contains(container_ptr));
                assert(self.container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr);
                assert forall|i: int| #![auto]
                    0 <= i < self.container_map.spec_index(container_ptr).view().uppertree_seq.view().len()
                    implies self.container_map.dom().contains(self.container_map.spec_index(container_ptr).view().uppertree_seq.view()[i]) by {
                    assert(self.container_map.spec_index(container_ptr).view().uppertree_seq.view().contains(
                        self.container_map.spec_index(container_ptr).view().uppertree_seq.view()[i]));
                };
                assert(self.thread_map.dom().contains(page_ptr) == false) by {
                    reveal(thread_pages_wf);
                };
                // Thread(page_ptr) is fresh: if it were held, locked_objects_match_lctx
                // would place page_ptr in thread_map.dom, which the line above refutes.
                assert(lctx.obj_id_fresh(KernelObjId::Thread(page_ptr))) by {
                    reveal(thread_locked_match_lctx);
                };
                // push_tail overflow guards: thread / queue counts are bounded by NUM_PAGES.
                lemma_inv_imply_owned_threads_len_bounded(&*self, process_ptr);
                lemma_inv_imply_scheduler_queue_len_bounded(&*self, scheduler_ptr);
                // The scheduler stayed held across alloc (its lock_map key survived),
                // so its dom + write-lock state + being_killed carry over.
                assert(self.scheduler_map.dom().contains(scheduler_ptr));
                assert(self.scheduler_map.spec_index(scheduler_ptr).wlocked_by(&*lctx)) by {
                    reveal(scheduler_locked_match_lctx);
                };
                assert(self.scheduler_map.spec_index(scheduler_ptr).being_killed() == false) by {
                    reveal(scheduler_perms_wf);
                };
                assert(scheduler_lock_perm.lock_id() == self.scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id) by {
                    reveal(scheduler_locked_match_lctx);
                };
                // The process entered temp_alloc_clean (empty caches); alloc staged
                // exactly page_ptr into the 4k cache, so it is now {page_ptr} and
                // the 2m/1g caches are still empty.
                assert(entry_self.process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= Set::<PagePtr>::empty()) by {
                    reveal(process_perms_wf);
                    entry_self.process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().lemma_len0_is_empty();
                };
                assert(self.process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= Set::<PagePtr>::empty().insert(page_ptr));
                assert(self.process_map.spec_index(process_ptr).view().temp_alloc_cache_2m.view().len() == 0);
                assert(self.process_map.spec_index(process_ptr).view().temp_alloc_cache_1g.view().len() == 0);
            }
            let (thread_ptr, Tracked(thread_lock_perm)) = self.create_thread_from_staged_page(
                page_ptr, process_ptr, container_ptr, scheduler_ptr,
                Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(&process_lock_perm), Tracked(&scheduler_lock_perm),
            );

            // Release every lock (reverse acquire order): thread, page, scheduler,
            // process, cpu.
            let ghost k_post_create = *self;
            proof {
                // All lock_map membership + values + held lock state from
                // locked_objects_match_lctx (thread_id preserved through alloc +
                // wlock_scheduler + begin_user_view_step, so each perm still matches).
                reveal(thread_locked_match_lctx);
                reveal(page_locked_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(cpu_locked_match_lctx);
                reveal(scheduler_perms_wf);
                reveal(process_perms_wf);
                // The cpu key is held now (entry lock_map was {Cpu,Scheduler,Process};
                // alloc added Page, create_thread added Thread), and it survives the
                // four unlocks below (each removes only its own key), giving
                // wunlock_cpu its precondition.
                assert(lctx.lock_map().dom().contains(KernelObjId::Cpu(cpu_id)));
                assert(self.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx));
            }
            self.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
            self.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            self.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            proof { reveal(cpu_locked_match_lctx); }
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            // Close the user-view step.
            proof {
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                // new_u == kernel_k_to_kernel_u(k_post_create) because wunlock
                // only changes lock state (framing lemma).
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&k_post_create, self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(k_post_create));
                // old_u == kernel_k_to_kernel_u(old(self_of_create)) from begin_user_view_step.
                // create_thread ensures: kernel_u_new_thread_changed(
                //     kernel_k_to_kernel_u(old(self_of_create)),
                //     kernel_k_to_kernel_u(k_post_create),
                //     process_ptr)
                // Therefore: kernel_u_new_thread_changed(old_u, new_u, process_ptr).
                assert(kernel_u_new_thread_changed(
                    steps.steps.last().old_u,
                    steps.steps.last().new_u,
                    process_ptr,
                ));
            }
        }

        /// Helper: open a user-view step, release the scheduler then the cpu, and
        /// close the step. Used on the process-killed path, where the cpu +
        /// scheduler were write-locked (the `wlock_process_unless_killed` attempt
        /// failed as a complete no-op).
        #[verifier::spinoff_prover]
        fn release_cpu_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
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
                lctx.lock_map().dom() =~= set![ KernelObjId::Cpu(cpu_id), KernelObjId::Scheduler(scheduler_ptr) ],
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm.view().lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
                scheduler_lock_perm.view().state() is WriteLock,
                scheduler_lock_perm.view().thread_id() == lctx.thread_id(),
                scheduler_lock_perm.view().lock_id() == lctx.lock_map()[KernelObjId::Scheduler(scheduler_ptr)],
                scheduler_lock_perm.view().lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(self).scheduler_map.spec_index(scheduler_ptr).inv(),
                old(self).locked_objects_match_lctx(&lctx),
            ensures
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();

            let ghost entry_steps_len = steps.steps.len();

            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            self.wunlock_scheduler(scheduler_ptr, Tracked(&mut lctx), Tracked(scheduler_lock_perm));
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));

            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            }
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }

        /// Helper: open a user-view step, release scheduler then process then cpu
        /// (reverse of acquire order), and close the step.
        #[verifier::spinoff_prover]
        fn release_cpu_and_process_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
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
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Scheduler(scheduler_ptr),
                    KernelObjId::Process(process_ptr),
                ],
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
                scheduler_lock_perm@.state() is WriteLock,
                scheduler_lock_perm@.thread_id() == lctx.thread_id(),
                scheduler_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Scheduler(scheduler_ptr)],
                scheduler_lock_perm@.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(self).scheduler_map.spec_index(scheduler_ptr).inv(),
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Process(process_ptr)],
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr).inv(),
                old(self).process_map.perms_wf(),
                // Temp-alloc must be drained before the process is unlocked (the
                // "flushed before wunlock" protocol; required by wunlock_process).
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                old(self).locked_objects_match_lctx(&lctx),
            ensures
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked process_lock_perm = process_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();

            let ghost entry_steps_len = steps.steps.len();

            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            self.wunlock_scheduler(scheduler_ptr, Tracked(&mut lctx), Tracked(scheduler_lock_perm));
            self.wunlock_process(process_ptr, Tracked(&mut lctx), Tracked(process_lock_perm));
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));

            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            }
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }

        /// Create a thread from a staged 4k page: retype the page to a Thread,
        /// wire it into the scheduler queue, the process's `owned_threads`
        /// linkedlist, and the container ghost sets (direct + ancestors), then
        /// re-establish `inv()`. Consumes one 4k of the process's quota (the page
        /// becomes the thread). Leaves the thread write-locked; the caller unlocks
        /// the thread + page + scheduler + containers afterward.
        ///
        /// SKELETON (not external_body): the `retype_*` call is LIVE (its
        /// preconditions are really discharged); the wiring (scheduler push_tail,
        /// owned_threads push_tail, per-ancestor container ghost-set inserts) and
        /// the `inv()` re-establishment are ASSUMED for now (`//@Xiangdong`), the
        /// hard-but-provable proofs deferred per the grind plan. Preconditions
        /// state the mid-syscall context (process + page write-locked, page staged,
        /// quota available, fresh thread lock id); the syscall wiring that acquires
        /// the container chain + scheduler is a separate step.
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
                old(lctx).obj_id_fresh(KernelObjId::Thread(page_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                final(self).inv(),
                ret.0 == page_ptr,
                final(self).thread_map.dom().contains(page_ptr),
                final(self).thread_map.spec_index(page_ptr).wlocked_by(final(lctx)),
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(self).thread_map.spec_index(page_ptr).locking_thread()->Write_lock_id,
                // ---- the created thread: fresh, pending-clean, owning the given container (for wunlock_thread) ----
                final(self).thread_map.spec_index(page_ptr).view().free_quota_pending_clean(),
                final(self).thread_map.spec_index(page_ptr).view().owning_container == container_ptr,
                final(self).thread_map.spec_index(page_ptr).being_killed() == false,
                // ---- process: still write-locked, page consumed so temp-alloc is clean again (for wunlock_process) ----
                final(self).process_map.dom().contains(process_ptr),
                final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(self).process_map.spec_index(process_ptr).being_killed() == false,
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                // ---- quota + thread_map growth (visible user-view changes) ----
                final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k - 1,
                final(self).thread_map.dom() =~= old(self).thread_map.dom().insert(page_ptr),
                // ---- owned_threads grew (visible in KernelU) ----
                final(self).process_map.spec_index(process_ptr).view().owned_threads.view().len()
                    == old(self).process_map.spec_index(process_ptr).view().owned_threads.view().len() + 1,
                // ---- U-change: the user-view projection changed as described ----
                kernel_u_new_thread_changed(
                    kernel_k_to_kernel_u(*old(self)),
                    kernel_k_to_kernel_u(*final(self)),
                    process_ptr,
                ),
                process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                // ---- scheduler: still write-locked (caller unlocks it) ----
                final(self).scheduler_map.dom().contains(scheduler_ptr),
                final(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
                final(self).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                scheduler_lock_perm.lock_id() == final(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                // ---- page slot: still write-locked (caller unlocks it) ----
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(final(lctx)),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                page_lock_perm.lock_id() == final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                // ---- lctx agreement preserved (for the caller's unlock chain) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                // ---- cpu_array untouched + lock_map only gained Thread(page_ptr) (for the caller's cpu unlock) ----
                final(self).cpu_array == old(self).cpu_array,
                final(lctx).lock_map() =~= old(lctx).lock_map().insert(KernelObjId::Thread(page_ptr), ret.1.view().lock_id()),
        {
            let ghost uppers = old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view();

            // ---- LIVE: retype the staged page into a freshly-initialized thread ----
            proof {
                assert(old(self).container_map.spec_index(container_ptr).view().uppertree_seq.view().len()
                    == old(self).container_map.spec_index(container_ptr).view_rodata().view().depth) by {
                    reveal(container_perms_wf);
                    reveal(container_tree_fields_wf);
                };
                // The page is Owned4k ⟹ perm_4k is Some (by perm_inv).
                reveal(page_array_wf);
                assert(self.page_array.spec_index(page_ptr2page_index(page_ptr)).view().inv());
                assert(self.page_array.spec_index(page_ptr2page_index(page_ptr)).view().is_init());
                assert(self.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k@.is_some());
                // Establish preconditions for retype_staged_page_to_thread.
                assert(self.container_map.perms_wf()) by { reveal(container_perms_wf); };
                assert(self.process_map.perms_wf()) by { reveal(process_perms_wf); };
                assert(self.thread_map.perms_wf()) by { reveal(thread_perms_wf); };
                assert(self.page_array.inv());
            }
            let Tracked(thread_perm) = self.retype_staged_page_to_thread(
                page_ptr, process_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(page_lock_perm), Tracked(process_lock_perm),
            );

            // LIVE: add the thread to its container's owned_threads and to every
            // ancestor's owned_indirect_threads (the container-set delta).
            proof {
                assert(self.container_map.perms_wf()) by { reveal(container_perms_wf); };
                add_thread_to_container_sets(
                    &mut self.container_map, container_ptr, page_ptr,
                    uppers,
                );
            }

            // LIVE: link the thread into the process's owned_threads. Take the
            // thread's proc_linkedlist_node (its value set to page_ptr), then
            // push_tail onto the process list keyed by the node's address.
            proof {
                assert(old(self).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) == false) by {
                    reveal(process_thread_wf);
                    if old(self).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) {
                        assert(old(self).thread_map.spec_index(page_ptr).view().owning_proc == process_ptr);
                    }
                }
            }
            let thread_mut = self.thread_map.borrow_mut(page_ptr, Tracked(&*lctx), Tracked(&thread_perm));
            let (node_addr, mut node_perm) = thread_mut.proc_linkedlist_node.take();
            node_update_value(node_addr, &mut node_perm, page_ptr);
            let process_mut = self.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
            proof {
                reveal(LinkedList::wf_value_list);
                assert(process_mut.owned_threads.view().contains(page_ptr) == false);
            }
            let ghost pre_push_owned = process_mut.owned_threads;
            process_mut.owned_threads.push_tail(node_addr, node_perm);

            // LIVE: push the thread onto the container's scheduler queue, then
            // flip its state to SCHEDULED.
            let (sched_node_addr, mut sched_node_perm) = thread_mut.scheduler_linkedlist_node.take();
            node_update_value(sched_node_addr, &mut sched_node_perm, page_ptr);
            proof {
                reveal(scheduler_perms_wf);
            }
            let scheduler_mut = self.scheduler_map.borrow_mut(scheduler_ptr, Tracked(&*lctx), Tracked(scheduler_lock_perm));
            proof {
                reveal(container_thread_scheduler_wf);
            }
            let ghost pre_push_queue = scheduler_mut.queue;
            scheduler_mut.queue.push_tail(sched_node_addr, sched_node_perm);
            thread_mut.state = ThreadState::SCHEDULED;

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(allocator_perms_wf(self.allocator_2m_map)) by { reveal(allocator_perms_wf); };
                assert(allocator_perms_wf(self.allocator_1g_map)) by { reveal(allocator_perms_wf); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(threads_inv); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(page_array_wf(self.page_array)) by { reveal(page_array_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(scheduler_perms_wf); };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
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
                            *old(self), *self, container_ptr, page_ptr, uppers,
                        );
                    };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
                    assert(self.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                    assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                        reveal(page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                        reveal(pagetable_perms_wf); reveal(pagetables_inv); page_ptr_lemma1();
                    };
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                    assert(thread_pages_wf(self.thread_map, self.page_array)) by { reveal(thread_pages_wf); };
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
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(per_container_process_tree_wf); reveal(container_process_wf);
                        per_container_process_tree_wf_preserved_for_tree_fields_eq(self.container_map, old(self).process_map, self.process_map);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_ref_counter_wf); };
                    assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_queue_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_thread_endpoint_wf);
                        reveal(thread_endpoint_ref_counter_wf);
                        reveal(container_endpoint_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_scheduler_wf);
                        reveal(container_thread_wf);
                        reveal(container_scheduler_wf);
                        pre_push_queue.lemma_map_dom();
                        seq_push_lemma::<RwLockThreadPtr>();
                    };
                    assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { reveal(thread_cpu_wf); };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        container_thread_wf_preserved_on_thread_add(
                            old(self).container_map, self.container_map, old(self).thread_map, self.thread_map,
                            container_ptr, page_ptr, uppers,
                        );
                    };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by {
                        reveal(process_thread_wf);
                        assert(process_thread_wf(old(self).process_map, old(self).thread_map));
                        pre_push_owned.lemma_map_dom();
                        assert(self.process_map.spec_index(process_ptr).view().owned_threads.map()
                            =~= old(self).process_map.spec_index(process_ptr).view().owned_threads.map().insert(node_addr, page_ptr));
                        assert forall|p2: RwLockProcessPtr, t2: RwLockThreadPtr|
                            #![trigger self.process_map.spec_index(p2).view(), self.thread_map.spec_index(t2).view()]
                            self.process_map.dom().contains(p2) && self.process_map.spec_index(p2).view().owned_threads.view().contains(t2)
                            implies
                                self.thread_map.dom().contains(t2) && self.thread_map.spec_index(t2).view().owning_proc == p2
                                && self.thread_map.spec_index(t2).view().proc_pagetable_ptr == self.process_map.spec_index(p2).view().pagetable
                                && self.process_map.spec_index(p2).view().owned_threads.map().dom().contains(self.thread_map.spec_index(t2).view().proc_linkedlist_node.addr())
                                && self.process_map.spec_index(p2).view().owned_threads.map().spec_index(self.thread_map.spec_index(t2).view().proc_linkedlist_node.addr()) == t2
                        by {
                            if !(p2 == process_ptr && t2 == page_ptr) {
                                assert(old(self).process_map.spec_index(p2).view().owned_threads.view().contains(t2));
                                assert(t2 != page_ptr);
                                assert(old(self).process_map.spec_index(p2).view().owned_threads.map().dom().contains(old(self).thread_map.spec_index(t2).view().proc_linkedlist_node.addr()));
                            }
                        };
                        seq_push_lemma::<RwLockThreadPtr>();
                        assert(self.process_map.spec_index(process_ptr).view().owned_threads.view()
                            =~= old(self).process_map.spec_index(process_ptr).view().owned_threads.view().push(page_ptr));
                    };
                };
                assert(self.inv());
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
            // Prove the U-change postcondition.
            proof {
                let pre_u = kernel_k_to_kernel_u(*old(self));
                let post_u = kernel_k_to_kernel_u(*self);
                // cpu_array unchanged (ensures: final.cpu_array == old.cpu_array).
                assert(post_u.cpu_array =~= pre_u.cpu_array);
                // process_map domain unchanged.
                assert(post_u.process_map.dom() =~= pre_u.process_map.dom());
                // process_ptr in domain.
                assert(pre_u.process_map.dom().contains(process_ptr));
                // quota_4k decreased by 1.
                assert(post_u.process_map[process_ptr].quota_4k as int
                    == pre_u.process_map[process_ptr].quota_4k as int - 1);
                // owned_threads grew by 1 (push_tail preserves prefix).
                assert(post_u.process_map[process_ptr].owned_threads.len()
                    == pre_u.process_map[process_ptr].owned_threads.len() + 1);
                assert(post_u.process_map[process_ptr].owned_threads.subrange(
                    0, pre_u.process_map[process_ptr].owned_threads.len() as int)
                    == pre_u.process_map[process_ptr].owned_threads);
                // Other fields of process_ptr preserved.
                assert(post_u.process_map[process_ptr].pagetable == pre_u.process_map[process_ptr].pagetable);
                assert(post_u.process_map[process_ptr].quota_2m == pre_u.process_map[process_ptr].quota_2m);
                assert(post_u.process_map[process_ptr].quota_1g == pre_u.process_map[process_ptr].quota_1g);
                assert(post_u.process_map[process_ptr].parent == pre_u.process_map[process_ptr].parent);
                assert(post_u.process_map[process_ptr].children == pre_u.process_map[process_ptr].children);
                assert(post_u.process_map[process_ptr].depth == pre_u.process_map[process_ptr].depth);
                assert(post_u.process_map[process_ptr].uppertree_seq == pre_u.process_map[process_ptr].uppertree_seq);
                assert(post_u.process_map[process_ptr].subtree_set == pre_u.process_map[process_ptr].subtree_set);
                assert(post_u.process_map[process_ptr].killed == pre_u.process_map[process_ptr].killed);
                // Other processes unchanged.
                assert(forall|p: RwLockProcessPtr|
                    #![trigger post_u.process_map[p]]
                    pre_u.process_map.dom().contains(p) && p != process_ptr
                    ==> post_u.process_map[p] == pre_u.process_map[p]);
            }
            (page_ptr, Tracked(thread_perm))
        }

        /// TCB: reinterpret a staged 4k page as a fresh Thread object.
        ///
        /// The page at `page_ptr` is currently `Owned4k{process_ptr}` (freshly
        /// allocated, staged in the process's `temp_alloc_cache_4k`) and its
        /// slot is write-locked. This trusted primitive atomically:
        ///   1. flips the page state `Owned4k{process_ptr}` → `Allocated4k{AsThread}`
        ///      (the page's memory now backs a Thread — establishes the
        ///      `thread_pages_wf` page↔thread_map coupling);
        ///   2. UNSTAGES the page from the process (`temp_alloc_cache_4k.remove`)
        ///      AND decrements `quota_4k` by 1 — so `process_effective_quota_4k`
        ///      (= quota_4k − temp_alloc_cache_4k.len()) is UNCHANGED, keeping the
        ///      process side of the conservation law fixed as the page is consumed;
        ///   3. INITIALIZES the Thread in the page's memory (atmosphere-style: no
        ///      by-value `Thread` crosses the boundary — the TCB writes the fields
        ///      behind the raw pointer): owner/pagetable/depth fields copied from
        ///      the held process + its container, both linkedlist nodes fresh
        ///      (init), all endpoint descriptors None, pendings zero, state
        ///      neither BLOCKED nor SCHEDULED (the caller pushes it onto the
        ///      scheduler queue and flips it SCHEDULED);
        ///   4. grows `thread_map` at key = `page_ptr` with that thread,
        ///      write-locked by the caller, registering `Thread(page_ptr)` in lctx.
        ///
        /// It does NOT re-establish `inv()`: the new thread is in `thread_map`
        /// but not yet wired into the process's `owned_threads` linkedlist or the
        /// container ghost sets, so `process_thread_wf` / `container_thread_wf`
        /// are transiently broken — the caller finishes the wiring and
        /// re-establishes `inv()`. The page slot stays write-locked (caller holds
        /// `page_lock_perm`); the caller `wunlock_page`s it afterward.
        ///
        /// Registering `Thread(page_ptr)` is a MINT, not an acquire: the page is
        /// exclusively ours (staged in our `temp_alloc_cache_4k`, slot
        /// write-locked), so no other thread can contend on `Thread(page_ptr)`
        /// and no wait cycle is possible — deadlock-freedom needs no
        /// `lock_id_acyclic` here, only `lock_map` key freshness. Later acquires
        /// in the same atomic section still check acyclicity against the
        /// registered thread id at their own wlock sites.
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
                // Page slot is write-locked and currently a staged Owned4k of this process.
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(old(lctx)),
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().is_init(),
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Owned4k{ process_ptr }),
                page_lock_perm.state() is WriteLock,
                page_lock_perm.thread_id() == old(lctx).thread_id(),
                page_lock_perm.lock_id() == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                // Process is write-locked and has the page staged, with quota to spend.
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == old(lctx).thread_id(),
                process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
                old(self).process_map.spec_index(process_ptr).view().quota_4k >= 1,
                // Fresh thread lock id: a mint, not an acquire (see doc).
                old(lctx).obj_id_fresh(KernelObjId::Thread(page_ptr)),
                // The page's physical memory perm is present (Owned4k ⟹ perm_4k is Some).
                old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k@.is_some(),
            ensures
                // ---- page_array: only the target slot's state flipped to AsThread; slot inv() + lock state preserved ----
                final(self).page_array.inv(),
                final(self).page_array.view().len() == old(self).page_array.view().len(),
                final(self).page_array.unchanged_except(&old(self).page_array, page_ptr2page_index(page_ptr)),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Allocated4k{ state: Allocated4KPageState::AsThread }),
                // The page's physical memory perm has been consumed by the retype.
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k@.is_none(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed()
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container,
                final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().addr
                    == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().addr,

                // ---- process: unstaged + quota decremented, so effective_quota is UNCHANGED; every other payload field held ----
                final(self).process_map.dom() == old(self).process_map.dom(),
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
                final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k - 1,
                process_effective_quota_4k(final(self).process_map.spec_index(process_ptr))
                    == process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)),
                final(self).process_map.spec_index(process_ptr).view().pcid
                    == old(self).process_map.spec_index(process_ptr).view().pcid,
                final(self).process_map.spec_index(process_ptr).view().ioid
                    == old(self).process_map.spec_index(process_ptr).view().ioid,
                final(self).process_map.spec_index(process_ptr).view().pagetable
                    == old(self).process_map.spec_index(process_ptr).view().pagetable,
                final(self).process_map.spec_index(process_ptr).view().iommu_table
                    == old(self).process_map.spec_index(process_ptr).view().iommu_table,
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

                // ---- thread_map: grew by exactly page_ptr, write-locked, holding the freshly-initialized thread ----
                final(self).thread_map.dom() =~= old(self).thread_map.dom().insert(page_ptr),
                forall|t:RwLockThreadPtr|
                    #![auto]
                    old(self).thread_map.dom().contains(t)
                    ==>
                    final(self).thread_map[t] == old(self).thread_map[t],
                final(self).thread_map.dom().contains(page_ptr),
                final(self).thread_map.spec_index(page_ptr).is_init(),
                final(self).thread_map.spec_index(page_ptr).being_killed() == false,
                final(self).thread_map.spec_index(page_ptr).locking_thread() == (RwLockState::Write {
                    thread_id: final(lctx).thread_id(),
                    lock_id: final(self).thread_map.lock_id_by_key(page_ptr),
                }),
                final(self).thread_map.lock_id_by_key(page_ptr) == (LockId{
                    container: final(self).thread_map.spec_index(page_ptr).view().container_depth(),
                    process: final(self).thread_map.spec_index(page_ptr).view().process_depth(),
                    major: final(self).thread_map.spec_index(page_ptr).view().current_lock_major(),
                    minor: page_ptr,
                }),
                final(self).thread_map.perms_wf(),

                // ---- the freshly-initialized thread's fields (atmosphere-style in-place init) ----
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

                // ---- other KernelK fields byte-equal ----
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

                // ---- the returned thread write perm ----
                ret.view().state() is WriteLock,
                ret.view().thread_id() == final(lctx).thread_id(),
                ret.view().lock_id() == final(self).thread_map.lock_id_by_key(page_ptr),

                // ---- lctx: the thread lock id registered under Thread(page_ptr) ----
                lock_ensures(old(lctx), final(lctx), final(self).thread_map.spec_index(page_ptr).view(), final(self).thread_map.lock_id_by_key(page_ptr), KernelObjId::Thread(page_ptr)),
        {
            // ---- 1. Read container/process info via borrow_rodata ----
            let container_rodata = self.container_map.borrow_rodata(container_ptr);
            let container_ro = container_rodata.borrow();
            let container_depth = container_ro.depth;

            let process_rodata = self.process_map.borrow_rodata(process_ptr);
            let process_ro = process_rodata.borrow();
            let process_depth = process_ro.depth;
            let proc_pagetable = process_ro.pagetable;

            // ---- 2. Read upper_container_seq (Ghost/spec read, no lock needed) ----
            let ghost upper_seq = self.container_map.spec_index(container_ptr).view().uppertree_seq.view();

            // ---- 3. Construct the fresh Thread value ----
            let thread_value = Thread::new_fresh(
                container_ptr,
                container_depth,
                process_ptr,
                process_depth,
                proc_pagetable,
                Ghost(upper_seq),
            );

            // ---- 4. Take perm_4k from the page + flip state ----
            let page_index = page_ptr2page_index(page_ptr);
            proof {
                // Establish addr fact BEFORE borrow_mut modifies the page.
                reveal(page_array_wf);
                assert(page_index_wf(page_index));
                assert(self.page_array.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index));
                page_ptr_lemma1();
                assert(self.page_array.spec_index(page_index).view().view().addr == page_ptr);
            }
            let page_mut = self.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(page_lock_perm));
            let Tracked(page_perm) = take_perm_4k(page_mut);
            page_mut.state = PageState::Allocated4k{ state: Allocated4KPageState::AsThread };

            // ---- 5. Retype: PagePerm4k -> locked ThreadRwLock + LockPerm ----
            let (Tracked(thread_rwlock_perm), Tracked(thread_lock_perm)) = retype_page_perm_to_thread(
                page_ptr, thread_value, Tracked(page_perm),
                Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)),
            );

            // ---- 6. Insert into thread_map (already locked, no lctx needed) ----
            self.thread_map.insert_with_perm(
                page_ptr,
                Tracked(thread_rwlock_perm),
                (),
                Ghost(()),
                Ghost(()),
            );

            // ---- 7. Unstage from process ----
            {
                let process_mut = self.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
                process_mut.temp_alloc_cache_4k = Ghost(process_mut.temp_alloc_cache_4k@.remove(page_ptr));
                process_mut.quota_4k = process_mut.quota_4k - 1;
            }

            Tracked(thread_lock_perm)
        }
    }

    /// A process's `owned_threads` list is bounded by `NUM_PAGES`: every thread
    /// occupies a distinct 4k page (its `thread_map` key IS its backing page), and
    /// `owned_threads` injects into `thread_map` (via `process_thread_wf`), so its
    /// length can't exceed the page count. Gives the `< usize::MAX` overflow guard
    /// `create_thread_from_staged_page` needs before `push_tail`.
    ///
    pub proof fn lemma_inv_imply_owned_threads_len_bounded(k: &KernelK, process_ptr: RwLockProcessPtr)
        requires
            k.inv(),
            k.process_map.dom().contains(process_ptr),
        ensures
            k.process_map.spec_index(process_ptr).view().owned_threads.view().len() <= NUM_PAGES,
    {
        reveal(process_thread_wf);
        reveal(thread_pages_wf);
        reveal(process_perms_wf);
        page_ptr_lemma1();

        // Every thread key is a valid page pointer (thread_pages_wf reverse).
        assert(forall|t: RwLockThreadPtr| #![auto] k.thread_map.dom().contains(t) ==> page_ptr_valid(t));

        // thread_dom.len() <= NUM_PAGES: pigeonhole (injective map into [0, NUM_PAGES)).
        //@Xiangdong PROOF GAP: need Set comprehension + lemma_len_subset for pigeonhole.
        assume(k.thread_map.dom().len() <= NUM_PAGES);

        //@Xiangdong PROOF GAP: value_list_unique uses (i != j), no_duplicates uses (i < j).
        // Logically equivalent but solver doesn't do the transformation.
        assume(k.process_map.spec_index(process_ptr).view().owned_threads.view().no_duplicates());

        // owned_threads.view().len() == owned_threads.view().to_set().len() (no_duplicates).
        k.process_map.spec_index(process_ptr).view().owned_threads.view().unique_seq_to_set();

        // owned_threads.to_set() subset_of thread_dom (process_thread_wf forward).
        //@Xiangdong PROOF GAP: process_thread_wf trigger doesn't fire for subset.
        assume(k.process_map.spec_index(process_ptr).view().owned_threads.view().to_set()
            .subset_of(k.thread_map.dom()));

        // to_set().len() <= thread_dom.len() (lemma_len_subset).
        vstd::set_lib::lemma_len_subset(
            k.process_map.spec_index(process_ptr).view().owned_threads.view().to_set(),
            k.thread_map.dom());
    }

    /// A scheduler's ready `queue` is bounded by `NUM_PAGES`: it holds distinct
    /// threads (each backed by a distinct page), so its length can't exceed the
    /// page count. Gives the `< usize::MAX` overflow guard before `push_tail`.
    ///
    //@Xiangdong PENDING PROOF (external_body stub, per your call): soundness =
    // the queue holds distinct `thread_map` members (each keyed by a distinct
    // page), so its length is bounded by `thread_map.dom().len() <= NUM_PAGES`.
    // Left unproven for now.
    #[verifier::external_body]
    pub proof fn lemma_inv_imply_scheduler_queue_len_bounded(k: &KernelK, scheduler_ptr: RwLockSchedulerPtr)
        requires
            k.inv(),
            k.scheduler_map.dom().contains(scheduler_ptr),
        ensures
            k.scheduler_map.spec_index(scheduler_ptr).view().queue.view().len() <= NUM_PAGES,
    {
    }

    /// Predicate: `post_cm` is `pre_cm` with the new thread `t_ptr` added to its
    /// direct container `dc`'s `owned_threads` set and to `owned_indirect_threads`
    /// of every ancestor container listed in `t_ptr`'s `upper_container_seq`.
    /// Every other container entry (and every non-set field of `dc` / the
    /// ancestors) is unchanged. This is the exact container-map delta the
    /// create-thread wrapper performs while holding the container-chain locks.
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

    /// Mutate the container ghost sets to record a fresh thread `t_ptr`: add it to
    /// the direct container `dc`'s `owned_threads` (user-view ghost) and to every
    /// ancestor container's `owned_indirect_threads` (kernel-view ghost), touching
    /// NOTHING else. Both updates are lock-free (the sets live in the `RwLock`
    /// ghost slots, mutated via `update_user_ghost` / `update_kernel_ghost` without
    /// a `LockPerm`). `uppers` must be distinct and disjoint from `dc` so the
    /// per-ancestor inserts compose without clobbering. Establishes the exact
    /// `container_map_gained_thread` delta the create-thread wrapper needs.
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
        let ghost new_dc_threads = container_map.spec_index(dc).view_user_ghost().owned_threads.view().insert(t_ptr);
        container_map.update_user_ghost(dc, ContainerGhostU { owned_threads: Ghost(new_dc_threads) });
        add_thread_to_ancestor_sets(container_map, dc, t_ptr, uppers);
    }

    /// Recursive helper for `add_thread_to_container_sets`: insert `t_ptr` into the
    /// `owned_indirect_threads` (kernel-view ghost) of every container in `uppers`,
    /// touching nothing else. `dc`'s `owned_threads` (already inserted by the
    /// caller) is preserved because `dc` is disjoint from `uppers`.
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
            let ghost new_c_indirect = container_map.spec_index(c0).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr);
            container_map.update_kernel_ghost(c0, ContainerGhostK { owned_indirect_threads: Ghost(new_c_indirect) });
            add_thread_to_ancestor_sets(container_map, dc, t_ptr, uppers.drop_first());
            assert(!uppers.drop_first().contains(c0)) by {
                if uppers.drop_first().contains(c0) {
                    let k = choose|k: int| 0 <= k < uppers.drop_first().len() && uppers.drop_first()[k] == c0;
                    assert(uppers[k + 1] == c0);
                    assert(uppers[0] == c0);
                }
            };
            assert forall|c: RwLockContainerPtr| #![auto] uppers.contains(c) implies c == c0 || uppers.drop_first().contains(c) by {
                if c != c0 {
                    let i = choose|i: int| 0 <= i < uppers.len() && uppers[i] == c;
                    assert(uppers.drop_first()[i - 1] == c);
                }
            };
            assert forall|c: RwLockContainerPtr| #![auto] uppers.drop_first().contains(c) implies uppers.contains(c) by {
                let k = choose|k: int| 0 <= k < uppers.drop_first().len() && uppers.drop_first()[k] == c;
                assert(uppers[k + 1] == c);
            };
        }
    }

    /// Re-establish `container_thread_wf` after the create-thread wrapper adds a
    /// fresh thread `t_ptr` to its direct container's `owned_threads` and to each
    /// ancestor's `owned_indirect_threads` (the `container_map_gained_thread`
    /// delta), given the `thread_map` already carries a consistent `t_ptr` whose
    /// `owning_container == dc`, `container_depth`/`upper_container_seq` match `dc`,
    /// and `upper_container_seq == uppers`.
    ///
    /// The four membership foralls close from the container/thread frame
    /// hypotheses alone (only the ghost sets and the fresh entry moved), so the
    /// body is a single `reveal`; the delicate part is the precondition, which
    /// must pin the fresh thread's `container_depth`/`upper_container_seq` to
    /// `dc` (the caller derives the depth via `container_tree_fields_wf`).
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
        reveal(container_thread_wf);
    }

    /// Conservation law preserved across creating one thread from a staged page.
    /// The delta: a fresh thread `t_ptr` (zero free-quota-pending on every size,
    /// direct AND indirect) joins the direct container `dc`'s `owned_threads`
    /// and every ancestor's `owned_indirect_threads`; `thread_map` grows by
    /// `t_ptr`; each process's `process_effective_quota_*` is unchanged (the
    /// retyped page's `temp_alloc_cache_*` −1 and `quota_*` −1 cancel); the
    /// allocators are byte-equal. Every per-container term is therefore
    /// unchanged: the process-quota fold by `_fold_eq`, the direct-thread fold by
    /// insert-of-zero at `dc` (else `_fold_eq`), the indirect-thread fold by
    /// insert-of-zero at each ancestor (else `_fold_eq_at_depth`), the allocator
    /// term by byte-equality — so each conservation equation still balances.
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
        reveal(container_process_allocator_quota_4k_wf);
        reveal(container_process_allocator_quota_2m_wf);
        reveal(container_process_allocator_quota_1g_wf);
        reveal(container_process_wf);
        reveal(container_thread_wf);

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
    }

    /// User-view change for a successful new_thread: the running process's
    /// quota_4k decreased by 1 and owned_threads grew by 1 (push_tail).
    /// All other U-visible fields are preserved.
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

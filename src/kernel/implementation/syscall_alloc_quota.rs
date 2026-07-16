use vstd::prelude::*;
use crate::*;
verus! {
    impl KernelK{
        pub fn syscall_alloc_quota_4k(&mut self, tracked mut lctx: Tracked<LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
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
                final(self).all_objects_unlocked(&lctx),
                ret is Success
                    || ret is ErrorContainerKilled
                    || ret is ErrorContainerQuotaInsufficient
                    || ret is ErrorProcessKilled
                    || ret is ErrorProcessQuotaOverflow,
                !(ret is Success) ==> {
                    &&& final(steps).steps.last().old_u == final(steps).steps.last().new_u
                },
                ret is Success ==> {
                    let process_ptr = old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self))
                },
                ret is Success ==> {
                    let process_ptr = old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& kernel_u_only_process_quota_4k_changed(
                            final(steps).steps.last().old_u,
                            final(steps).steps.last().new_u,
                            process_ptr,
                            alloc_amount as int,
                        )
                },
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
                    self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view().owned_processes.view()
                        .contains(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    &&&
                    self.process_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().process_depth == self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().depth
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().container_depth == self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                    &&&
                    self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().container_depth
                        ==
                        self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                }
            ) by {
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };

            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let thread_ptr = cpu.current_thread.unwrap();
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;
            let container_res = self.wlock_container_unless_killed(container_ptr, Tracked(&mut lctx));
            if let (false, _) = container_res{
                // assert(self.container_map.spec_index(container_ptr).being_killed() == true);
                // self.release_cpu_and_finish(
                //     Tracked(lctx.get()),
                //     Tracked(&mut *steps),
                //     cpu_id,
                //     Tracked(cpu_lock_perm),
                // );
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, &mut lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, &mut lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                }
                return RetValueType::ErrorContainerKilled;
            }
            let Tracked(container_lock_perm) = container_res.1.unwrap();
            let container_ro = self.container_map.borrow_rodata(container_ptr);
            let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
            assert(
                {
                    &&&
                    self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().container_depth
                        == self.container_map.spec_index(container_ptr).view_rodata().view().depth
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.locked_by(&lctx) == false
                }
            ) by {
                reveal(container_allocator_wf);
                reveal(allocator_objects_unlocked);
            };

            let Tracked(quota_lock_perm) = self.wlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx));

            let quota_ref = self.allocator_4k_map.borrow_quota(
                alloc_ptr_4k, Tracked(&quota_lock_perm),
            );
            if quota_ref.value < alloc_amount {
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, &mut lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, &mut lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(&mut lctx));
            if let (false, _) = process_res {
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, &mut lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, &mut lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();
            let process_ref: &Process = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            let process_quota_4k = process_ref.quota_4k;
            if alloc_amount > usize::MAX - process_quota_4k {
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, &mut lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm));
                self.wunlock_process(process_ptr, Tracked(&mut lctx), Tracked(process_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, &mut lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            }
            self.commit_alloc_quota_4k(
                Tracked(&mut lctx),
                Tracked(&mut *steps),
                cpu_id,
                container_ptr,
                process_ptr,
                alloc_ptr_4k,
                alloc_amount,
                Tracked(cpu_lock_perm),
                Tracked(container_lock_perm),
                Tracked(quota_lock_perm),
                Tracked(process_lock_perm),
            );
            proof {
                reveal(cpu_objects_unlocked);
                reveal(page_objects_unlocked);
                reveal(container_objects_unlocked);
                reveal(process_objects_unlocked);
                reveal(thread_objects_unlocked);
                reveal(endpoint_objects_unlocked);
                reveal(pagetable_objects_unlocked);
                reveal(scheduler_objects_unlocked);
                reveal(allocator_objects_unlocked);
            }
            return  RetValueType::Success;
        }


        pub fn commit_alloc_quota_4k(
            &mut self,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            container_ptr: RwLockContainerPtr,
            process_ptr: RwLockProcessPtr,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            alloc_amount: usize,
            cpu_lock_perm: Tracked<LockPerm>,
            container_lock_perm: Tracked<LockPerm>,
            quota_lock_perm: Tracked<LockPerm>,
            process_lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                cpu_id_valid(cpu_id),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                old(self).cpu_array[cpu_id]@.wlocked_by(old(lctx)),
                old(self).cpu_array[cpu_id]@.being_killed() == false,
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == old(lctx).thread_id(),
                cpu_lock_perm@.lock_id() == old(self).cpu_array[cpu_id]@.locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Cpu(cpu_id)),
                old(lctx).lock_map()[KernelObjId::Cpu(cpu_id)] == cpu_lock_perm@.lock_id(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(self).container_map.spec_index(container_ptr).being_killed() == false,
                container_lock_perm@.state() is WriteLock,
                container_lock_perm@.thread_id() == old(lctx).thread_id(),
                container_lock_perm@.lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Container(container_ptr)),
                old(lctx).lock_map()[KernelObjId::Container(container_ptr)] == container_lock_perm@.lock_id(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.wlocked_by(old(lctx)),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.is_init(),
                quota_lock_perm@.state() is WriteLock,
                quota_lock_perm@.thread_id() == old(lctx).thread_id(),
                quota_lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
                old(lctx).lock_map()[KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)] == quota_lock_perm@.lock_id(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == old(lctx).thread_id(),
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
                old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == process_lock_perm@.lock_id(),
                old(self).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
                old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                alloc_amount <= usize::MAX - old(self).process_map.spec_index(process_ptr).view().quota_4k,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().value >= alloc_amount,
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: untouched KernelK fields ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- cpu_array / container_map / process_map: targeted entry now unlocked ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array[cpu_id]@.locking_thread() is None,
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.spec_index(container_ptr).locking_thread() is None,
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.spec_index(process_ptr).locking_thread() is None,

                // ---- allocator_4k_map: dom unchanged; targeted entry's quota now unlocked ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread() is None,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: thread preserved; the four held keys removed ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).lock_map() =~= old(lctx).lock_map()
                    .remove(KernelObjId::Cpu(cpu_id))
                    .remove(KernelObjId::Container(container_ptr))
                    .remove(KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))
                    .remove(KernelObjId::Process(process_ptr)),

                // ---- One user-view step opened and closed ----
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self)),
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),

                // ---- User-visible effect: only process_ptr's 4k quota rose ----
                kernel_u_only_process_quota_4k_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                    alloc_amount as int,
                ),
        {
            let ghost pre_self = *self;
            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                reveal(process_perms_wf);
                reveal(allocator_perms_wf);
            }
            {
                let process_mut = self.process_map.borrow_mut(
                    process_ptr,
                    Tracked(&*lctx),
                    Tracked(process_lock_perm.borrow()),
                );
                process_mut.quota_4k = process_mut.quota_4k + alloc_amount;
            }
            {
                let quota_mut = self.allocator_4k_map.borrow_mut_quota(
                    alloc_ptr_4k,
                    Tracked(&*lctx),
                    Tracked(quota_lock_perm.borrow()),
                );
                quota_mut.value = quota_mut.value - alloc_amount;
            }

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf);
                        reveal(mapped_2m_page_pagetable_wf);
                        reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        // container_process_allocator_quota_4k_wf_preserved_on_alloc(&pre_self, self, container_ptr, process_ptr, alloc_ptr_4k, alloc_amount as int);
                        reveal(container_process_allocator_quota_4k_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                            self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                                    + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                    + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                    + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                    == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                            by {
                                let depth = self.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                                lemma_thread_direct_pending_4k_fold_eq(
                                    self.container_map.spec_index(c_ptr).view().owned_threads.view(),
                                    pre_self.thread_map, self.thread_map);
                                lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                                    self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view(),
                                    pre_self.thread_map, self.thread_map, depth);
                                assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                    reveal(container_process_wf);
                                };
                                assert(self.allocator_4k_map.dom().contains(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k)) by {
                                    reveal(container_allocator_wf);
                                }
                                if c_ptr == container_ptr{
                                    lemma_process_effective_quota_4k_fold_change_by(
                                        self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                        pre_self.process_map, self.process_map, process_ptr, alloc_amount as int);
                                }else{
                                    assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().contains(process_ptr) == false) by {
                                        reveal(container_process_wf);
                                    };
                                    assert(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k != alloc_ptr_4k) by {
                                        reveal(container_allocator_wf);
                                    }
                                    lemma_process_effective_quota_4k_fold_eq(
                                        self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                        pre_self.process_map, self.process_map);
                                }
                            };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                        reveal(container_process_allocator_quota_2m_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                                == self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_2m_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                pre_self.process_map, self.process_map);

                        };
                        // container_process_allocator_quota_2m_wf_preserved_on_alloc(&pre_self, self);
                    };
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_1g_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_1g(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                                == self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_1g_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                pre_self.process_map, self.process_map);

                        };
                    };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_4k_wf);
                        reveal(process_staged_pages_2m_wf);
                        reveal(process_staged_pages_1g_wf);
                    };
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                        assert forall|c_ptr: RwLockContainerPtr| #![auto]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            process_tree_wf(
                                self.container_map.spec_index(c_ptr).view().root_process,
                                self.container_map.spec_index(c_ptr).view().owned_processes@,
                                self.process_map,
                            )
                        by {
                            process_no_change_to_tree_fields_imply_wf(
                                self.container_map.spec_index(c_ptr).view().root_process,
                                self.container_map.spec_index(c_ptr).view().owned_processes@,
                                pre_self.process_map, self.process_map,
                            );
                        };
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
            self.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
            self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut *lctx), quota_lock_perm);
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
            proof {
                steps.end_user_view_step(&*self, lctx);
                kernel_process_quota_4k_changed_imply_kernel_u_changed(&pre_self, self, process_ptr, alloc_amount as int);
            }
        }

    }

    pub open spec fn kernel_u_only_process_quota_4k_changed(
        old_u: KernelU,
        new_u: KernelU,
        process_ptr: RwLockProcessPtr,
        delta: int,
    ) -> bool {
        &&& new_u.cpu_array == old_u.cpu_array
        &&& new_u.process_map.dom() == old_u.process_map.dom()
        &&& old_u.process_map.dom().contains(process_ptr)
        // The targeted process: only `quota_4k` increased by `delta`;
        // every other field preserved.
        &&& new_u.process_map[process_ptr].quota_4k as int
                == old_u.process_map[process_ptr].quota_4k as int + delta
        &&& new_u.process_map[process_ptr].pagetable      == old_u.process_map[process_ptr].pagetable
        &&& new_u.process_map[process_ptr].quota_2m       == old_u.process_map[process_ptr].quota_2m
        &&& new_u.process_map[process_ptr].quota_1g       == old_u.process_map[process_ptr].quota_1g
        &&& new_u.process_map[process_ptr].parent         == old_u.process_map[process_ptr].parent
        &&& new_u.process_map[process_ptr].children       == old_u.process_map[process_ptr].children
        &&& new_u.process_map[process_ptr].depth          == old_u.process_map[process_ptr].depth
        &&& new_u.process_map[process_ptr].uppertree_seq  == old_u.process_map[process_ptr].uppertree_seq
        &&& new_u.process_map[process_ptr].subtree_set    == old_u.process_map[process_ptr].subtree_set
        &&& new_u.process_map[process_ptr].owned_threads  == old_u.process_map[process_ptr].owned_threads
        &&& new_u.process_map[process_ptr].killed         == old_u.process_map[process_ptr].killed
        // Every other process: projection unchanged.
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map[p]]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map[p] == old_u.process_map[p]
    }

    pub proof fn kernel_process_quota_4k_changed_imply_kernel_u_changed(
        pre: &KernelK,
        post: &KernelK,
        process_ptr: RwLockProcessPtr,
        delta: int,
    )
        requires
            // pagetable_map: only the per-entry `view()` is read (via
            // `get_process_pagetable`), not lock state.
            forall|pt: RwLockPageTableRoot|
                #![trigger post.pagetable_map.spec_index(pt).view()]
                post.pagetable_map.spec_index(pt).view() == pre.pagetable_map.spec_index(pt).view(),
            // cpu_array: per-slot payload `view()`.
            forall|i: int|
                #![trigger post.cpu_array.spec_index(i as usize).value.view()]
                0 <= i < NUM_CPUS ==>
                    post.cpu_array.spec_index(i as usize).value.view()
                        == pre.cpu_array.spec_index(i as usize).value.view(),
            // process_map: same domain, targeted process present.
            post.process_map.dom() =~= pre.process_map.dom(),
            pre.process_map.dom().contains(process_ptr),
            // Targeted process: `quota_4k` up by `delta`; every other field
            // the projection reads (`view()` minus `quota_4k`, `view_rodata()`,
            // `being_killed()`) preserved.
            post.process_map.spec_index(process_ptr).view().quota_4k as int
                == pre.process_map.spec_index(process_ptr).view().quota_4k as int + delta,
            post.process_map.spec_index(process_ptr).view().quota_2m
                == pre.process_map.spec_index(process_ptr).view().quota_2m,
            post.process_map.spec_index(process_ptr).view().quota_1g
                == pre.process_map.spec_index(process_ptr).view().quota_1g,
            post.process_map.spec_index(process_ptr).view().children
                == pre.process_map.spec_index(process_ptr).view().children,
            post.process_map.spec_index(process_ptr).view().uppertree_seq
                == pre.process_map.spec_index(process_ptr).view().uppertree_seq,
            post.process_map.spec_index(process_ptr).view().subtree_set
                == pre.process_map.spec_index(process_ptr).view().subtree_set,
            post.process_map.spec_index(process_ptr).view().owned_threads
                == pre.process_map.spec_index(process_ptr).view().owned_threads,
            post.process_map.spec_index(process_ptr).view().pagetable
                == pre.process_map.spec_index(process_ptr).view().pagetable,
            post.process_map.spec_index(process_ptr).view_rodata()
                == pre.process_map.spec_index(process_ptr).view_rodata(),
            post.process_map.spec_index(process_ptr).being_killed()
                == pre.process_map.spec_index(process_ptr).being_killed(),
            // Every other process: full projection-relevant equality (same as
            // the no-change lemma's per-process hypothesis).
            forall|ptr: RwLockProcessPtr|
                #![trigger post.process_map.spec_index(ptr)]
                pre.process_map.dom().contains(ptr) && ptr != process_ptr ==>
                    post.process_map.spec_index(ptr).view() == pre.process_map.spec_index(ptr).view()
                    && post.process_map.spec_index(ptr).view_rodata() == pre.process_map.spec_index(ptr).view_rodata()
                    && post.process_map.spec_index(ptr).being_killed() == pre.process_map.spec_index(ptr).being_killed(),
        ensures
            kernel_u_only_process_quota_4k_changed(
                kernel_k_to_kernel_u(*pre),
                kernel_k_to_kernel_u(*post),
                process_ptr,
                delta,
            ),
    {
        let pre_u = kernel_k_to_kernel_u(*pre);
        let post_u = kernel_k_to_kernel_u(*post);
        // cpu_array: element-wise, from the per-slot payload-view equality.
        assert(post_u.cpu_array =~= pre_u.cpu_array) by {
            assert forall|i: int|
                0 <= i < NUM_CPUS
                implies #[trigger] post_u.cpu_array[i] == pre_u.cpu_array[i]
            by {
                assert(post.cpu_array.spec_index(i as usize).value.view()
                    == pre.cpu_array.spec_index(i as usize).value.view());
            }
        };
        // process_map domain: equal, so the targeted process is in both.
        assert(post_u.process_map.dom() =~= pre_u.process_map.dom());
        assert(pre_u.process_map.dom().contains(process_ptr));
        assert(post_u.process_map.dom().contains(process_ptr));
        // Targeted process: the only delta is `quota_4k`; the projected
        // pagetable is preserved because the process points at the same
        // pagetable and that entry's `view()` is equal.
        assert(post.get_process_pagetable(process_ptr) == pre.get_process_pagetable(process_ptr)) by {
            let pt = post.process_map.spec_index(process_ptr).view().pagetable;
            assert(post.pagetable_map.spec_index(pt).view() == pre.pagetable_map.spec_index(pt).view());
        };
        // Every other process: its whole projection is unchanged — same
        // `view()` (so same `quota_*`/tree fields/`pagetable` ptr), same
        // `view_rodata()`, same `being_killed()`, and that pagetable's
        // `view()` is equal, so `get_process_pagetable` matches too.
        assert forall|p: RwLockProcessPtr|
            #[trigger] pre_u.process_map.dom().contains(p) && p != process_ptr
            implies post_u.process_map[p] == pre_u.process_map[p]
        by {
            assert(pre.process_map.dom().contains(p));
            assert(post.process_map.spec_index(p).view() == pre.process_map.spec_index(p).view());
            assert(post.process_map.spec_index(p).view_rodata() == pre.process_map.spec_index(p).view_rodata());
            assert(post.process_map.spec_index(p).being_killed() == pre.process_map.spec_index(p).being_killed());
            let pt = post.process_map.spec_index(p).view().pagetable;
            assert(post.get_process_pagetable(p) == pre.get_process_pagetable(p)) by {
                assert(post.pagetable_map.spec_index(pt).view() == pre.pagetable_map.spec_index(pt).view());
            };
        };
    }

    /// Preservation lemma for the 4k conservation invariant under the
    /// `syscall_alloc_quota_4k` mutation: exactly one process's effective 4k
    /// quota rises by `alloc_amount` and exactly that container's 4k allocator
    /// `quota.value` falls by `alloc_amount` (its `total_free_pages` held), with
    /// `container_map` / `thread_map` / every other process / every other
    /// allocator entry byte-unchanged between `pre` and `post`. The per-container
    /// conservation sum is therefore preserved (the +`alloc_amount` on the
    /// process fold cancels the −`alloc_amount` on the allocator quota; every
    /// other container is wholly untouched). Lifts the inline fold block out of
    /// `syscall_alloc_quota_4k`.
    ///
    /// Takes the whole `pre`/`post` `KernelK` rather than the individual maps:
    /// the source-wf conjuncts read off `pre` are exactly entry-`inv()` clauses,
    /// so a caller holding `old(self).inv()` discharges them directly. Because
    /// `post.container_map == pre.container_map` and `post.thread_map ==
    /// pre.thread_map`, the container/thread folds are syntactically identical
    /// pre/post and need no fold lemma; only the process fold shifts, bridged by
    /// the `kernel_fold_axioms` set axioms (`_fold_change_by` on the touched
    /// container, `_fold_eq` elsewhere).
    #[verifier::spinoff_prover]
    pub proof fn container_process_allocator_quota_4k_wf_preserved_on_alloc(
        pre: &KernelK,
        post: &KernelK,
        container_ptr: RwLockContainerPtr,
        process_ptr: RwLockProcessPtr,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        alloc_amount: int,
    )
        requires
            // OLD 4k conservation holds (an entry-`inv()` clause).
            container_process_allocator_quota_4k_wf(pre.container_map, pre.process_map, pre.thread_map, pre.allocator_4k_map),
            // Container→process structure: owned sets sit in the process domain,
            // and each process belongs to exactly one container (uniqueness).
            container_process_wf(pre.container_map, pre.process_map),
            // Container→allocator structure: gives, per container, that its 4k
            // allocator is in the allocator domain and is owned by that container
            // (indexing + allocator-uniqueness). Stated as the opaque `inv()`
            // clause itself so a caller holding `old(self).inv()` discharges it
            // directly; the body reveals it to extract the two facts it needs.
            container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
            // `container_map`: the quota path WRITE-LOCKS the owning container,
            // so its byte representation is NOT preserved (lock state moves).
            // The conservation fold reads only `view()` / `view_rodata()`, both
            // of which a lock op preserves — so require per-entry projection
            // equality + same domain, not whole-map byte equality.
            post.container_map.dom() =~= pre.container_map.dom(),
            forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr)]
                pre.container_map.dom().contains(c_ptr) ==>
                    post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view()
                    && post.container_map.spec_index(c_ptr).view_rodata() == pre.container_map.spec_index(c_ptr).view_rodata(),
            // `thread_map` IS byte-equal: no thread object is touched on this path.
            post.thread_map == pre.thread_map,
            // The mutation's anchor objects.
            pre.container_map.dom().contains(container_ptr),
            pre.container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
            pre.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            // Domains preserved (no process / allocator added or removed).
            post.process_map.dom() =~= pre.process_map.dom(),
            post.allocator_4k_map.dom() =~= pre.allocator_4k_map.dom(),
            // Process delta: only `process_ptr`'s effective 4k quota rose by
            // `alloc_amount`; every other process's effective 4k quota is held.
            process_effective_quota_4k(post.process_map.spec_index(process_ptr))
                == process_effective_quota_4k(pre.process_map.spec_index(process_ptr)) + alloc_amount,
            forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(post.process_map.spec_index(p))]
                pre.process_map.dom().contains(p) && p != process_ptr ==>
                    process_effective_quota_4k(post.process_map.spec_index(p))
                        == process_effective_quota_4k(pre.process_map.spec_index(p)),
            // Allocator delta: `alloc_ptr_4k`'s quota value fell by `alloc_amount`
            // with `total_free_pages` held; every other allocator entry untouched.
            post.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() as int
                == pre.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() as int - alloc_amount,
            post.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view()
                == pre.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view(),
            forall|a: RwLockPageAllocatorPtr|
                #![trigger post.allocator_4k_map.spec_index(a)]
                pre.allocator_4k_map.dom().contains(a) && a != alloc_ptr_4k ==>
                    post.allocator_4k_map.spec_index(a) == pre.allocator_4k_map.spec_index(a),
        ensures
            container_process_allocator_quota_4k_wf(post.container_map, post.process_map, post.thread_map, post.allocator_4k_map),
    {
        reveal(container_process_allocator_quota_4k_wf);
        // Establish the post-state conservation equation container-by-container.
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
            post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(post.process_map.spec_index(p_ptr))})
                    + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                    + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                    == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
            by {
                // The fold reads only `view()` / `view_rodata()` off the
                // container, both preserved by the write-lock — bridge the goal
                // (stated over `post.container_map`) back to `pre.container_map`,
                // where the entry invariant lives.
                assert(pre.container_map.dom().contains(c_ptr));
                assert(post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view());
                assert(post.container_map.spec_index(c_ptr).view_rodata() == pre.container_map.spec_index(c_ptr).view_rodata());
                // The owned sets the three folds range over are byte-equal pre/post
                // (same container `view()`), and the allocator pointer is too (same
                // `view_rodata()`) — so the goal's `post`-side folds/index are the
                // very same expressions as the `pre`-side ones the lemmas produce.
                assert(post.container_map.spec_index(c_ptr).view().owned_processes
                    == pre.container_map.spec_index(c_ptr).view().owned_processes);
                assert(post.container_map.spec_index(c_ptr).view().owned_threads
                    == pre.container_map.spec_index(c_ptr).view().owned_threads);
                assert(post.container_map.spec_index(c_ptr).view().owned_indirect_threads
                    == pre.container_map.spec_index(c_ptr).view().owned_indirect_threads);
                assert(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k
                    == pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k);
                assert(post.container_map.spec_index(c_ptr).view_rodata().view().depth
                    == pre.container_map.spec_index(c_ptr).view_rodata().view().depth);
                // OLD equation at this container — the only fact pulled from the
                // entry invariant; everything else is framing arithmetic.
                assert(pre.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(pre.process_map.spec_index(p_ptr))})
                    + pre.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + pre.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                    + pre.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + pre.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    + pre.allocator_4k_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                    == pre.allocator_4k_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view())
                    by { reveal(container_process_allocator_quota_4k_wf); };

                // owned_processes ⊆ process domain (for the fold axioms).
                assert(pre.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(pre.process_map.dom())) by {
                    reveal(container_process_wf);
                };

                if c_ptr == container_ptr {
                    // Touched container: its allocator IS `alloc_ptr_4k`. Process
                    // fold rises by `alloc_amount`, allocator quota falls by
                    // `alloc_amount` (total_free held) — the two cancel.
                    assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k);
                    lemma_process_effective_quota_4k_fold_change_by(
                        pre.container_map.spec_index(c_ptr).view().owned_processes.view(),
                        pre.process_map, post.process_map, process_ptr, alloc_amount);
                    assert(post.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() as int
                        == pre.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() as int - alloc_amount);
                    assert(post.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view()
                        == pre.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view());
                } else {
                    // Other container: `process_ptr` is not one of its processes
                    // (uniqueness), so its process fold is unchanged...
                    assert(pre.container_map.spec_index(c_ptr).view().owned_processes.view().contains(process_ptr) == false) by {
                        reveal(container_process_wf);
                    };
                    lemma_process_effective_quota_4k_fold_eq(
                        pre.container_map.spec_index(c_ptr).view().owned_processes.view(),
                        pre.process_map, post.process_map);
                    // ...and its allocator differs from the touched one, so its
                    // quota / total_free are untouched: if they coincided, the
                    // shared entry's `owning_container` would be both `c_ptr`
                    // and `container_ptr` — contradicting `c_ptr != container_ptr`.
                    assert(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k != alloc_ptr_4k) by {
                        reveal(container_allocator_wf);
                        assert(pre.allocator_4k_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).owning_container == c_ptr);
                        assert(pre.allocator_4k_map.spec_index(pre.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).owning_container == container_ptr);
                    };
                    // That allocator entry is in the domain (container_allocator_wf)
                    // and is `!= alloc_ptr_4k`, so by "every other allocator entry
                    // untouched" it's byte-equal — its quota / total_free are exactly
                    // the pre values the OLD equation uses.
                    assert(pre.allocator_4k_map.dom().contains(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(post.allocator_4k_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k)
                        == pre.allocator_4k_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k));
                }
            };
    }

    /// Preservation lemma for the 2m conservation invariant across the
    /// `syscall_alloc_quota_4k` mutation. The 4k path never touches any 2m
    /// quantity, so every 2m summand is unchanged between `pre` and `post` —
    /// this is the pure "nothing changed" case, with NO distinguished
    /// process/allocator, no delta, and no `container_allocator_wf`
    /// (the whole 2m allocator map is byte-equal, so no uniqueness argument is
    /// needed). Minimal preconditions: source-wf + same domains + the projection
    /// equalities the 2m fold actually reads (container `view()`/`view_rodata()`,
    /// per-process `process_effective_quota_2m`, byte-equal `thread_map` and
    /// `allocator_2m_map`). Only the process fold needs the (set-fold-eq) bridge;
    /// the container/thread/allocator terms are already syntactically equal.
    #[verifier::spinoff_prover]
    pub proof fn container_process_allocator_quota_2m_wf_preserved_on_alloc(
        pre: &KernelK,
        post: &KernelK,
    )
        requires
            // OLD 2m conservation holds (an entry-`inv()` clause).
            container_process_allocator_quota_2m_wf(pre.container_map, pre.process_map, pre.thread_map, pre.allocator_2m_map),
            // Container→process structure: owned sets sit in the process domain
            // (so the fold's per-element bridge applies to each owned process).
            container_process_wf(pre.container_map, pre.process_map),
            // `container_map`: write-locked on the 4k path, so byte representation
            // is NOT preserved; the fold reads only `view()` / `view_rodata()`,
            // which a lock op preserves — require those + same domain.
            post.container_map.dom() =~= pre.container_map.dom(),
            forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr)]
                pre.container_map.dom().contains(c_ptr) ==>
                    post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view()
                    && post.container_map.spec_index(c_ptr).view_rodata() == pre.container_map.spec_index(c_ptr).view_rodata(),
            // `thread_map` / `allocator_2m_map` are byte-equal: no 2m object moves.
            post.thread_map == pre.thread_map,
            post.allocator_2m_map == pre.allocator_2m_map,
            // Process domain preserved, and every process's 2m effective quota
            // is held (the 4k path only shifts `quota_4k`).
            post.process_map.dom() =~= pre.process_map.dom(),
            forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_2m(post.process_map.spec_index(p))]
                pre.process_map.dom().contains(p) ==>
                    process_effective_quota_2m(post.process_map.spec_index(p))
                        == process_effective_quota_2m(pre.process_map.spec_index(p)),
        ensures
            container_process_allocator_quota_2m_wf(post.container_map, post.process_map, post.thread_map, post.allocator_2m_map),
    {
        reveal(container_process_allocator_quota_2m_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
            post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(post.process_map.spec_index(p_ptr))})
                    + post.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                    + post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                    == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
            by {
                // Bridge the goal (over `post.container_map`) back to `pre`: the
                // owned sets and allocator pointer are byte-equal (same container
                // `view()` / `view_rodata()`), and `thread_map`/`allocator_2m_map`
                // are byte-equal outright — so the container/thread/allocator terms
                // are the very same expressions as the OLD equation's.
                assert(pre.container_map.dom().contains(c_ptr));
                assert(post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view());
                assert(post.container_map.spec_index(c_ptr).view_rodata() == pre.container_map.spec_index(c_ptr).view_rodata());
                // OLD equation at this container.
                assert(pre.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(pre.process_map.spec_index(p_ptr))})
                    + pre.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + pre.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                    + pre.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + pre.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    + pre.allocator_2m_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                    == pre.allocator_2m_map.spec_index(pre.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view())
                    by { reveal(container_process_allocator_quota_2m_wf); };
                // owned_processes ⊆ process domain (so each owned process's 2m
                // effective quota is held by the per-process precondition).
                assert(pre.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(pre.process_map.dom())) by {
                    reveal(container_process_wf);
                };
                // Only the process fold needs the set-fold bridge; no quota changed.
                lemma_process_effective_quota_2m_fold_eq(
                    pre.container_map.spec_index(c_ptr).view().owned_processes.view(),
                    pre.process_map, post.process_map);
            };
    }
}

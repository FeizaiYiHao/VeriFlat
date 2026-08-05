use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
verus! {
    impl KernelK{
        pub fn syscall_alloc_quota_4k(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(lctx).lock_id_set() =~= Set::<LockId>::empty(),
                old(self).all_objects_unlocked(old(lctx)),
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                old(self).locked_objects_match_lctx(old(lctx)),
                old(lctx).wf(),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(steps).steps.len() == 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(self).all_objects_unlocked(final(lctx)),
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
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
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(process_perms_wf);
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };

            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;
            let container_res = self.wlock_container_unless_killed(container_ptr, Tracked(lctx));
            if let (false, _) = container_res{
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx);
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
                }
            ) by {
                reveal(allocator_perms_wf);
                reveal(container_allocator_wf);
            };

            let Tracked(quota_lock_perm) = self.wlock_quota_4k(alloc_ptr_4k, Tracked(lctx));

            let quota_ref = self.allocator_4k_map.borrow_quota(
                alloc_ptr_4k, Tracked(&quota_lock_perm),
            );
            if quota_ref.value < alloc_amount {
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(lctx));
            if let (false, _) = process_res {
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();
            let process_ref: &Process = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            let process_quota_4k = process_ref.quota_4k;
            if alloc_amount > usize::MAX - process_quota_4k {
                proof {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    steps.begin_user_view_step(&*self, lctx);
                }
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                self.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                proof {
                    steps.end_user_view_step(&*self, lctx);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            }
            self.commit_alloc_quota_4k(
                Tracked(lctx),
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
                self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx);
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
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
                cpu_lock_perm.view().lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).container_map.dom().contains(container_ptr),
                container_lock_perm.view().state() is WriteLock,
                container_lock_perm.view().thread_id() == old(lctx).thread_id(),
                container_lock_perm.view().lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(self).container_map.spec_index(container_ptr).being_killed() == false,
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.is_init(),
                quota_lock_perm.view().state() is WriteLock,
                quota_lock_perm.view().thread_id() == old(lctx).thread_id(),
                quota_lock_perm.view().lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    .wlocked_by(old(lctx)),
                old(self).process_map.dom().contains(process_ptr),
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == old(lctx).thread_id(),
                process_lock_perm.view().lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
                old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                alloc_amount <= usize::MAX - old(self).process_map.spec_index(process_ptr).view().quota_4k,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().value >= alloc_amount,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.spec_index(cpu_id).view().locking_thread() is None,
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.spec_index(container_ptr).locking_thread() is None,
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.spec_index(process_ptr).locking_thread() is None,
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread() is None,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).wf(),
                final(lctx).lock_id_set() =~=
                    old(lctx).lock_id_set()
                        .remove(old(self).cpu_array.lock_id_by_index(cpu_id))
                        .remove(old(self).container_map.lock_id_by_key(container_ptr))
                        .remove(
                            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                                .quota.lock_id(),
                        )
                        .remove(old(self).process_map.lock_id_by_key(process_ptr)),
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self)),
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                kernel_u_only_process_quota_4k_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                    alloc_amount as int,
                ),
        {
            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                assert(
                    self.process_map.perms_wf()
                    && self.process_map.spec_index(process_ptr).is_init()
                ) by {
                    reveal(process_perms_wf);
                };
                assert(self.allocator_4k_map.perms_wf()) by {
                    reveal(allocator_perms_wf);
                };
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
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by { lemma_no_change_imply_container_process_page_pagetable_wf_forall(); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { lemma_no_change_imply_process_pages_wf_forall(); };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_process_wf);
                        reveal(container_allocator_wf);
                        crate::kernel::implementation::allocate_free_4k_page::lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, alloc_amount as int);
                        crate::kernel::implementation::allocate_free_4k_page::lemma_process_effective_quota_4k_fold_sum_eq_forall();
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by { crate::kernel::implementation::allocate_free_4k_page::container_process_allocator_quota_2m_wf_forall(); };
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by { crate::kernel::implementation::allocate_free_4k_page::container_process_allocator_quota_1g_wf_forall(); };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { lemma_no_change_imply_process_pagetable_match_forall(); };
                    assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by { lemma_no_change_imply_container_allocator_free_4k_page_wf_forall(); };
                };
                assert(self.process_management_inv()) by {
                    assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                    assert(container_process_wf(self.container_map, self.process_map)) by { lemma_no_change_imply_container_process_wf_forall(); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { lemma_no_change_imply_per_container_process_tree_wf_forall(); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { lemma_no_change_imply_process_cpu_wf_forall(); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { lemma_no_change_imply_process_thread_wf_forall(); };
                };
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by { lemma_no_change_imply_cpu_dirty_map_wf_forall(); };
                assert(iommu_root_table_process_wf(&self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                assert(process_pci_function_ownership_wf(&self.iommu_root_table, self.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                ) by {
                    reveal(allocator_perms_wf);
                };
            }
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
            self.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
            self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut *lctx), quota_lock_perm);
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
            proof {
                steps.end_user_view_step(&*self, lctx);
                kernel_process_quota_4k_changed_imply_kernel_u_changed(
                    old(self),
                    self,
                    process_ptr,
                    alloc_amount as int,
                );
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
        &&& new_u.process_map.spec_index(process_ptr).quota_4k as int
                == old_u.process_map.spec_index(process_ptr).quota_4k as int + delta
        &&& new_u.process_map.spec_index(process_ptr).pagetable      == old_u.process_map.spec_index(process_ptr).pagetable
        &&& new_u.process_map.spec_index(process_ptr).iommu_table    == old_u.process_map.spec_index(process_ptr).iommu_table
        &&& new_u.process_map.spec_index(process_ptr).quota_2m       == old_u.process_map.spec_index(process_ptr).quota_2m
        &&& new_u.process_map.spec_index(process_ptr).quota_1g       == old_u.process_map.spec_index(process_ptr).quota_1g
        &&& new_u.process_map.spec_index(process_ptr).parent         == old_u.process_map.spec_index(process_ptr).parent
        &&& new_u.process_map.spec_index(process_ptr).children       == old_u.process_map.spec_index(process_ptr).children
        &&& new_u.process_map.spec_index(process_ptr).depth          == old_u.process_map.spec_index(process_ptr).depth
        &&& new_u.process_map.spec_index(process_ptr).uppertree_seq  == old_u.process_map.spec_index(process_ptr).uppertree_seq
        &&& new_u.process_map.spec_index(process_ptr).subtree_set    == old_u.process_map.spec_index(process_ptr).subtree_set
        &&& new_u.process_map.spec_index(process_ptr).owned_threads  == old_u.process_map.spec_index(process_ptr).owned_threads
        &&& new_u.process_map.spec_index(process_ptr).killed         == old_u.process_map.spec_index(process_ptr).killed
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map.spec_index(p)]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map.spec_index(p) == old_u.process_map.spec_index(p)
    }

    pub proof fn kernel_process_quota_4k_changed_imply_kernel_u_changed(
        pre: &KernelK,
        post: &KernelK,
        process_ptr: RwLockProcessPtr,
        delta: int,
    )
        requires
            post.iommu_table_map == pre.iommu_table_map,
            post.iommu_root_table == pre.iommu_root_table,
            forall|pt: RwLockPageTableRoot|
                #![trigger post.pagetable_map.spec_index(pt).view()]
                post.pagetable_map.spec_index(pt).view() == pre.pagetable_map.spec_index(pt).view(),
            forall|i: int|
                #![trigger post.cpu_array.spec_index(i as usize).value.view()]
                0 <= i < NUM_CPUS ==>
                    post.cpu_array.spec_index(i as usize).value.view()
                        == pre.cpu_array.spec_index(i as usize).value.view(),
            post.process_map.dom() =~= pre.process_map.dom(),
            pre.process_map.dom().contains(process_ptr),
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
            post.process_map.spec_index(process_ptr).view().iommu_table
                == pre.process_map.spec_index(process_ptr).view().iommu_table,
            post.process_map.spec_index(process_ptr).view_rodata()
                == pre.process_map.spec_index(process_ptr).view_rodata(),
            post.process_map.spec_index(process_ptr).being_killed()
                == pre.process_map.spec_index(process_ptr).being_killed(),
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
        assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
    }
}

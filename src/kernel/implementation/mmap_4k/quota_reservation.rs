use vstd::prelude::*;
use crate::*;

verus! {

impl KernelK {
    /// Move 4K quota between an owning process and one of its threads.
    ///
    /// This is an internal user-visible atomic step: the caller has already
    /// opened the step and holds both write locks.  No lock or LocalContext
    /// state changes here.
    fn transfer_process_thread_4k_quota(
        &mut self,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        amount: usize,
        to_thread: bool,
        Tracked(lctx): Tracked<&mut LocalContext>,
        process_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).user_view_locking_state() is Release,
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc == process_ptr,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            to_thread ==> {
                &&& old(self).process_map.spec_index(process_ptr).view().quota_4k >= amount
                &&& amount <= usize::MAX
                    - old(self).thread_map.spec_index(thread_ptr).view().quota_4k
            },
            !to_thread ==> {
                &&& thread_effective_quota_4k(
                    old(self).thread_map.spec_index(thread_ptr),
                ) >= amount as int
                &&& amount <= usize::MAX
                    - old(self).process_map.spec_index(process_ptr).view().quota_4k
            },
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set(),
            final(lctx).page_lock_map() =~= old(lctx).page_lock_map(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).process_map.unchanged_except(
                &old(self).process_map,
                process_ptr,
            ),
            final(self).thread_map.unchanged_except(
                &old(self).thread_map,
                thread_ptr,
            ),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed()
                == old(self).process_map.spec_index(process_ptr).being_killed(),
            final(self).thread_map.spec_index(thread_ptr).being_killed()
                == old(self).thread_map.spec_index(thread_ptr).being_killed(),
            process_lock_perm.view().lock_id()
                == final(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            thread_lock_perm.view().lock_id()
                == final(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).being_killed()
                == old(self).process_map.spec_index(process_ptr).being_killed(),
            final(self).thread_map.spec_index(thread_ptr).being_killed()
                == old(self).thread_map.spec_index(thread_ptr).being_killed(),
            to_thread ==> {
                &&& final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k
                        - amount
                &&& final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                        + amount
            },
            !to_thread ==> {
                &&& final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k
                        + amount
                &&& final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                        - amount
            },
            process_quota_4k_framed_fields_unchanged(
                old(self).process_map,
                final(self).process_map,
            ),
            thread_process_management_fields_unchanged(
                old(self).thread_map,
                final(self).thread_map,
            ),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view().quota_2m
                == old(self).thread_map.spec_index(thread_ptr).view().quota_2m,
            final(self).thread_map.spec_index(thread_ptr).view().quota_1g
                == old(self).thread_map.spec_index(thread_ptr).view().quota_1g,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index
                == old(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index,
            final(self).thread_map.spec_index(thread_ptr).view().ipc_payload
                == old(self).thread_map.spec_index(thread_ptr).view().ipc_payload,
            final(self).thread_map.spec_index(thread_ptr).view().error_code
                == old(self).thread_map.spec_index(thread_ptr).view().error_code,
            final(self).thread_map.spec_index(thread_ptr).view().trap_frame
                == old(self).thread_map.spec_index(thread_ptr).view().trap_frame,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).page_array == old(self).page_array,
            final(self).cpu_array == old(self).cpu_array,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).allocator_4k_map == old(self).allocator_4k_map,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).default_pagetable == old(self).default_pagetable,
    {
        proof {
            assert(
                self.process_map.perms_wf()
                && self.process_map.spec_index(process_ptr).is_init()
                && self.thread_map.perms_wf()
                && self.thread_map.spec_index(thread_ptr).is_init()
            ) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
            };
        }
        if to_thread {
            let process = self.process_map.borrow_mut(
                process_ptr,
                Tracked(&*lctx),
                process_lock_perm,
            );
            process.quota_4k = process.quota_4k - amount;
            let thread = self.thread_map.borrow_mut(
                thread_ptr,
                Tracked(&*lctx),
                thread_lock_perm,
            );
            thread.quota_4k = thread.quota_4k + amount;
        } else {
            let process = self.process_map.borrow_mut(
                process_ptr,
                Tracked(&*lctx),
                process_lock_perm,
            );
            process.quota_4k = process.quota_4k + amount;
            let thread = self.thread_map.borrow_mut(
                thread_ptr,
                Tracked(&*lctx),
                thread_lock_perm,
            );
            thread.quota_4k = thread.quota_4k - amount;
        }

        proof {
            assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
            assert(thread_perms_wf(self.thread_map)) by {
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
                reveal(thread_temp_alloc_empty_unless_wlocked);
            };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by {
                assert(container_process_page_pagetable_wf(
                    self.container_map,
                    self.process_map,
                    self.pagetable_map,
                    self.page_array,
                )) by { lemma_no_change_imply_container_process_page_pagetable_wf_forall(); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { lemma_no_change_imply_process_pages_wf_forall(); };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                    thread_staged_pages_4k_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                    thread_staged_pages_2m_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                };
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { lemma_no_change_imply_process_pagetable_match_forall(); };
                assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                assert(container_process_allocator_quota_4k_wf(
                    self.container_map,
                    self.process_map,
                    self.thread_map,
                    self.allocator_4k_map,
                )) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_thread_wf);
                    reveal(process_thread_wf);
                    assert forall|c_ptr: RwLockContainerPtr|
                        #![trigger self.container_map.spec_index(c_ptr)
                            .view_rodata().view().allocator_ptr_4k]
                        self.container_map.dom().contains(c_ptr)
                    implies
                        process_effective_quota_4k_fold_sum(
                            self.container_map.spec_index(c_ptr).view()
                                .owned_processes.view(),
                            self.process_map,
                        )
                        + thread_effective_quota_4k_fold_sum(
                            self.container_map.spec_index(c_ptr).view_user_ghost()
                                .owned_threads.view(),
                            self.thread_map,
                        )
                        + thread_direct_pending_4k_fold_sum(
                            self.container_map.spec_index(c_ptr).view_user_ghost()
                                .owned_threads.view(),
                            self.thread_map,
                        )
                        + thread_indirect_pending_4k_fold_sum_at_depth(
                            self.container_map.spec_index(c_ptr).view_kernel_ghost()
                                .owned_indirect_threads.view(),
                            self.thread_map,
                            self.container_map.spec_index(c_ptr).view_rodata()
                                .view().depth as int,
                        )
                        + self.allocator_4k_map.spec_index(
                            self.container_map.spec_index(c_ptr).view_rodata()
                                .view().allocator_ptr_4k,
                        ).quota.view().view()
                        == self.allocator_4k_map.spec_index(
                            self.container_map.spec_index(c_ptr).view_rodata()
                                .view().allocator_ptr_4k,
                        ).total_free_pages.view()
                    by {
                        let processes = self.container_map.spec_index(c_ptr)
                            .view().owned_processes.view();
                        let threads = self.container_map.spec_index(c_ptr)
                            .view_user_ghost().owned_threads.view();
                        let indirect_threads = self.container_map.spec_index(c_ptr)
                            .view_kernel_ghost().owned_indirect_threads.view();
                        let depth = self.container_map.spec_index(c_ptr)
                            .view_rodata().view().depth as int;
                        let process_container = old(self).process_map
                            .spec_index(process_ptr).view_rodata().view().owning_container;
                        let thread_delta: int = if to_thread {
                            amount as int
                        } else {
                            -(amount as int)
                        };
                        if c_ptr == process_container {
                            lemma_process_effective_quota_4k_fold_change_by(
                                processes,
                                old(self).process_map,
                                self.process_map,
                                process_ptr,
                                -thread_delta,
                            );
                            lemma_thread_effective_quota_4k_fold_change_by(
                                threads,
                                old(self).thread_map,
                                self.thread_map,
                                thread_ptr,
                                thread_delta,
                            );
                        } else {
                            lemma_process_effective_quota_4k_fold_eq(
                                processes,
                                old(self).process_map,
                                self.process_map,
                            );
                            lemma_thread_effective_quota_4k_fold_eq(
                                threads,
                                old(self).thread_map,
                                self.thread_map,
                            );
                        }
                        lemma_thread_direct_pending_4k_fold_eq(
                            threads,
                            old(self).thread_map,
                            self.thread_map,
                        );
                        lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                            indirect_threads,
                            old(self).thread_map,
                            self.thread_map,
                            depth,
                        );
                    };
                };
                assert(container_process_allocator_quota_2m_wf(
                    self.container_map,
                    self.process_map,
                    old(self).thread_map,
                    self.allocator_2m_map,
                )) by { crate::kernel::implementation::allocate_free_4k_page::container_process_allocator_quota_2m_wf_forall(); };
                assert(container_process_allocator_quota_2m_wf(
                    self.container_map,
                    self.process_map,
                    self.thread_map,
                    self.allocator_2m_map,
                )) by {
                    reveal(thread_quota_2m_fields_unchanged);
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                };
                assert(container_process_allocator_quota_1g_wf(
                    self.container_map,
                    self.process_map,
                    old(self).thread_map,
                    self.allocator_1g_map,
                )) by { crate::kernel::implementation::allocate_free_4k_page::container_process_allocator_quota_1g_wf_forall(); };
                assert(container_process_allocator_quota_1g_wf(
                    self.container_map,
                    self.process_map,
                    self.thread_map,
                    self.allocator_1g_map,
                )) by {
                    reveal(thread_quota_1g_fields_unchanged);
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
            };
            assert(self.process_management_inv()) by {
                assert(container_process_wf(self.container_map, self.process_map)) by { lemma_no_change_imply_container_process_wf_forall(); };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { lemma_no_change_imply_per_container_process_tree_wf_forall(); };
                assert(process_pcid_allocator_wf(
                    self.container_map,
                    self.process_map,
                    self.pcid_allocator_map,
                )) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by { lemma_no_change_imply_process_cpu_wf_forall(); };
                assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.endpoint_map); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.scheduler_map); };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { container_thread_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.cpu_array); };
            };
            assert(cpu_dirty_map_wf(
                self.container_map,
                self.process_map,
                self.cpu_array,
                self.cpu_tlb,
                self.pagetable_map,
            )) by { lemma_no_change_imply_cpu_dirty_map_wf_forall(); };
            assert(iommu_root_table_process_wf(
                &self.iommu_root_table,
                self.process_map,
                self.iommu_table_map,
            )) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
            assert(process_pci_function_ownership_wf(
                &self.iommu_root_table,
                self.process_map,
            )) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
            assert(iommu_tlb_wf_spec(
                self.iommu_tlb,
                &self.iommu_root_table,
                self.process_map,
                self.iommu_table_map,
            )) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(process_locked_match_lctx);
                reveal(thread_locked_match_lctx);
            };
        }
    }

    pub fn reserve_process_4k_quota_for_thread(
        &mut self,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        amount: usize,
        Tracked(lctx): Tracked<&mut LocalContext>,
        process_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).user_view_locking_state() is Release,
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc == process_ptr,
            old(self).process_map.spec_index(process_ptr).view().quota_4k >= amount,
            amount <= usize::MAX
                - old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set(),
            final(lctx).page_lock_map() =~= old(lctx).page_lock_map(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).process_map.spec_index(process_ptr).view().quota_4k
                == old(self).process_map.spec_index(process_ptr).view().quota_4k
                    - amount,
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    + amount,
            final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed()
                == old(self).process_map.spec_index(process_ptr).being_killed(),
            final(self).thread_map.spec_index(thread_ptr).being_killed()
                == old(self).thread_map.spec_index(thread_ptr).being_killed(),
            process_lock_perm.view().lock_id()
                == final(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            thread_lock_perm.view().lock_id()
                == final(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            process_quota_4k_framed_fields_unchanged(
                old(self).process_map,
                final(self).process_map,
            ),
            thread_process_management_fields_unchanged(
                old(self).thread_map,
                final(self).thread_map,
            ),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view().quota_2m
                == old(self).thread_map.spec_index(thread_ptr).view().quota_2m,
            final(self).thread_map.spec_index(thread_ptr).view().quota_1g
                == old(self).thread_map.spec_index(thread_ptr).view().quota_1g,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index
                == old(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index,
            final(self).thread_map.spec_index(thread_ptr).view().ipc_payload
                == old(self).thread_map.spec_index(thread_ptr).view().ipc_payload,
            final(self).thread_map.spec_index(thread_ptr).view().error_code
                == old(self).thread_map.spec_index(thread_ptr).view().error_code,
            final(self).thread_map.spec_index(thread_ptr).view().trap_frame
                == old(self).thread_map.spec_index(thread_ptr).view().trap_frame,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).page_array == old(self).page_array,
            final(self).cpu_array == old(self).cpu_array,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).allocator_4k_map == old(self).allocator_4k_map,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).default_pagetable == old(self).default_pagetable,
    {
        self.transfer_process_thread_4k_quota(
            process_ptr,
            thread_ptr,
            amount,
            true,
            Tracked(lctx),
            process_lock_perm,
            thread_lock_perm,
        );
    }

    pub fn refund_thread_4k_quota_to_process(
        &mut self,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        amount: usize,
        Tracked(lctx): Tracked<&mut LocalContext>,
        process_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).user_view_locking_state() is Release,
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc == process_ptr,
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= amount as int,
            amount <= usize::MAX
                - old(self).process_map.spec_index(process_ptr).view().quota_4k,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set(),
            final(lctx).page_lock_map() =~= old(lctx).page_lock_map(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).process_map.spec_index(process_ptr).view().quota_4k
                == old(self).process_map.spec_index(process_ptr).view().quota_4k
                    + amount,
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    - amount,
            final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed()
                == old(self).process_map.spec_index(process_ptr).being_killed(),
            final(self).thread_map.spec_index(thread_ptr).being_killed()
                == old(self).thread_map.spec_index(thread_ptr).being_killed(),
            process_lock_perm.view().lock_id()
                == final(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            thread_lock_perm.view().lock_id()
                == final(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            process_quota_4k_framed_fields_unchanged(
                old(self).process_map,
                final(self).process_map,
            ),
            thread_process_management_fields_unchanged(
                old(self).thread_map,
                final(self).thread_map,
            ),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view().quota_2m
                == old(self).thread_map.spec_index(thread_ptr).view().quota_2m,
            final(self).thread_map.spec_index(thread_ptr).view().quota_1g
                == old(self).thread_map.spec_index(thread_ptr).view().quota_1g,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index
                == old(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index,
            final(self).thread_map.spec_index(thread_ptr).view().ipc_payload
                == old(self).thread_map.spec_index(thread_ptr).view().ipc_payload,
            final(self).thread_map.spec_index(thread_ptr).view().error_code
                == old(self).thread_map.spec_index(thread_ptr).view().error_code,
            final(self).thread_map.spec_index(thread_ptr).view().trap_frame
                == old(self).thread_map.spec_index(thread_ptr).view().trap_frame,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).page_array == old(self).page_array,
            final(self).cpu_array == old(self).cpu_array,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).allocator_4k_map == old(self).allocator_4k_map,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).default_pagetable == old(self).default_pagetable,
    {
        self.transfer_process_thread_4k_quota(
            process_ptr,
            thread_ptr,
            amount,
            false,
            Tracked(lctx),
            process_lock_perm,
            thread_lock_perm,
        );
    }
}

}

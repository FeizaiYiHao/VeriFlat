use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        /// Wrapper around `LockedMap::wlock_unless_killed` for `process_map`
        /// that re-establishes `inv()` after the lock attempt. Same shape as
        /// `wlock_container_unless_killed`, but for the process map, which is
        /// touched by the conservation-fold conjunct
        /// `container_process_allocator_quota_wf` — so that piece is discharged
        /// via the per-process set-fold axioms (the lock only moves lock state,
        /// so each process's `process_effective_quota_*` is unchanged ==> the
        /// folded sum is unchanged).
        ///
        #[verifier::spinoff_prover]
        pub fn wlock_process_unless_killed(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).process_map.dom().contains(process_ptr),
                !old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).process_map.lock_id_by_key(process_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only process_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- process_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.perms_wf(),
                process_objects_unlocked(
                    old(self).process_map, old(lctx).thread_id(),
                ) ==> process_objects_unlocked_except(
                    final(self).process_map, final(lctx).thread_id(), process_ptr),
                process_objects_unlocked(
                    old(self).process_map, old(lctx).thread_id(),
                ) && !ret.0 ==> process_objects_unlocked(
                    final(self).process_map, final(lctx).thread_id()),

                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- Failure: process is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == true
                    &&& final(self).process_map.spec_index(process_ptr) == old(self).process_map.spec_index(process_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                    &&& final(lctx).stable_lock_id_set() =~= old(lctx).stable_lock_id_set()
                },

                // ---- Success: process locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).process_map.spec_index(process_ptr),
                        final(self).process_map.spec_index(process_ptr),
                        old(self).process_map.lock_id_by_key(process_ptr),
                        final(lctx),
                        ret.1.unwrap().view(),
                    )
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set()
                    &&& final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set().insert(
                        (
                            ret.1.unwrap().view().ordering_lock_id(),
                            KernelObjId::Process(process_ptr),
                        ),
                    )
                },
        {
            proof {
                assert(old(self).process_map.perms_wf()) by {
                    reveal(process_perms_wf);
                };
            }
            let res = self.process_map.wlock_unless_killed(
                process_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Process(process_ptr)),
            );

            proof {
                assert(self.inv()) by {
                    assert(process_perms_wf(self.process_map)) by {
                        reveal(process_perms_wf);
                    };
                    assert(process_invariant_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        process_lock_op_preserves_invariant_fields(
                            old(self).process_map,
                            self.process_map,
                            process_ptr,
                        );
                    };
                    assert(process_quota_4k_framed_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        reveal(process_invariant_fields_unchanged);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            lemma_no_change_imply_container_process_page_pagetable_wf_forall();
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_process_pages_wf_forall();
                        };
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_4k(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_4k(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_4k_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_2m_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_2m]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_2m(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_2m(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_2m_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_1g_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_1g]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_1g(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_1g(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_1g_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(process_pagetable_match(
                            self.process_map,
                            self.pagetable_map,
                        )) by {
                            lemma_no_change_imply_process_pagetable_match_forall();
                        };
                        assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                    };
                    assert(self.process_management_inv()) by {
                        assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                        assert(container_process_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_container_process_wf_forall();
                        };
                        assert(per_container_process_tree_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_per_container_process_tree_wf_forall();
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            lemma_no_change_imply_process_cpu_wf_forall();
                        };
                        assert(process_thread_wf(
                            self.process_map,
                            self.thread_map,
                        )) by {
                            lemma_no_change_imply_process_thread_wf_forall();
                        };
                    };
                    assert(iommu_root_table_process_wf(&self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                    assert(process_pci_function_ownership_wf(&self.iommu_root_table, self.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                    assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        lemma_no_change_imply_cpu_dirty_map_wf_forall();
                    };
                    reveal(KernelK::inv);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(lock_ensures);
                };
                assert(process_objects_unlocked(
                    old(self).process_map, old(lctx).thread_id(),
                ) ==> process_objects_unlocked_except(
                    self.process_map, lctx.thread_id(), process_ptr,
                )) by {
                    reveal(process_objects_unlocked_except);
                };
                assert(process_objects_unlocked(
                    old(self).process_map, old(lctx).thread_id(),
                ) && !res.0 ==> process_objects_unlocked(
                    self.process_map, lctx.thread_id(),
                )) by {
                    reveal(process_objects_unlocked_except);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            res
        }

        /// Companion of `wlock_process_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `process_map` and re-establishes
        /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
        /// caller already holds the write lock, so this is unconditional.
        #[verifier::spinoff_prover]
        pub fn wunlock_process(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr)
                    .wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).process_map.spec_index(process_ptr)
                        .locking_thread()->Write_lock_id,
                old(lctx).lock_entry_contains_for(
                    lock_id_for_unlock(
                        old(self).process_map.lock_id_by_key(process_ptr),
                        lock_perm.view().ordering_lock_id(), STABLE_LOCK_ID),
                    KernelObjId::Process(process_ptr),
                    STABLE_LOCK_ID,
                ),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (process now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only process_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- process_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.perms_wf(),
                final(self).process_map.spec_index(process_ptr).locking_thread() is None,
                !final(self).process_map.spec_index(process_ptr).locked(),
                final(self).process_map.lock_id_by_key(process_ptr)
                    == old(self).process_map.lock_id_by_key(process_ptr),
                wunlock_ensures(
                    old(self).process_map.spec_index(process_ptr),
                    final(self).process_map.spec_index(process_ptr),
                ),
                process_objects_unlocked_except(
                    old(self).process_map, old(lctx).thread_id(), process_ptr,
                ) ==> process_objects_unlocked(
                    final(self).process_map, final(lctx).thread_id()),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                final(lctx).lock_id_set() == old(lctx).lock_id_set(),

                final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set().remove(
                    (
                        lock_id_for_unlock(
                            old(self).process_map.lock_id_by_key(process_ptr),
                            lock_perm.view().ordering_lock_id(), STABLE_LOCK_ID),
                        KernelObjId::Process(process_ptr),
                    ),
                ),
        {
            proof {
                assert({
                    &&& old(self).process_map.perms_wf()
                    &&& old(self).process_map.spec_index(process_ptr).inv()
                }) by {
                    reveal(process_perms_wf);
                };
            }
            self.process_map.wunlock(
                process_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Process(process_ptr)),
            );
            // Re-establish inv(). Only `process_map[process_ptr]`'s lock state
            // moved; every process payload view, every other entry, and every
            // other KernelK field is byte-equal pre/post. Same template as
            // wlock_process_unless_killed.
            proof {
                assert(self.inv()) by {
                    assert(process_perms_wf(self.process_map)) by {
                        reveal(process_perms_wf);
                    };
                    assert(process_invariant_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        process_lock_op_preserves_invariant_fields(
                            old(self).process_map,
                            self.process_map,
                            process_ptr,
                        );
                    };
                    assert(process_quota_4k_framed_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        reveal(process_invariant_fields_unchanged);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            lemma_no_change_imply_container_process_page_pagetable_wf_forall();
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_process_pages_wf_forall();
                        };
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_4k(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_4k(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_4k_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_2m_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_2m]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_2m(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_2m(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_2m_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_1g_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_1g]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_1g(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_1g(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_1g_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(process_pagetable_match(
                            self.process_map,
                            self.pagetable_map,
                        )) by {
                            lemma_no_change_imply_process_pagetable_match_forall();
                        };
                        assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                    };
                    assert(self.process_management_inv()) by {
                        assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                        assert(container_process_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_container_process_wf_forall();
                        };
                        assert(per_container_process_tree_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_per_container_process_tree_wf_forall();
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            lemma_no_change_imply_process_cpu_wf_forall();
                        };
                        assert(process_thread_wf(
                            self.process_map,
                            self.thread_map,
                        )) by {
                            lemma_no_change_imply_process_thread_wf_forall();
                        };
                    };
                    assert(iommu_root_table_process_wf(&self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                    assert(process_pci_function_ownership_wf(&self.iommu_root_table, self.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                    assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        lemma_no_change_imply_cpu_dirty_map_wf_forall();
                    };
                    reveal(KernelK::inv);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(unlock_ensures);
                };
                assert(process_objects_unlocked_except(
                    old(self).process_map, old(lctx).thread_id(), process_ptr,
                ) ==> process_objects_unlocked(
                    self.process_map, lctx.thread_id(),
                )) by {
                    reveal(process_objects_unlocked_except);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!

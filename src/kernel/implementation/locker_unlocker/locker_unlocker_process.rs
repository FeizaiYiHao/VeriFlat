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
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----

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
                    final(self).process_map, final(lctx).thread_id(), set![process_ptr]),
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
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                        (
                            final(self).process_map.lock_id_by_key(process_ptr),
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
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        process_no_change_imply_memory_management_inv(
                            *old(self),
                            *self,
                        );
                    };
                    assert(self.process_management_inv()) by {
                        process_no_change_imply_process_management_inv(
                            *old(self),
                            *self,
                        );
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
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);

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
                old(lctx).lock_entry_contains(
                    old(self).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (process now released) ----

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
                    old(self).process_map, old(lctx).thread_id(), set![process_ptr],
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


                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    (
                        old(self).process_map.lock_id_by_key(process_ptr),
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
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        process_no_change_imply_memory_management_inv(
                            *old(self),
                            *self,
                        );
                    };
                    assert(self.process_management_inv()) by {
                        process_no_change_imply_process_management_inv(
                            *old(self),
                            *self,
                        );
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
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);

                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!

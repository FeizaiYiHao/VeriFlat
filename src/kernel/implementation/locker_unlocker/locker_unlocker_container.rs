use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_container_unless_killed(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).container_map.dom().contains(container_ptr),
                !old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).container_map.lock_id_by_key(container_ptr)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (success: container locked; failure: no-op) ----

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- container_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.perms_wf(),
                container_objects_unlocked(
                    old(self).container_map, old(lctx).thread_id(),
                ) ==> container_objects_unlocked_except(
                    final(self).container_map, final(lctx).thread_id(), set![container_ptr]),

                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- Failure: container is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == true
                    &&& final(self).container_map.spec_index(container_ptr) == old(self).container_map.spec_index(container_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                },

                // ---- Success: container locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).container_map.spec_index(container_ptr),
                        final(self).container_map.spec_index(container_ptr),
                        old(self).container_map.lock_id_by_key(container_ptr),
                        final(lctx),
                        ret.1.unwrap().view(),
                    )
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                        (
                            final(self).container_map.lock_id_by_key(container_ptr),
                            KernelObjId::Container(container_ptr),
                        ),
                    )
                },
        {
            proof {
                assert(old(self).container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
            }
            let res = self.container_map.wlock_unless_killed(
                container_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Container(container_ptr)),
            );
            proof {
                    assert(container_perms_wf(self.container_map)) by {
                        reveal(container_perms_wf);
                        reveal(container_tree_fields_wf);
                    };
                    assert(container_invariant_fields_unchanged(
                        old(self).container_map,
                        self.container_map,
                    )) by {
                        container_lock_op_preserves_invariant_fields(
                            old(self).container_map,
                            self.container_map,
                            container_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        container_no_change_imply_memory_management_inv(
                            *old(self),
                            *self,
                        );
                    };
                    assert(self.process_management_inv()) by {
                        container_no_change_imply_process_management_inv(
                            *old(self),
                            *self,
                        );
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        container_no_change_imply_cpu_dirty_map_wf(
                            *old(self),
                            *self,
                        );
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

        /// Companion of `wlock_container_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `container_map` and re-establishes
        /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
        /// caller already holds the write lock, so this is unconditional.
        ///
        /// What changes in this lock phase:
        ///  * `container_map[container_ptr]`'s `locking_thread()` becomes
        ///    `None`; its payload view, rodata, and ghost state are all
        ///    preserved (`wunlock_ensures`).
        ///  * Every other entry of `container_map` is byte-equal pre/post
        ///    (`unchanged_except`).
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * the held-lock ledger loses the exact container pair
        ///    entry (encapsulated by `unlock_ensures`).
        pub fn wunlock_container(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).being_killed() == false,
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).container_map.spec_index(container_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(lctx).lock_entry_contains(
                    old(self).container_map.lock_id_by_key(container_ptr),
                    KernelObjId::Container(container_ptr)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (container now released) ----

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- container_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.perms_wf(),
                final(self).container_map.spec_index(container_ptr).locking_thread() is None,
                final(self).container_map.lock_id_by_key(container_ptr)
                    == old(self).container_map.lock_id_by_key(container_ptr),
                wunlock_ensures(
                    old(self).container_map.spec_index(container_ptr),
                    final(self).container_map.spec_index(container_ptr),
                ),
                container_objects_unlocked_except(
                    old(self).container_map, old(lctx).thread_id(), set![container_ptr],
                ) ==> container_objects_unlocked(
                    final(self).container_map, final(lctx).thread_id()),

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
                        old(self).container_map.lock_id_by_key(container_ptr),
                        KernelObjId::Container(container_ptr),
                    ),
                ),
        {
            proof {
                assert({
                    &&& old(self).container_map.perms_wf()
                    &&& old(self).container_map.spec_index(container_ptr).inv()
                }) by {
                    reveal(container_perms_wf);
                };
            }
            self.container_map.wunlock(
                container_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Container(container_ptr)),
            );
            // Re-establish inv(). The only change to `self` since entry is
            // *lock state on container_map[container_ptr]*: it went from
            // WriteLock(us) to None. Every payload view, every rodata, every
            // other LockedMap entry, and every other KernelK field is
            // unchanged. Same proof template as wlock_container_unless_killed.
            proof {
                    assert(container_perms_wf(self.container_map)) by {
                        reveal(container_perms_wf);
                        reveal(container_tree_fields_wf);
                    };
                    assert(container_invariant_fields_unchanged(
                        old(self).container_map,
                        self.container_map,
                    )) by {
                        container_lock_op_preserves_invariant_fields(
                            old(self).container_map,
                            self.container_map,
                            container_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        container_no_change_imply_memory_management_inv(
                            *old(self),
                            *self,
                        );
                    };
                    assert(self.process_management_inv()) by {
                        container_no_change_imply_process_management_inv(
                            *old(self),
                            *self,
                        );
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        container_no_change_imply_cpu_dirty_map_wf(
                            *old(self),
                            *self,
                        );
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

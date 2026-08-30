use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        #[verifier::spinoff_prover]
        pub fn wlock_thread_unless_killed(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).thread_map.dom().contains(thread_ptr),
                !old(lctx).thread_lock_map().dom().contains(thread_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).thread_map.lock_id_by_key(thread_ptr)),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                final(self).pagetable_map == old(self).pagetable_map,
                final(self).iommu_table_map == old(self).iommu_table_map,
                final(self).iommu_root_table == old(self).iommu_root_table,
                final(self).page_array == old(self).page_array,
                final(self).cpu_array == old(self).cpu_array,
                final(self).cpu_tlb == old(self).cpu_tlb,
                final(self).iommu_tlb == old(self).iommu_tlb,
                final(self).root_container == old(self).root_container,
                final(self).container_map == old(self).container_map,
                final(self).scheduler_map == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map == old(self).process_map,
                final(self).endpoint_map == old(self).endpoint_map,
                final(self).allocator_4k_map == old(self).allocator_4k_map,
                final(self).allocator_2m_map == old(self).allocator_2m_map,
                final(self).allocator_1g_map == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,
                final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
                final(self).thread_map.perms_wf(),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                ret.0 == false ==> {
                    &&& old(self).thread_map.spec_index(thread_ptr).being_killed()
                    &&& final(self).thread_map.spec_index(thread_ptr)
                        == old(self).thread_map.spec_index(thread_ptr)
                    &&& ret.1 is None
                    &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
                    &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
                    &&& !final(lctx).thread_lock_map().dom().contains(thread_ptr)
                },
                ret.0 == true ==> {
                    &&& old(self).thread_map.spec_index(thread_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).thread_map.spec_index(thread_ptr),
                        final(self).thread_map.spec_index(thread_ptr),
                        old(self).thread_map.lock_id_by_key(thread_ptr),
                        final(lctx),
                        ret.1.unwrap().view(),
                    )
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .free_quota_pending_clean()
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_clean()
                    &&& typed_lock_maps_inserted(
                        old(lctx), final(lctx), KernelObjId::Thread(thread_ptr),
                        TypedHeldLock {
                            lock_id: final(self).thread_map.lock_id_by_key(thread_ptr),
                            mode: TypedLockMode::Write,
                        },
                    )
                    &&& final(lctx).thread_lock_map().contains_pair(thread_ptr, TypedHeldLock {
                            lock_id: final(self).thread_map.lock_id_by_key(thread_ptr),
                            mode: TypedLockMode::Write,
                        })
                    &&& ret.1.unwrap().view().ordering_lock_id()
                        == final(self).thread_map.lock_id_by_key(thread_ptr)
                },
        {
            proof {
                assert(old(self).thread_map.perms_wf()) by {
                    reveal(thread_perms_wf);
                };
                assert(!old(self).thread_map.spec_index(thread_ptr)
                    .wlocked_by(old(lctx))) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            let res = self.thread_map.wlock_unless_killed(
                thread_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Thread(thread_ptr)),
            );
            proof {
                    assert(thread_perms_wf(self.thread_map)) by {
                        reveal(thread_perms_wf);

                        reveal(thread_free_quota_pending_empty_unless_wlocked);
                        reveal(thread_temp_alloc_empty_unless_wlocked);
                    };
                    assert(thread_invariant_fields_unchanged(
                        old(self).thread_map,
                        self.thread_map,
                    )) by {
                        thread_lock_op_preserves_invariant_fields(
                            old(self).thread_map,
                            self.thread_map,
                            thread_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            container_process_allocator_quota_4k_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            container_process_allocator_quota_2m_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            container_process_allocator_quota_1g_wf_preserved_for_thread_fields_forall();
                        };
                        assert(thread_pages_wf(self.thread_map, self.page_array)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                            lemma_no_change_imply_thread_staged_pages_wf_forall();
                        };
                    };
                    assert(self.process_management_inv()) by {
                        thread_invariant_fields_unchanged_implies_process_management_fields(old(self).thread_map, self.thread_map);
                        assert(thread_caller_callee_wf(self.thread_map)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map); };
                        assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                        assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                        assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.endpoint_map); };
                        assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.scheduler_map); };
                        assert(container_thread_wf(self.container_map, self.thread_map)) by { container_thread_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map); };
                        assert(process_thread_wf(self.process_map, self.thread_map)) by { process_thread_wf_preserved_for_thread_process_management_fields(self.process_map, old(self).thread_map, self.thread_map); };
                        assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.cpu_array); };
                    };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedMap::typed_lock_map_aligned);

                };
                if res.0 {
                    assert(
                        self.thread_map.spec_index(thread_ptr).view()
                            .free_quota_pending_clean()
                        && self.thread_map.spec_index(thread_ptr).view()
                            .temp_alloc_clean()
                    ) by {
                        reveal(thread_perms_wf);
                        reveal(thread_free_quota_pending_empty_unless_wlocked);
                        reveal(thread_temp_alloc_empty_unless_wlocked);

                    };
                }
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            res
        }

        /// Companion of the thread write-lock for the unlock side. Wraps
        /// `LockedMap::wunlock` for `thread_map` and re-establishes `inv()`. Only
        /// the targeted `thread_map` entry's lock state moves; every thread
        /// payload view, every other entry, and every other KernelK field is
        /// byte-equal pre/post — so the conservation folds transport by
        /// byte-equality (thread payloads unchanged).
        ///
        /// The pending-clean protocol: the thread must be `free_quota_pending_clean`
        /// before releasing the write lock, because once unlocked the global
        /// invariant `thread_free_quota_pending_empty_unless_wlocked` demands it.
        /// A freshly-created thread satisfies this (its pendings are all zero).
        #[verifier::spinoff_prover]
        pub fn wunlock_thread(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).thread_map.dom().contains(thread_ptr),
                old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
                !(old(self).thread_map.spec_index(thread_ptr).view().state
                    is IPC_ENDPOINT_TRANSIT),
                typed_lock_map_contains_mode(
                    old(lctx).thread_lock_map(), thread_ptr,
                    TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).thread_map.spec_index(thread_ptr)
                        .locking_thread()->Write_lock_id,
                // The pending-clean protocol: pendings must be flushed before
                // releasing the write lock (see doc comment above).
                old(self).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
                old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (thread now released) ----
                typed_lock_maps_aligned(final(self), final(lctx)),

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
                final(self).process_map       == old(self).process_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- thread_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
                final(self).thread_map.perms_wf(),
                final(self).thread_map.spec_index(thread_ptr).locking_thread() is None,
                !final(self).thread_map.spec_index(thread_ptr).locked(),
                final(self).thread_map.lock_id_by_key(thread_ptr)
                    == old(self).thread_map.lock_id_by_key(thread_ptr),
                wunlock_ensures(
                    old(self).thread_map.spec_index(thread_ptr),
                    final(self).thread_map.spec_index(thread_ptr),
                ),
                typed_lock_maps_removed(
                    old(lctx), final(lctx), KernelObjId::Thread(thread_ptr),
                ),
                !final(lctx).thread_lock_map().dom().contains(thread_ptr),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release (same trap as
                // the NOTE on wunlock_process / LockedArray::wunlock).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                final(lctx).kernel_view_locking_state() is Release,


                unlock_ensures(
                    old(lctx), final(lctx), (),
                    lock_perm.view().lock_id(),
                    KernelObjId::Thread(thread_ptr),
                    old(self).thread_map.lock_id_by_key(thread_ptr),
                ),
        {
            proof {
                assert({
                    &&& old(self).thread_map.perms_wf()
                    &&& old(self).thread_map.spec_index(thread_ptr).inv()
                }) by {
                    reveal(thread_perms_wf);
                };
                assert(old(self).thread_map.spec_index(thread_ptr)
                    .wlocked_by(old(lctx))) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
                assert(old(lctx).lock_entry_contains(
                    old(self).thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr),
                )) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            self.thread_map.wunlock(
                thread_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Thread(thread_ptr)),
            );
            proof {
                    assert(thread_perms_wf(self.thread_map)) by {
                        reveal(thread_perms_wf);

                        reveal(thread_free_quota_pending_empty_unless_wlocked);
                        reveal(thread_temp_alloc_empty_unless_wlocked);
                    };
                    assert(thread_invariant_fields_unchanged(
                        old(self).thread_map,
                        self.thread_map,
                    )) by {
                        thread_lock_op_preserves_invariant_fields(
                            old(self).thread_map,
                            self.thread_map,
                            thread_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            container_process_allocator_quota_4k_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            container_process_allocator_quota_2m_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            container_process_allocator_quota_1g_wf_preserved_for_thread_fields_forall();
                        };
                        assert(thread_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            lemma_no_change_imply_thread_staged_pages_wf_forall();
                        };
                    };
                    assert(self.process_management_inv()) by {
                        thread_invariant_fields_unchanged_implies_process_management_fields(old(self).thread_map, self.thread_map);
                        assert(thread_caller_callee_wf(self.thread_map)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map); };
                        assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                        assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                        assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.endpoint_map); };
                        assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.scheduler_map); };
                        assert(container_thread_wf(self.container_map, self.thread_map)) by { container_thread_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map); };
                        assert(process_thread_wf(self.process_map, self.thread_map)) by { process_thread_wf_preserved_for_thread_process_management_fields(self.process_map, old(self).thread_map, self.thread_map); };
                        assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.cpu_array); };
                    };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedMap::typed_lock_map_aligned);

                };
            }
        }
}
} // verus!

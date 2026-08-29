use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_scheduler(
            &mut self,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                !old(lctx).scheduler_lock_set().contains(scheduler_ptr),
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).scheduler_map.spec_index(scheduler_ptr).container_depth(),
                    process: old(self).scheduler_map.spec_index(scheduler_ptr).process_depth(),
                    major: old(self).scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                    minor: scheduler_ptr,
                }),
                lock_id_aligned(old(self), old(lctx)),
                typed_lock_sets_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (scheduler now locked) ----

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),
                typed_lock_sets_aligned(final(self), final(lctx)),

                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed ----
                final(self).scheduler_map.dom() == old(self).scheduler_map.dom(),
                final(self).scheduler_map.unchanged_except(&old(self).scheduler_map, scheduler_ptr),
                typed_lock_sets_inserted(
                    old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr)),
                final(lctx).scheduler_lock_set().contains(scheduler_ptr),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedMap::wlock) ----
                wlock_ensures(
                    old(self).scheduler_map.spec_index(scheduler_ptr),
                    final(self).scheduler_map.spec_index(scheduler_ptr),
                    LockId{
                        container: old(self).scheduler_map.spec_index(scheduler_ptr).container_depth(),
                        process: old(self).scheduler_map.spec_index(scheduler_ptr).process_depth(),
                        major: old(self).scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                        minor: scheduler_ptr,
                    },
                    final(lctx),
                    ret.view(),
                ),
                final(lctx).lock_id_set()
                    == old(lctx).lock_id_set().insert(
                    (
                        final(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                        KernelObjId::Scheduler(scheduler_ptr),
                    ),
                ),
        {
            proof {
                assert(old(self).scheduler_map.perms_wf()) by {
                    reveal(scheduler_perms_wf);
                };
                assert(wlock_requires(
                    old(self).scheduler_map.spec_index(scheduler_ptr), old(lctx))) by {
                    reveal(typed_lock_sets_aligned);
                };
            }
            let ret = self.scheduler_map.wlock(scheduler_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                    assert(scheduler_perms_wf(
                        self.scheduler_map,
                    )) by {
                        reveal(scheduler_perms_wf);
                    };
                    assert(scheduler_invariant_fields_unchanged(
                        old(self).scheduler_map,
                        self.scheduler_map,
                    )) by {
                        scheduler_lock_op_preserves_invariant_fields(
                            old(self).scheduler_map,
                            self.scheduler_map,
                            scheduler_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_scheduler_wf(
                            self.container_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_scheduler_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                    };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);

                };
                assert(typed_lock_sets_aligned(self, &*lctx)) by {
                    reveal(typed_lock_sets_aligned);
                };
            }
            ret
        }

        pub fn wunlock_scheduler(
            &mut self,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr)
                    .wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).scheduler_map.spec_index(scheduler_ptr)
                        .locking_thread()->Write_lock_id,
                lock_id_aligned(old(self), old(lctx)),
                typed_lock_sets_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (scheduler now released) ----

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),
                typed_lock_sets_aligned(final(self), final(lctx)),

                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed (now unlocked) ----
                final(self).scheduler_map.dom() == old(self).scheduler_map.dom(),
                final(self).scheduler_map.unchanged_except(&old(self).scheduler_map, scheduler_ptr),
                final(self).scheduler_map.spec_index(scheduler_ptr).locking_thread() is None,
                !final(self).scheduler_map.spec_index(scheduler_ptr).locked(),
                final(self).scheduler_map.lock_id_by_key(scheduler_ptr)
                    == old(self).scheduler_map.lock_id_by_key(scheduler_ptr),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                wunlock_ensures(
                    old(self).scheduler_map.spec_index(scheduler_ptr),
                    final(self).scheduler_map.spec_index(scheduler_ptr),
                ),
                typed_lock_sets_removed(
                    old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr)),
                !final(lctx).scheduler_lock_set().contains(scheduler_ptr),
                final(lctx).lock_id_set()
                    == old(lctx).lock_id_set().remove(
                    (
                        old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                        KernelObjId::Scheduler(scheduler_ptr),
                    ),
                ),
                unlock_ensures(
                    old(lctx), final(lctx), (),
                    lock_perm.view().lock_id(),
                    KernelObjId::Scheduler(scheduler_ptr),
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                ),
        {
            proof {
                assert(old(lctx).lock_entry_contains(
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                    KernelObjId::Scheduler(scheduler_ptr),
                )) by {
                    reveal(lock_id_aligned);
                };
                assert({
                    &&& old(self).scheduler_map.perms_wf()
                    &&& old(self).scheduler_map.spec_index(scheduler_ptr).inv()
                }) by {
                    reveal(scheduler_perms_wf);
                };
            }
            self.scheduler_map.wunlock(scheduler_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                    assert(scheduler_perms_wf(
                        self.scheduler_map,
                    )) by {
                        reveal(scheduler_perms_wf);
                    };
                    assert(scheduler_invariant_fields_unchanged(
                        old(self).scheduler_map,
                        self.scheduler_map,
                    )) by {
                        scheduler_lock_op_preserves_invariant_fields(
                            old(self).scheduler_map,
                            self.scheduler_map,
                            scheduler_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_scheduler_wf(
                            self.container_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_scheduler_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                    };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);

                };
                assert(typed_lock_sets_aligned(self, &*lctx)) by {
                    reveal(typed_lock_sets_aligned);
                };
            }
        }

}
} // verus!

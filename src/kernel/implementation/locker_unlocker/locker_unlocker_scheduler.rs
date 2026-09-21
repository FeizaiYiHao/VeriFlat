use vstd::prelude::*;
use vstd::assert_sets_equal;
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
                old(self).sched_mp.dom().contains(scheduler_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                !typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
                old(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(self).sched_mp.spec_index(scheduler_ptr).is_init() == old(self).sched_mp.spec_index(scheduler_ptr).is_init(),
                // ---- Every held lock still matches lctx (scheduler now locked) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only scheduler_map's lock state moves ----
                *final(self) == (KernelK { sched_mp: final(self).sched_mp, ..*old(self) }),
                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed ----
                final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from LockedMap::wlock) ----
                wlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr), final(self).sched_mp.spec_index(scheduler_ptr), LockId{ container: old(self).sched_mp.spec_index(scheduler_ptr).container_depth(), process: old(self).sched_mp.spec_index(scheduler_ptr).process_depth(), major: old(self).sched_mp.spec_index(scheduler_ptr).view().current_lock_major(), minor: scheduler_ptr, }, final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr), TypedHeldLock { lock_id: final(self).sched_mp.lock_id_by_key(scheduler_ptr), mode: TypedLockMode::Write }),
                final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        {
            proof {
                scheduler_perms_wf_at(old(self).sched_mp, scheduler_ptr);
                assert(old(lctx).lock_id_acyclic(LockId{ container: old(self).sched_mp.spec_index(scheduler_ptr).container_depth(), process: old(self).sched_mp.spec_index(scheduler_ptr).process_depth(), major: old(self).sched_mp.spec_index(scheduler_ptr).view().current_lock_major(), minor: scheduler_ptr, })) by { reveal(scheduler_perms_wf); };
                assert(!old(self).sched_mp.spec_index(scheduler_ptr)
                    .wlocked_by_thread(old(lctx).thread_id())) by {
                    if old(self).sched_mp.spec_index(scheduler_ptr)
                        .wlocked_by_thread(old(lctx).thread_id())
                    {
                        assert(typed_lock_map_contains_mode(
                            old(lctx).scheduler_lock_map(),
                            scheduler_ptr,
                            TypedLockMode::Write,
                        )) by {
                            reveal(LockedMap::typed_lock_map_aligned);
                        };
                    }
                };
                assert(!old(self).sched_mp.spec_index(scheduler_ptr)
                    .wlocked_by(&*old(lctx)));
            }
            assert(wlock_requires(self.sched_mp.spec_index(scheduler_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let ret = self.sched_mp.wlock(scheduler_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                assert(scheduler_perms_wf(self.sched_mp)) by { reveal(scheduler_perms_wf); };
                assert(scheduler_invariant_fields_unchanged(old(self).sched_mp, self.sched_mp)) by { scheduler_lock_op_preserves_invariant_fields(old(self).sched_mp, self.sched_mp, scheduler_ptr); };
                assert(self.memory_management_inv()) by { reveal(scheduler_pages_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.process_management_inv()) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)) by { reveal(scheduler_perms_wf); assert(SCHEDULER_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR) by (compute); };
                assert(lctx.pcid_needflush_lock_map().dom().is_empty()) by {
                    let held = lctx.pcid_needflush_lock_map().dom();
                    assert_sets_equal!(
                        held == Set::<(CpuId, Pcid)>::empty(),
                        key => {
                            if held.contains(key) {
                                assert(lctx.lock_entry_contains(self.pcid_needflush.lock_id_by_index(key.0, key.1), KernelObjId::PcidNeedFlush(key.0, key.1))) by { reveal(LockedArray2D::typed_lock_map_aligned); };
                                assert(lctx.lock_id_set().contains((self.pcid_needflush.lock_id_by_index(key.0, key.1), KernelObjId::PcidNeedFlush(key.0, key.1)))) by { reveal(lock_id_set_aligned); };
                            }
                        }
                    );
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
                old(self).sched_mp.dom().contains(scheduler_ptr),
                typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                // ---- Every held lock still matches lctx (scheduler now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only scheduler_map's lock state moves ----
                *final(self) == (KernelK { sched_mp: final(self).sched_mp, ..*old(self) }),
                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed (now unlocked) ----
                final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
                final(self).sched_mp.spec_index(scheduler_ptr).locking_thread() is None,
                !final(self).sched_mp.spec_index(scheduler_ptr).locked(),
                final(self).sched_mp.lock_id_by_key(scheduler_ptr) == old(self).sched_mp.lock_id_by_key(scheduler_ptr),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                wunlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr), final(self).sched_mp.spec_index(scheduler_ptr)),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr)),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr), old(self).sched_mp.lock_id_by_key(scheduler_ptr)),
        {
            proof {
                assert({
                    &&& old(self).sched_mp.perms_wf()
                    &&& old(self).sched_mp.spec_index(scheduler_ptr).inv()
                }) by { reveal(scheduler_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            assert(self.sched_mp.spec_index(scheduler_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            self.sched_mp.wunlock(scheduler_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                assert(scheduler_perms_wf(self.sched_mp)) by { reveal(scheduler_perms_wf); };
                assert(scheduler_invariant_fields_unchanged(old(self).sched_mp, self.sched_mp)) by { scheduler_lock_op_preserves_invariant_fields(old(self).sched_mp, self.sched_mp, scheduler_ptr); };
                assert(self.memory_management_inv()) by { reveal(scheduler_pages_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.process_management_inv()) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        }
}
} // verus!

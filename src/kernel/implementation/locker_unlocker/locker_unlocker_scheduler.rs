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
                !old(lctx).scheduler_lock_map().dom().contains(scheduler_ptr),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < SCHEDULER_LOCK_MAJOR,
                forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
                forall|held_scheduler: RwLockSchedulerPtr| #![trigger old(lctx).scheduler_lock_map().dom().contains(held_scheduler)] old(lctx).scheduler_lock_map().dom().contains(held_scheduler) ==> held_scheduler < scheduler_ptr,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                forall|key: usize|
                    #![trigger old(self).sched_mp.view().spec_index(key)]
                    #![trigger final(self).sched_mp.view().spec_index(key)]
                    old(self).sched_mp.dom().contains(key) ==> {
                        &&& final(self).sched_mp.view().spec_index(key).is_init() == old(self).sched_mp.view().spec_index(key).is_init()
                        &&& final(self).sched_mp.view().spec_index(key).addr() == old(self).sched_mp.view().spec_index(key).addr()
                    },
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                final(self).sched_mp.spec_index(scheduler_ptr).is_init() == old(self).sched_mp.spec_index(scheduler_ptr).is_init(),
                // ---- Every held lock still matches lctx (scheduler now locked) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                // ---- Field framing: only scheduler_map's lock state moves ----
                *final(self) == (KernelK { sched_mp: final(self).sched_mp, ..*old(self) }),
                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed ----
                final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from LockedMap::wlock) ----
                wlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr), final(self).sched_mp.spec_index(scheduler_ptr), LockId{ container: old(self).sched_mp.spec_index(scheduler_ptr).container_depth(), process: old(self).sched_mp.spec_index(scheduler_ptr).process_depth(), major: old(self).sched_mp.spec_index(scheduler_ptr).view().current_lock_major(), minor: scheduler_ptr, }, final(lctx), ret.view()),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr), TypedHeldLock { lock_id: final(self).sched_mp.lock_id_by_key(scheduler_ptr), mode: TypedLockMode::Write }),
        {
            proof {
                scheduler_perms_wf_at(old(self).sched_mp, scheduler_ptr);
                assert(old(lctx).lock_id_acyclic(LockId{ container: old(self).sched_mp.spec_index(scheduler_ptr).container_depth(), process: old(self).sched_mp.spec_index(scheduler_ptr).process_depth(), major: old(self).sched_mp.spec_index(scheduler_ptr).view().current_lock_major(), minor: scheduler_ptr, })) by {
                    reveal(LocalContext::lock_id_acyclic);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                };
                assert(!old(self).sched_mp.spec_index(scheduler_ptr).locked_by_thread(old(lctx).thread_id())) by {
                    if old(self).sched_mp.spec_index(scheduler_ptr).locked_by_thread(old(lctx).thread_id()) {
                        assert(old(lctx).scheduler_lock_map().dom().contains(scheduler_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                    }
                };
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
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by {
                    reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_scheduler_wf);
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
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                // ---- Every held lock still matches lctx (scheduler now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
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
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr)),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr), old(self).sched_mp.lock_id_by_key(scheduler_ptr)),
        {
            proof {
                assert({
                    &&& old(self).sched_mp.perms_wf()
                    &&& old(self).sched_mp.spec_index(scheduler_ptr).inv()
                }) by { reveal(scheduler_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
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
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by {
                    reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_scheduler_wf);
                };
            }
        }
}
} // verus!

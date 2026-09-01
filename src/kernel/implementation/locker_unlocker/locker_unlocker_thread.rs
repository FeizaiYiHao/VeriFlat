use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_thread_unless_killed(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).thr_mp.dom().contains(thread_ptr),
                !old(self).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                thread_lock_acquire_scope(old(self), old(lctx), thread_ptr),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp == old(self).pt_mp,
                final(self).it_mp == old(self).it_mp,
                final(self).irt == old(self).irt,
                final(self).pg_arr == old(self).pg_arr,
                final(self).cpu_arr == old(self).cpu_arr,
                final(self).cpu_tlb == old(self).cpu_tlb,
                final(self).iommu_tlb == old(self).iommu_tlb,
                final(self).rt_ctn == old(self).rt_ctn,
                final(self).ctn_mp == old(self).ctn_mp,
                final(self).sched_mp == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp == old(self).prc_mp,
                final(self).ep_mp == old(self).ep_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
                final(self).thr_mp.perms_wf(),
                thread_objects_unlocked(old(self).thr_mp, old(lctx).thread_id()) ==> thread_objects_unlocked_except(final(self).thr_mp, final(lctx).thread_id(), set![thread_ptr]),
                thread_objects_unlocked(old(self).thr_mp, old(lctx).thread_id()) && !ret.0 ==> thread_objects_unlocked(final(self).thr_mp, final(lctx).thread_id()),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> final(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
                ret.0 == false ==> { &&& old(self).thr_mp.spec_index(thread_ptr).being_killed() &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr) &&& ret.1 is None &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set() &&& typed_lock_maps_unchanged(old(lctx), final(lctx)) },
                ret.0 == true ==> { &&& old(self).thr_mp.spec_index(thread_ptr).being_killed() == false &&& ret.1 is Some &&& wlock_ensures(old(self).thr_mp.spec_index(thread_ptr), final(self).thr_mp.spec_index(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr), final(lctx), ret.1.unwrap().view()) &&& final(self).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean() &&& final(self).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean() &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))) &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr), TypedHeldLock { lock_id: final(self).thr_mp.lock_id_by_key(thread_ptr), mode: TypedLockMode::Write }) &&& forall|cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>| #![trigger old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)] old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints) ==> final(lctx).base_lock_scope(cpus, containers, processes, threads.insert(thread_ptr), endpoints) },
        {
            proof {
                assert(old(self).thr_mp.perms_wf()) by { reveal(thread_perms_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by { reveal(thread_lock_acquire_scope); reveal(LocalContext::base_lock_scope); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(container_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); };
            }
            let res = self.thr_mp.wlock_unless_killed(thread_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Thread(thread_ptr)));
            proof {
                assert(thread_perms_wf(self.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                assert(thread_invariant_fields_unchanged(old(self).thr_mp, self.thr_mp)) by { thread_lock_op_preserves_invariant_fields(old(self).thr_mp, self.thr_mp, thread_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { thread_no_change_imply_memory_management_inv(*old(self), *self); };
                assert(self.process_management_inv()) by { thread_no_change_imply_process_management_inv(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> lctx.held_lock_majors_lt(SCHEDULER_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); assert(PAGE_TABLE_LOCK_MAJOR < SCHEDULER_LOCK_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                if res.0 {
                    reveal(typed_lock_maps_inserted);
                    reveal(LocalContext::base_lock_scope);
                    reveal(LocalContext::object_lock_scope);
                    broadcast use vstd::map::lemma_map_insert_domain;
                    broadcast use vstd::set::lemma_set_insert_same;
                    broadcast use vstd::set::lemma_set_insert_different;
                    assert(
                        self.thr_mp.spec_index(thread_ptr).view()
                            .free_quota_pending_clean()
                        && self.thr_mp.spec_index(thread_ptr).view()
                            .temp_alloc_clean()
                    ) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                }
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
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
        pub fn wunlock_thread(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).thr_mp.dom().contains(thread_ptr),
                old(self).thr_mp.spec_index(thread_ptr).being_killed() == false,
                !(old(self).thr_mp.spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
                old(self).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                // The pending-clean protocol: pendings must be flushed before
                // releasing the write lock (see doc comment above).
                old(self).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
                old(self).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (thread now released) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- thread_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
                final(self).thr_mp.perms_wf(),
                final(self).thr_mp.spec_index(thread_ptr).locking_thread() is None,
                !final(self).thr_mp.spec_index(thread_ptr).locked(),
                final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr),
                wunlock_ensures(old(self).thr_mp.spec_index(thread_ptr), final(self).thr_mp.spec_index(thread_ptr)),
                thread_objects_unlocked_except(old(self).thr_mp, old(lctx).thread_id(), set![thread_ptr]) ==> thread_objects_unlocked(final(self).thr_mp, final(lctx).thread_id()),
                forall|held_thread: RwLockThreadPtr|
                    #![trigger final(self).thr_mp.lock_id_by_key(held_thread)]
                    #![trigger old(self).thr_mp.spec_index(held_thread).wlocked_by(old(lctx))]
                    old(self).thr_mp.dom().contains(held_thread)
                        && held_thread != thread_ptr
                        && old(self).thr_mp.spec_index(held_thread).wlocked_by(old(lctx))
                    ==> final(self).thr_mp.dom().contains(held_thread)
                        && final(self).thr_mp.spec_index(held_thread).wlocked_by(final(lctx))
                        && final(self).thr_mp.lock_id_by_key(held_thread)
                            == old(self).thr_mp.lock_id_by_key(held_thread),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release (same trap as
                // the NOTE on wunlock_process / LockedArray::wunlock).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr)),
                unlock_ensures(old(lctx), final(lctx), (), lock_perm.view().lock_id(), KernelObjId::Thread(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr)),
                forall|held: HeldLock|
                    #![trigger final(lctx).lock_id_set().contains((held.0, held.1))]
                    held.1 != KernelObjId::Thread(thread_ptr)
                    ==> final(lctx).lock_id_set().contains((held.0, held.1))
                        == old(lctx).lock_id_set().contains((held.0, held.1)),
        {
            proof {
                assert({
                    &&& old(self).thr_mp.perms_wf()
                    &&& old(self).thr_mp.spec_index(thread_ptr).inv()
                }) by { reveal(thread_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            self.thr_mp.wunlock(thread_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Thread(thread_ptr)));
            proof {
                assert(thread_perms_wf(self.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                assert(thread_invariant_fields_unchanged(old(self).thr_mp, self.thr_mp)) by { thread_lock_op_preserves_invariant_fields(old(self).thr_mp, self.thr_mp, thread_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { thread_no_change_imply_memory_management_inv(*old(self), *self); };
                assert(self.process_management_inv()) by { thread_no_change_imply_process_management_inv(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        }
}
} // verus!

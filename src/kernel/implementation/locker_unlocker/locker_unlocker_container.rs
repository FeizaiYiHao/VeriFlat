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
                old(self).ctn_mp.dom().contains(container_ptr),
                !old(self).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                container_lock_acquire_scope(old(self), old(lctx), container_ptr),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (success: container locked; failure: no-op) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only container_map's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- container_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
                final(self).ctn_mp.perms_wf(),
                container_objects_unlocked(old(self).ctn_mp, old(lctx).thread_id()) ==> container_objects_unlocked_except(final(self).ctn_mp, final(lctx).thread_id(), set![container_ptr]),
                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                // ---- Failure: container is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).ctn_mp.spec_index(container_ptr).being_killed() == true
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                    &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
                },

                // ---- Success: container locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).ctn_mp.spec_index(container_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(old(self).ctn_mp.spec_index(container_ptr), final(self).ctn_mp.spec_index(container_ptr), old(self).ctn_mp.lock_id_by_key(container_ptr), final(lctx), ret.1.unwrap().view())
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr)))
                    &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(container_ptr), TypedHeldLock { lock_id: final(self).ctn_mp.lock_id_by_key(container_ptr), mode: TypedLockMode::Write })
                    &&& container_lock_held_scope(final(self), final(lctx), container_ptr)
                },
        {
            proof {
                assert(old(self).ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).ctn_mp.lock_id_by_key(container_ptr))) by { reveal(container_lock_acquire_scope); reveal(LocalContext::base_lock_scope); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(container_cpu_wf); };
            }
            let res = self.ctn_mp.wlock_unless_killed(container_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Container(container_ptr)));
            proof {
                assert(container_perms_wf(self.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(container_invariant_fields_unchanged(old(self).ctn_mp, self.ctn_mp)) by { container_lock_op_preserves_invariant_fields(old(self).ctn_mp, self.ctn_mp, container_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { container_no_change_imply_memory_management_inv(*old(self), *self); };
                assert(container_process_wf(self.ctn_mp, self.prc_mp)) by { reveal(container_process_wf); };
                assert(self.process_management_inv()) by { container_no_change_imply_process_management_inv(*old(self), *self); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { container_no_change_imply_cpu_dirty_map_wf(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                if res.0 {
                    assert(container_lock_held_scope(self, lctx, container_ptr)) by { reveal(container_lock_acquire_scope); reveal(container_lock_held_scope); reveal(cpu_lock_held_scope); reveal(LocalContext::base_lock_scope); };
                }
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) ==> lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(container_perms_wf); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
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
                old(self).ctn_mp.dom().contains(container_ptr),
                old(self).ctn_mp.spec_index(container_ptr).being_killed() == false,
                !old(self).ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty(),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(self).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (container now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only container_map's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- container_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
                final(self).ctn_mp.perms_wf(),
                final(self).ctn_mp.spec_index(container_ptr).locking_thread() is None,
                final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr),
                wunlock_ensures(old(self).ctn_mp.spec_index(container_ptr), final(self).ctn_mp.spec_index(container_ptr)),
                container_objects_unlocked_except(old(self).ctn_mp, old(lctx).thread_id(), set![container_ptr]) ==> container_objects_unlocked(final(self).ctn_mp, final(lctx).thread_id()),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Container(container_ptr)),
        {
            proof {
                assert({
                    &&& old(self).ctn_mp.perms_wf()
                    &&& old(self).ctn_mp.spec_index(container_ptr).inv()
                }) by { reveal(container_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            self.ctn_mp.wunlock(container_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Container(container_ptr)));
            // Re-establish inv(). The only change to `self` since entry is
            // *lock state on container_map[container_ptr]*: it went from
            // WriteLock(us) to None. Every payload view, every rodata, every
            // other LockedMap entry, and every other KernelK field is
            // unchanged. Same proof template as wlock_container_unless_killed.
            proof {
                assert(container_perms_wf(self.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(container_invariant_fields_unchanged(old(self).ctn_mp, self.ctn_mp)) by { container_lock_op_preserves_invariant_fields(old(self).ctn_mp, self.ctn_mp, container_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { container_no_change_imply_memory_management_inv(*old(self), *self); };
                assert(container_process_wf(self.ctn_mp, self.prc_mp)) by { reveal(container_process_wf); };
                assert(self.process_management_inv()) by { container_no_change_imply_process_management_inv(*old(self), *self); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { container_no_change_imply_cpu_dirty_map_wf(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!

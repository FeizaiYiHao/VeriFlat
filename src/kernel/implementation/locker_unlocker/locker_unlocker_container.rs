use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_container_unless_killed(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Option<Tracked<LockPerm>>)
            requires
                old(self).inv(),
                old(self).ctn_mp.dom().contains(container_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).page_lock_map().dom().is_empty(),
                old(lctx).container_lock_map().dom().is_empty(),
                old(lctx).process_lock_map().dom().is_empty(),
                old(lctx).thread_lock_map().dom().is_empty(),
                old(lctx).endpoint_lock_map().dom().is_empty(),
                old(lctx).scheduler_lock_map().dom().is_empty(),
                old(lctx).pcid_allocator_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).pagetable_lock_map().dom().is_empty(),
                old(lctx).iommu_table_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
                old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                !old(lctx).cpu_lock_map().dom().is_empty(),
                (forall|held_cpu_id: CpuId|
                    #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
                    old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> {
                        &&& index_valid(NUM_CPUS, held_cpu_id)
                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == container_ptr
                        &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                    }),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (success: container locked; failure: no-op) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only container_map's lock state moves ----
                *final(self) == (KernelK { ctn_mp: final(self).ctn_mp, ..*old(self) }),
                // ---- container_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
                final(self).ctn_mp.perms_wf(),
                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                // ---- Failure: container is being killed; complete no-op ----
                ret is None ==>
                {
                    &&& old(self).ctn_mp.spec_index(container_ptr).being_killed() == true
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                    &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
                },

                // ---- Success: container locked by us, perm returned ----
                ret is Some ==>
                {
                    &&& old(self).ctn_mp.spec_index(container_ptr).being_killed() == false
                    &&& wlock_ensures(old(self).ctn_mp.spec_index(container_ptr), final(self).ctn_mp.spec_index(container_ptr), old(self).ctn_mp.lock_id_by_key(container_ptr), final(lctx), ret.unwrap().view())
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr)))
                    &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(container_ptr), TypedHeldLock { lock_id: final(self).ctn_mp.lock_id_by_key(container_ptr), mode: TypedLockMode::Write })
                },
        {
            proof {
                container_perms_wf_at(old(self).ctn_mp, container_ptr);
                assert(old(lctx).lock_id_acyclic(old(self).ctn_mp.lock_id_by_key(container_ptr))) by { reveal(lock_id_set_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(container_cpu_wf); };
                assert(!typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write)) by { reveal(typed_lock_map_contains_mode); };
                assert(!old(self).ctn_mp.spec_index(container_ptr)
                    .wlocked_by_thread(old(lctx).thread_id())) by {
                    if old(self).ctn_mp.spec_index(container_ptr)
                        .wlocked_by_thread(old(lctx).thread_id())
                    {
                        assert(old(lctx).container_lock_map().dom()
                            .contains(container_ptr)) by {
                            reveal(typed_lock_maps_aligned);
                            reveal(LockedMap::typed_lock_map_aligned);
                        };
                    }
                };
                assert(!old(self).ctn_mp.spec_index(container_ptr)
                    .wlocked_by(&*old(lctx))) by {
                    reveal(RwLock::wlocked_by);
                    reveal(RwLock::wlocked_by_thread);
                };
            }
            assert(wlock_requires(self.ctn_mp.spec_index(container_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let res = self.ctn_mp.wlock_unless_killed(container_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Container(container_ptr)));
            proof {
                assert(container_perms_wf(self.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(container_invariant_fields_unchanged(old(self).ctn_mp, self.ctn_mp)) by { container_lock_op_preserves_invariant_fields(old(self).ctn_mp, self.ctn_mp, container_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(*old(self), *self); };
                assert(container_process_wf(self.ctn_mp, self.prc_mp)) by { reveal(container_process_wf); };
                assert(self.process_management_inv()) by { process_management_inv_preserved_for_container_invariant_fields(*old(self), *self); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_container_invariant_fields(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) ==> lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by { reveal(container_perms_wf); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
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
                typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (container now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                // ---- Field framing: only container_map's lock state moves ----
                *final(self) == (KernelK { ctn_mp: final(self).ctn_mp, ..*old(self) }),
                // ---- container_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
                wunlock_ensures(old(self).ctn_mp.spec_index(container_ptr), final(self).ctn_mp.spec_index(container_ptr)),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::Container(container_ptr), old(self).ctn_mp.lock_id_by_key(container_ptr)),
        {
            proof {
                assert({
                    &&& old(self).ctn_mp.perms_wf()
                    &&& old(self).ctn_mp.spec_index(container_ptr).inv()
                }) by { reveal(container_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            assert(self.ctn_mp.spec_index(container_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
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
                assert(self.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(*old(self), *self); };
                assert(container_process_wf(self.ctn_mp, self.prc_mp)) by { reveal(container_process_wf); };
                assert(self.process_management_inv()) by { process_management_inv_preserved_for_container_invariant_fields(*old(self), *self); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_container_invariant_fields(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!

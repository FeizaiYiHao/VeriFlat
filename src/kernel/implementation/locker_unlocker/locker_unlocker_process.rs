use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        /// Wrapper around `LockedMap::wlock_unless_killed` for `process_map`
        /// that re-establishes `inv()` after the lock attempt. Same shape as
        /// `wlock_container_unless_killed`, but for the process map, which is
        /// touched by the conservation-fold conjunct
        /// `container_process_allocator_quota_wf` — so that piece is discharged
        /// via the per-process set-fold lemmas (the lock only moves lock state,
        /// so each process's `process_effective_quota_*` is unchanged ==> the
        /// folded sum is unchanged).
        ///
        pub fn wlock_process_unless_killed(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Ghost(cpu_id): Ghost<CpuId>,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Option<Tracked<LockPerm>>)
            requires
                old(self).inv(),
                old(self).prc_mp.dom().contains(process_ptr),
                !old(lctx).process_lock_map().dom().contains(process_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                {
                    let cpus = old(lctx).cpu_lock_map().dom();
                    let container_ptr = old(self).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container;
                    let containers = old(lctx).container_lock_map().dom();
                    let pcid_allocators = old(lctx).pcid_allocator_lock_map().dom();
                    &&& (forall|held_cpu_id: CpuId|
                        #![trigger cpus.contains(held_cpu_id)]
                        cpus.contains(held_cpu_id) ==> {
                            &&& index_valid(NUM_CPUS, held_cpu_id)
                            &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == container_ptr
                            &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                            &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is None || old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process == Some(process_ptr)
                        })
                    &&& cpus.contains(cpu_id)
                    &&& old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
                    &&& {
                            &&& old(lctx).page_lock_map().dom().is_empty()
                            &&& old(lctx).process_lock_map().dom().is_empty()
                            &&& old(lctx).thread_lock_map().dom().is_empty()
                            &&& old(lctx).endpoint_lock_map().dom().is_empty()
                            &&& old(lctx).scheduler_lock_map().dom().is_empty()
                            &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                            &&& old(lctx).pagetable_lock_map().dom().is_empty()
                            &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                            &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                            &&& containers.subset_of(set![container_ptr])
                            &&& pcid_allocators.subset_of(set![old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator])
                    }
                },
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                // ---- Field framing: only process_map's lock state moves ----
                *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
                // ---- process_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
                final(self).prc_mp.perms_wf(),
                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- Failure: process is being killed; complete no-op ----
                ret is None ==>
                {
                    &&& old(self).prc_mp.spec_index(process_ptr).being_killed() == true
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                    &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
                },

                // ---- Success: process locked by us, perm returned ----
                ret is Some ==>
                {
                    &&& old(self).prc_mp.spec_index(process_ptr).being_killed() == false
                    &&& wlock_ensures(old(self).prc_mp.spec_index(process_ptr), final(self).prc_mp.spec_index(process_ptr), old(self).prc_mp.lock_id_by_key(process_ptr), final(lctx), ret.unwrap().view())
                    &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Process(process_ptr), TypedHeldLock { lock_id: final(self).prc_mp.lock_id_by_key(process_ptr), mode: TypedLockMode::Write })
                },
        {
            proof {
                process_perms_wf_at(old(self).prc_mp, process_ptr);
                assert(old(lctx).lock_id_acyclic(old(self).prc_mp.lock_id_by_key(process_ptr))) by { reveal(LocalContext::lock_id_acyclic); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); reveal(container_pcid_allocator_wf); reveal(container_allocator_wf); reveal(pcid_allocator_perms_wf); reveal(allocator_perms_wf); };
                assert(!old(self).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id())) by {
                    if old(self).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id()) {
                        assert(old(lctx).process_lock_map().dom().contains(process_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                    }
                };
            }
            assert(wlock_requires(self.prc_mp.spec_index(process_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let res = self.prc_mp.wlock_unless_killed(process_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Process(process_ptr)));

            proof {
                assert(process_perms_wf(self.prc_mp)) by { reveal(process_perms_wf); };
                assert(process_invariant_fields_unchanged(old(self).prc_mp, self.prc_mp)) by { process_lock_op_preserves_invariant_fields(old(self).prc_mp, self.prc_mp, process_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { memory_management_inv_preserved_for_process_invariant_fields(*old(self), *self); };
                assert(process_thread_wf(self.prc_mp, self.thr_mp)) by { reveal(process_thread_wf); reveal(process_empty_lists_wlocked); };
                assert(self.process_management_inv()) by { process_management_inv_preserved_for_process_invariant_fields(*old(self), *self); };
                assert(iommu_root_table_process_wf(&self.irt, self.prc_mp, self.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(process_pci_function_ownership_wf(&self.irt, self.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.irt, self.prc_mp, self.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_process_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
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
                old(self).prc_mp.dom().contains(process_ptr),
                old(self).prc_mp.spec_index(process_ptr).being_killed() == false,
                old(self).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0
                    || (old(self).prc_mp.spec_index(process_ptr).view().zombie
                        && old(self).prc_mp.spec_index(process_ptr).view().children.view().len() != 0),
                typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                kernel_k_to_nonlock_kernel_u(*final(self)) == kernel_k_to_nonlock_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (process now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                // ---- Field framing: only process_map's lock state moves ----
                *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
                // ---- process_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
                final(self).prc_mp.perms_wf(),
                final(self).prc_mp.spec_index(process_ptr).locking_thread() is None,
                !final(self).prc_mp.spec_index(process_ptr).locked(),
                final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr),
                wunlock_ensures(old(self).prc_mp.spec_index(process_ptr), final(self).prc_mp.spec_index(process_ptr)),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(process_ptr)),
        {
            proof {
                assert({
                    &&& old(self).prc_mp.perms_wf()
                    &&& old(self).prc_mp.spec_index(process_ptr).inv()
                }) by { reveal(process_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).prc_mp.lock_id_by_key(process_ptr), KernelObjId::Process(process_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
            assert(self.prc_mp.spec_index(process_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            self.prc_mp.wunlock(process_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Process(process_ptr)));
            // Re-establish inv(). Only `process_map[process_ptr]`'s lock state
            // moved; every process payload view, every other entry, and every
            // other KernelK field is byte-equal pre/post. Same template as
            // wlock_process_unless_killed.
            proof {
                assert(process_perms_wf(self.prc_mp)) by { reveal(process_perms_wf); };
                assert(process_invariant_fields_unchanged(old(self).prc_mp, self.prc_mp)) by { process_lock_op_preserves_invariant_fields(old(self).prc_mp, self.prc_mp, process_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { memory_management_inv_preserved_for_process_invariant_fields(*old(self), *self); };
                assert(process_thread_wf(self.prc_mp, self.thr_mp)) by { reveal(process_thread_wf); reveal(process_empty_lists_wlocked); };
                assert(self.process_management_inv()) by { process_management_inv_preserved_for_process_invariant_fields(*old(self), *self); };
                assert(iommu_root_table_process_wf(&self.irt, self.prc_mp, self.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(process_pci_function_ownership_wf(&self.irt, self.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.irt, self.prc_mp, self.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_process_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                assert(kernel_k_to_nonlock_kernel_u(*self) == kernel_k_to_nonlock_kernel_u(*old(self))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(self), self); };
            }
        }
}
} // verus!

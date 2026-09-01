use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                wlock_requires(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                container_lock_held_scope(old(self), old(lctx), old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                // ---- Every held lock still matches lctx (quota now locked) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
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
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- allocator_4k_map: dom unchanged; only the targeted entry's quota lock state changed ----
                final(self).allc_4k_mp.dom() == old(self).allc_4k_mp.dom(),
                final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
                final(self).allc_4k_mp.perms_wf(),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
                allocator_objects_unlocked(old(self).allc_4k_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked_except_quota(final(self).allc_4k_mp, final(lctx).thread_id(), alloc_ptr_4k),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_quota) ----
                wlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k), TypedHeldLock { lock_id: final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), mode: TypedLockMode::Write }),
        {
            proof {
                assert(old(self).allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id())) by { reveal(container_lock_held_scope); reveal(LocalContext::base_lock_scope); reveal(LocalContext::object_lock_scope); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(container_cpu_wf); reveal(container_allocator_wf); reveal(container_perms_wf); reveal(allocator_perms_wf); };
            }
            let ret = self.allc_4k_mp.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_4k_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_4k_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                    assert(container_process_allocator_quota_4k_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
                    assert(container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                    assert(allocator_free_page_ptrs_wf(self.allc_4k_mp)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(container_allocator_free_4k_page_wf(self.allc_4k_mp, self.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            }
            ret
        }

        /// Companion of `wlock_quota_4k` for the unlock side. Wraps
        /// `UnLockedMap::wunlock_quota` for `allocator_4k_map` and
        /// re-establishes `inv()` immediately afterwards. Same template as
        /// `wlock_quota_4k`; the quota's `view()` is preserved by
        /// `wunlock_ensures`, so the fold conjunct holds via the same set-fold
        /// axioms.
        pub fn wunlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.inv(),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.wlocked_by(old(lctx)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                // ---- Every held lock still matches lctx (quota now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
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
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- allocator_4k_map: dom unchanged; only the targeted entry's quota lock state changed (now unlocked) ----
                final(self).allc_4k_mp.dom() == old(self).allc_4k_mp.dom(),
                final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                !final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.locked_by_thread(final(lctx).thread_id()),
                allocator_objects_unlocked_except_quota(old(self).allc_4k_mp, old(lctx).thread_id(), alloc_ptr_4k) ==> allocator_objects_unlocked(final(self).allc_4k_mp, final(lctx).thread_id()),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_quota) ----
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(),
                wunlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
        {
            proof {
                assert(old(self).allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)))) by { reveal(lock_id_set_aligned); };
            }
            self.allc_4k_mp.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_4k_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_4k_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                    assert(container_process_allocator_quota_4k_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
                    assert(container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                    assert(allocator_free_page_ptrs_wf(self.allc_4k_mp)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(container_allocator_free_4k_page_wf(self.allc_4k_mp, self.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            }
        }
}
} // verus!

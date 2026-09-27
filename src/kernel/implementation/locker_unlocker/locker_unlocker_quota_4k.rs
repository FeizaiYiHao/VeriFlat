use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_allocator_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                !typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < QUOTA_MAJOR,
                old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { allc_4k_mp: final(self).allc_4k_mp, ..*old(self) }),
                final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
                final(self).allc_4k_mp.perms_wf(),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), final(lctx), ret.view()),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k), TypedHeldLock { lock_id: final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), mode: TypedLockMode::Write }),
        {
            proof {
                allocator_perms_wf_at(old(self).allc_4k_mp, alloc_ptr_4k);
                assert(old(lctx).lock_id_acyclic(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id())) by {
                    reveal(LocalContext::lock_id_acyclic);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                };
            }
            assert(wlock_requires(self.allc_4k_mp.spec_index(alloc_ptr_4k).quota, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
            let ret = self.allc_4k_mp.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    lemma_allocator_pages_wf_preserved_for_allocator_quota_value_framed_fields_forall();
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_allocator_wf);
                    lemma_container_allocator_wf_preserved_for_allocator_quota_value_framed_fields_forall();
                    lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall();
                    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self);
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
            }
            ret
        }

        pub fn wunlock_allocator_quota_4k(
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
                typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { allc_4k_mp: final(self).allc_4k_mp, ..*old(self) }),
                final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                !final(lctx).allocator_quota_4k_lock_map().dom().contains(alloc_ptr_4k),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
                // `unlock_ensures` owns the Acquire -> Release phase transition.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(),
                wunlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
        {
            proof {
                assert(old(self).allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
            }
            assert(self.allc_4k_mp.spec_index(alloc_ptr_4k).quota.wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
            self.allc_4k_mp.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    lemma_allocator_pages_wf_preserved_for_allocator_quota_value_framed_fields_forall();
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_allocator_wf);
                    lemma_container_allocator_wf_preserved_for_allocator_quota_value_framed_fields_forall();
                    lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall();
                    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self);
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
            }
        }
}
} // verus!

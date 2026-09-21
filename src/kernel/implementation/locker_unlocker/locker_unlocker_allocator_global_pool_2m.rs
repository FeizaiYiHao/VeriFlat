use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_allocator_global_pool_2m(
            &mut self,
            alloc_ptr_2m: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allc_2m_mp.dom().contains(alloc_ptr_2m),
                !typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedLockMode::Write),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{ container: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().container_depth(), process: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().process_depth(), major: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().current_lock_major(), minor: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().lock_minor(), }),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                *final(self) == (KernelK { allc_2m_mp: final(self).allc_2m_mp, ..*old(self) }),
                final(self).allc_2m_mp.unchanged_except(&old(self).allc_2m_mp, alloc_ptr_2m),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf(),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages,
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool, final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool, LockId{ container: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().container_depth(), process: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().process_depth(), major: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().current_lock_major(), minor: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().lock_minor(), }, final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr_2m))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr_2m), TypedHeldLock { lock_id: final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write }),
        {
            proof {
                assert(old(self).allc_2m_mp.perms_wf() && old(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf()) by { reveal(allocator_perms_wf); };
                assert(wlock_requires(self.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool, &*lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            }
            let ret = self.allc_2m_mp.wlock_global_pool(alloc_ptr_2m, Tracked(&mut *lctx), Ghost(PageSize::SZ2m));

            proof {
                assert(allocator_perms_wf(self.allc_2m_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    reveal(allocator_2m_pages_wf);
                    reveal(container_process_allocator_quota_2m_wf);
                    reveal(container_allocator_wf);
                    lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall();
                    lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*old(self), *self);
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        pub fn wunlock_allocator_global_pool_2m(
            &mut self,
            alloc_ptr_2m: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allc_2m_mp.dom().contains(alloc_ptr_2m),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { allc_2m_mp: final(self).allc_2m_mp, ..*old(self) }),
                final(self).allc_2m_mp.unchanged_except(&old(self).allc_2m_mp, alloc_ptr_2m),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf(),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages,
                wunlock_ensures(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool, final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr_2m), old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id()),
        {
            proof {
                assert({
                    &&& old(self).allc_2m_mp.perms_wf()
                    &&& old(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf()
                }) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr_2m))) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr_2m)))) by { reveal(lock_id_set_aligned); };
            }
            assert(self.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            self.allc_2m_mp.wunlock_global_pool(alloc_ptr_2m, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ2m));

            proof {
                assert(allocator_perms_wf(self.allc_2m_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    reveal(allocator_2m_pages_wf);
                    reveal(container_process_allocator_quota_2m_wf);
                    reveal(container_allocator_wf);
                    lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall();
                    lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*old(self), *self);
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!

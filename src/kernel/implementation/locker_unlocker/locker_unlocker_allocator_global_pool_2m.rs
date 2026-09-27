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
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < ALLOCATOR_GLOBAL_POLL_MAJOR,
                forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
                old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
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
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr_2m), TypedHeldLock { lock_id: final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write }),
        {
            proof {
                assert(old(self).allc_2m_mp.perms_wf() && old(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf()) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_id_acyclic(LockId{ container: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().container_depth(), process: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().process_depth(), major: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().current_lock_major(), minor: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().lock_minor(), })) by {
                    reveal(LocalContext::lock_id_acyclic);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                };
                assert(wlock_requires(self.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool, &*lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            }
            let ret = self.allc_2m_mp.wlock_global_pool(alloc_ptr_2m, Tracked(&mut *lctx), Ghost(PageSize::SZ2m));

            proof {
                assert(allocator_perms_wf(self.allc_2m_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { reveal(allocator_2m_pages_wf); };
                assert(allocator_free_page_ptrs_wf(self.allc_2m_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
                assert(container_allocator_free_2m_page_wf(self.allc_2m_mp, self.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*old(self), *self); };
                assert(self.memory_management_inv()) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
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
            ensures
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
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
            }
            assert(self.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            self.allc_2m_mp.wunlock_global_pool(alloc_ptr_2m, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ2m));

            proof {
                assert(allocator_perms_wf(self.allc_2m_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { reveal(allocator_2m_pages_wf); };
                assert(allocator_free_page_ptrs_wf(self.allc_2m_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
                assert(container_allocator_free_2m_page_wf(self.allc_2m_mp, self.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*old(self), *self); };
                assert(self.memory_management_inv()) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
            }
        }
}
} // verus!

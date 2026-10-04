use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_allocator_cache_4k(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cache_cpu: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
            index_valid(NUM_CPUS, cache_cpu),
            !typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cache_cpu), TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < ALLOCATOR_CACHE_MAJOR,
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            forall|held_cache: (RwLockPageAllocatorPtr, CpuId)| #![trigger old(lctx).allocator_cache_4k_lock_map().dom().contains(held_cache)] old(lctx).allocator_cache_4k_lock_map().dom().contains(held_cache) ==> held_cache.1 < cache_cpu,
            forall|held_cache: (RwLockPageAllocatorPtr, CpuId)| #![trigger old(lctx).allocator_cache_2m_lock_map().dom().contains(held_cache)] old(lctx).allocator_cache_2m_lock_map().dom().contains(held_cache) ==> held_cache.1 < cache_cpu,
            forall|held_cache: (RwLockPageAllocatorPtr, CpuId)| #![trigger old(lctx).allocator_cache_1g_lock_map().dom().contains(held_cache)] old(lctx).allocator_cache_1g_lock_map().dom().contains(held_cache) ==> held_cache.1 < cache_cpu,
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
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(), final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(), LockId { container: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).container_depth(), process: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).process_depth(), major: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(), minor: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).lock_minor() }, final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu), TypedHeldLock { lock_id: final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.lock_id_by_index(cache_cpu), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).allc_4k_mp.perms_wf() && old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf()) by { reveal(allocator_perms_wf); };
            assert(old(lctx).lock_id_acyclic(LockId { container: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).container_depth(), process: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).process_depth(), major: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(), minor: old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).lock_minor() })) by {
                reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
            };
            assert(wlock_requires(self.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(), &*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        }
        let ret = self.allc_4k_mp.wlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));
        proof {
            assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
            assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_cache_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k, cache_cpu); };
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

    pub fn wunlock_allocator_cache_4k(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cache_cpu: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
        lock_perm: Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
            index_valid(NUM_CPUS, cache_cpu),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cache_cpu), TypedLockMode::Write),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { allc_4k_mp: final(self).allc_4k_mp, ..*old(self) }),
            final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
            final(self).allc_4k_mp.perms_wf(),
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
            wunlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(), final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu), old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).lock_id()),
    {
        proof {
            assert({
                &&& old(self).allc_4k_mp.perms_wf()
                &&& old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf()
            }) by { reveal(allocator_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.lock_id_by_index(cache_cpu), KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu))) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        }
        assert(self.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        self.allc_4k_mp.wunlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));
        proof {
            assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
            assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_cache_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k, cache_cpu); };
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
}

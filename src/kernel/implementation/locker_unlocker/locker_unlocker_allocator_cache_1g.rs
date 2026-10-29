#[cfg(verus_keep_ghost)]
use super::locker_unlocker_allocator_eof::allocator_1g_lock_op_eof;
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_allocator_cache_1g(&mut self, alloc_ptr_1g: RwLockPageAllocatorPtr, cache_cpu: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_1g_mp.dom().contains(alloc_ptr_1g),
            index_valid(NUM_CPUS, cache_cpu),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            forall|held_cache: (RwLockPageAllocatorPtr, CpuId)| #![trigger old(lctx).allocator_cache_1g_lock_map().dom().contains(held_cache)] old(lctx).allocator_cache_1g_lock_map().dom().contains(held_cache) ==> held_cache.1 < cache_cpu,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { allc_1g_mp: final(self).allc_1g_mp, ..*old(self) }),
            final(self).allc_1g_mp.unchanged_except(&old(self).allc_1g_mp, alloc_ptr_1g),
            final(self).allc_1g_mp.perms_wf(),
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).wf(),
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.unchanged_except(&old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches, cache_cpu),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view(), final(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view(),
                old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.lock_id_by_index(cache_cpu), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ1g, alloc_ptr_1g, cache_cpu), TypedHeldLock { lock_id: final(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.lock_id_by_index(cache_cpu), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).allc_1g_mp.perms_wf() && old(self).allc_1g_mp.spec_index(alloc_ptr_1g).inv()) by { allocator_perms_wf_map(old(self).allc_1g_mp); allocator_perms_wf_at(old(self).allc_1g_mp, alloc_ptr_1g); };
            assert(old(lctx).lock_id_acyclic(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.lock_id_by_index(cache_cpu))) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
            };
            assert(!self.allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view().locked_by_thread(lctx.thread_id())
                && wlock_requires(self.allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view(), &*lctx)) by {
                reveal(UnLockedMap::typed_cache_lock_map_aligned); assert(!lctx.allocator_cache_1g_lock_map().dom().contains((alloc_ptr_1g, cache_cpu)));
            };
        }
        let ret = self.allc_1g_mp.wlock_cache(alloc_ptr_1g, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ1g));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_1g_mp, self.allc_1g_mp)) by { allocator_cache_lock_op_preserves_invariant_fields(old(self).allc_1g_mp, self.allc_1g_mp, alloc_ptr_1g, cache_cpu); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_1g_lock_op_eof(*old(self), *self, alloc_ptr_1g);
        }
        ret
    }

    pub fn wunlock_allocator_cache_1g(&mut self, alloc_ptr_1g: RwLockPageAllocatorPtr, cache_cpu: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_1g_mp.dom().contains(alloc_ptr_1g),
            index_valid(NUM_CPUS, cache_cpu),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_cache_1g_lock_map(), (alloc_ptr_1g, cache_cpu), TypedLockMode::Write),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { allc_1g_mp: final(self).allc_1g_mp, ..*old(self) }),
            final(self).allc_1g_mp.unchanged_except(&old(self).allc_1g_mp, alloc_ptr_1g),
            final(self).allc_1g_mp.perms_wf(),
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).wf(),
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.unchanged_except(&old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches, cache_cpu),
            wunlock_ensures(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view(), final(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ1g, alloc_ptr_1g, cache_cpu), old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).lock_id()),
    {
        proof {
            assert(old(self).allc_1g_mp.perms_wf() && old(self).allc_1g_mp.spec_index(alloc_ptr_1g).inv()) by { allocator_perms_wf_map(old(self).allc_1g_mp); allocator_perms_wf_at(old(self).allc_1g_mp, alloc_ptr_1g); };
            assert(old(lctx).lock_entry_contains(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.lock_id_by_index(cache_cpu), KernelObjId::AllocatorCache(PageSize::SZ1g, alloc_ptr_1g, cache_cpu))) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        }
        assert(self.allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches.spec_index(cache_cpu).view().wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        self.allc_1g_mp.wunlock_cache(alloc_ptr_1g, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ1g));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_1g_mp, self.allc_1g_mp)) by { allocator_cache_lock_op_preserves_invariant_fields(old(self).allc_1g_mp, self.allc_1g_mp, alloc_ptr_1g, cache_cpu); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_1g_lock_op_eof(*old(self), *self, alloc_ptr_1g);
        }
    }
}
}

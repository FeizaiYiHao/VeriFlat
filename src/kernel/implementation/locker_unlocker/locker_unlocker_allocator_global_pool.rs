#[cfg(verus_keep_ghost)]
use super::locker_unlocker_allocator_eof::allocator_4k_lock_op_eof;
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_allocator_global_pool_4k(&mut self, alloc_ptr_4k: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), ALLOCATOR_GLOBAL_POOL_4K_MAJOR),
            typed_lock_map_majors_lt(old(lctx).thread_lock_map(), THREAD_SCHEDULED_LOCK_MAJOR),
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
            *final(self) == (KernelK { allc_4k_mp: final(self).allc_4k_mp, ..*old(self) }),
            final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
            final(self).allc_4k_mp.perms_wf(),
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool, old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(PageSize::SZ4k, alloc_ptr_4k), TypedHeldLock { lock_id: final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).allc_4k_mp.perms_wf() && old(self).allc_4k_mp.spec_index(alloc_ptr_4k).inv()) by { allocator_perms_wf_map(old(self).allc_4k_mp); allocator_perms_wf_at(old(self).allc_4k_mp, alloc_ptr_4k); };
            assert(old(lctx).lock_id_acyclic(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id())) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            };
            assert(!self.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locked_by_thread(lctx.thread_id()) && wlock_requires(self.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool, &*lctx)) by {
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned); assert(!lctx.allocator_global_pool_4k_lock_map().dom().contains(alloc_ptr_4k));
            };
        }
        let ret = self.allc_4k_mp.wlock_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_4k_lock_op_eof(*old(self), *self, alloc_ptr_4k);
        }
        ret
    }

    pub fn wunlock_allocator_global_pool_4k(&mut self, alloc_ptr_4k: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write),
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
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
            final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
            wunlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(PageSize::SZ4k, alloc_ptr_4k), old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id()),
    {
        proof {
            assert({ &&& old(self).allc_4k_mp.perms_wf() &&& old(self).allc_4k_mp.spec_index(alloc_ptr_4k).inv() }) by { allocator_perms_wf_map(old(self).allc_4k_mp); allocator_perms_wf_at(old(self).allc_4k_mp, alloc_ptr_4k); };
            assert(old(lctx).lock_entry_contains(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(PageSize::SZ4k, alloc_ptr_4k))) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        }
        assert(self.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        self.allc_4k_mp.wunlock_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_4k_lock_op_eof(*old(self), *self, alloc_ptr_4k);
        }
    }
}
} // verus!

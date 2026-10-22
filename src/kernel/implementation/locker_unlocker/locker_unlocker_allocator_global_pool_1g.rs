#[cfg(verus_keep_ghost)]
use super::locker_unlocker_allocator_eof::allocator_1g_lock_op_eof;
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Write-hold the global pool of the 1G allocator `alloc_ptr_1g` while 4K and 2M global pools may be held; 1G global pools are ordered by their
    /// owning container (the pool minor).
    pub fn wlock_allocator_global_pool_1g_ordered(&mut self, alloc_ptr_1g: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_1g_mp.dom().contains(alloc_ptr_1g),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), ALLOCATOR_GLOBAL_POOL_1G_MAJOR),
            typed_lock_map_majors_lt(old(lctx).thread_lock_map(), THREAD_SCHEDULED_LOCK_MAJOR),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            forall|held: RwLockPageAllocatorPtr| #![trigger old(lctx).allocator_global_pool_1g_lock_map().dom().contains(held)] old(lctx).allocator_global_pool_1g_lock_map().dom().contains(held)
                ==> old(self).allc_1g_mp.spec_index(held).owning_container < old(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container,
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
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool, final(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool, old(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.lock_id(), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(PageSize::SZ1g, alloc_ptr_1g), TypedHeldLock { lock_id: final(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.lock_id(), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).allc_1g_mp.perms_wf() && old(self).allc_1g_mp.spec_index(alloc_ptr_1g).inv()) by { allocator_perms_wf_map(old(self).allc_1g_mp); allocator_perms_wf_at(old(self).allc_1g_mp, alloc_ptr_1g); };
            assert(old(lctx).lock_id_acyclic(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.lock_id())) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(allocator_perms_wf);
            };
            assert(!self.allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.locked_by_thread(lctx.thread_id()) && wlock_requires(self.allc_1g_mp.spec_index(alloc_ptr_1g).global_pool, &*lctx)) by {
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned); assert(!lctx.allocator_global_pool_1g_lock_map().dom().contains(alloc_ptr_1g));
            };
        }
        let ret = self.allc_1g_mp.wlock_global_pool(alloc_ptr_1g, Tracked(&mut *lctx), Ghost(PageSize::SZ1g));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_1g_mp, self.allc_1g_mp)) by { allocator_global_pool_lock_op_preserves_invariant_fields(old(self).allc_1g_mp, self.allc_1g_mp, alloc_ptr_1g); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_1g_lock_op_eof(*old(self), *self, alloc_ptr_1g);
        }
        ret
    }
}
} // verus!

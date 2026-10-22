#[cfg(verus_keep_ghost)]
use super::locker_unlocker_allocator_eof::{allocator_4k_lock_op_eof, allocator_2m_lock_op_eof, allocator_1g_lock_op_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Like `wlock_allocator_quota_4k`, but other 4K quotas may be held: same-size quotas are ordered by their owning container (the quota minor).
    pub fn wlock_allocator_quota_4k_ordered(&mut self, alloc_ptr_4k: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
            forall|held: RwLockPageAllocatorPtr| #![trigger old(lctx).allocator_quota_4k_lock_map().dom().contains(held)] old(lctx).allocator_quota_4k_lock_map().dom().contains(held)
                ==> old(self).allc_4k_mp.spec_index(held).owning_container < old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
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
            allocator_perms_wf_map(old(self).allc_4k_mp);
            allocator_perms_wf_at(old(self).allc_4k_mp, alloc_ptr_4k);
            assert(old(lctx).lock_id_acyclic(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id())) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(allocator_perms_wf);
            };
        }
        assert(!self.allc_4k_mp.spec_index(alloc_ptr_4k).quota.locked_by_thread(lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        let ret = self.allc_4k_mp.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_4k_lock_op_eof(*old(self), *self, alloc_ptr_4k);
        }
        ret
    }

    /// Like `wlock_allocator_quota_2m`, but other 2M quotas may be held: same-size quotas are ordered by their owning container (the quota minor).
    pub fn wlock_allocator_quota_2m_ordered(&mut self, alloc_ptr_2m: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
            forall|held: RwLockPageAllocatorPtr| #![trigger old(lctx).allocator_quota_2m_lock_map().dom().contains(held)] old(lctx).allocator_quota_2m_lock_map().dom().contains(held)
                ==> old(self).allc_2m_mp.spec_index(held).owning_container < old(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container,
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
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
            final(self).allc_2m_mp.perms_wf(),
            final(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf(),
            final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches,
            final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
            final(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container,
            final(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota, final(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota, old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota.lock_id(), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ2m, alloc_ptr_2m), TypedHeldLock { lock_id: final(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota.lock_id(), mode: TypedLockMode::Write }),
    {
        proof {
            allocator_perms_wf_map(old(self).allc_2m_mp);
            allocator_perms_wf_at(old(self).allc_2m_mp, alloc_ptr_2m);
            assert(old(lctx).lock_id_acyclic(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota.lock_id())) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(allocator_perms_wf);
            };
        }
        assert(!self.allc_2m_mp.spec_index(alloc_ptr_2m).quota.locked_by_thread(lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        let ret = self.allc_2m_mp.wlock_quota(alloc_ptr_2m, Tracked(&mut *lctx), Ghost(PageSize::SZ2m));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m); };
            assert(self.allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_2m_lock_op_eof(*old(self), *self, alloc_ptr_2m);
        }
        ret
    }

    /// Like `wlock_allocator_quota_1g`, but other 1G quotas may be held: same-size quotas are ordered by their owning container (the quota minor).
    pub fn wlock_allocator_quota_1g_ordered(&mut self, alloc_ptr_1g: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).allc_1g_mp.dom().contains(alloc_ptr_1g),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
            forall|held: RwLockPageAllocatorPtr| #![trigger old(lctx).allocator_quota_1g_lock_map().dom().contains(held)] old(lctx).allocator_quota_1g_lock_map().dom().contains(held)
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
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).owning_container,
            final(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages == old(self).allc_1g_mp.spec_index(alloc_ptr_1g).total_free_pages,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota, final(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota, old(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota.lock_id(), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ1g, alloc_ptr_1g), TypedHeldLock { lock_id: final(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota.lock_id(), mode: TypedLockMode::Write }),
    {
        proof {
            allocator_perms_wf_map(old(self).allc_1g_mp);
            allocator_perms_wf_at(old(self).allc_1g_mp, alloc_ptr_1g);
            assert(old(lctx).lock_id_acyclic(old(self).allc_1g_mp.spec_index(alloc_ptr_1g).quota.lock_id())) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(allocator_perms_wf);
            };
        }
        assert(!self.allc_1g_mp.spec_index(alloc_ptr_1g).quota.locked_by_thread(lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        let ret = self.allc_1g_mp.wlock_quota(alloc_ptr_1g, Tracked(&mut *lctx), Ghost(PageSize::SZ1g));
        proof {
            assert(allocator_invariant_fields_unchanged(old(self).allc_1g_mp, self.allc_1g_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_1g_mp, self.allc_1g_mp, alloc_ptr_1g); };
            assert(self.allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            allocator_1g_lock_op_eof(*old(self), *self, alloc_ptr_1g);
        }
        ret
    }
}
} // verus!

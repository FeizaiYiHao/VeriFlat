#[cfg(verus_keep_ghost)]
use super::locker_unlocker_iommu_eof::{iommu_root_table_lock_op_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_iommu_root_table(&mut self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { irt: final(self).irt, ..*old(self) }),
            wlock_ensures(old(self).irt, final(self).irt, old(self).irt.lock_id(), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::IommuRootTable(old(self).irt.view().table_base()), TypedHeldLock { lock_id: old(self).irt.lock_id(), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(lctx).lock_id_acyclic(old(self).irt.lock_id())) by {
                reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(wlock_requires(old(self).irt, old(lctx))) by { reveal(iommu_root_table_typed_lock_map_aligned); };
        }
        let ret = self.irt.wlock(Tracked(&mut *lctx), Ghost(self.irt.lock_id()), Ghost(KernelObjId::IommuRootTable(self.irt.view().table_base())));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            iommu_root_table_lock_op_eof(*old(self), *self);
        }
        ret
    }

    pub fn wunlock_iommu_root_table(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).irt.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).iommu_root_table_lock_map(), old(self).irt.view().table_base(), TypedLockMode::Write),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { irt: final(self).irt, ..*old(self) }),
            wunlock_ensures(old(self).irt, final(self).irt),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::IommuRootTable(old(self).irt.view().table_base()), old(self).irt.lock_id()),
    {
        proof { assert(old(self).irt.wlocked_by(old(lctx)) && old(lctx).lock_entry_contains(old(self).irt.lock_id(), KernelObjId::IommuRootTable(old(self).irt.view().table_base()))) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
        self.irt.wunlock(Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::IommuRootTable(self.irt.view().table_base())));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            iommu_root_table_lock_op_eof(*old(self), *self);
        }
    }
}
}

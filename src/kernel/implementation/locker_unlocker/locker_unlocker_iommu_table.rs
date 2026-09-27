use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wunlock_iommu_table(
        &mut self,
        iommu_table_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        lock_perm: Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            old(self).it_mp.dom().contains(iommu_table_ptr),
            typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { it_mp: final(self).it_mp, ..*old(self) }),
            final(self).it_mp.unchanged_except(&old(self).it_mp, iommu_table_ptr),
            final(self).it_mp.lock_id_by_key(iommu_table_ptr) == old(self).it_mp.lock_id_by_key(iommu_table_ptr),
            wunlock_ensures(old(self).it_mp.spec_index(iommu_table_ptr), final(self).it_mp.spec_index(iommu_table_ptr)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::IommuTable(iommu_table_ptr), old(self).it_mp.lock_id_by_key(iommu_table_ptr)),
    {
        proof {
            assert(old(self).it_mp.perms_wf() && old(self).it_mp.spec_index(iommu_table_ptr).inv()) by { reveal(iommu_table_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).it_mp.lock_id_by_key(iommu_table_ptr), KernelObjId::IommuTable(iommu_table_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.it_mp.spec_index(iommu_table_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        self.it_mp.wunlock(iommu_table_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::IommuTable(iommu_table_ptr)));
        proof {
            assert(iommu_table_perms_wf(self.it_mp)) by { reveal(iommu_table_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(iommu_table_pages_wf); reveal(process_iommu_table_match); };
            assert(iommu_root_table_process_wf(&self.irt, self.prc_mp, self.it_mp)) by { reveal(iommu_root_table_process_wf); };
            assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.irt, self.prc_mp, self.it_mp)) by { reveal(iommu_tlb_wf_spec); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
    }
}
} // verus!

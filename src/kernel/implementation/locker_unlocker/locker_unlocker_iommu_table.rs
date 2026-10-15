use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Write-locks one IOMMU table while its process is write-held and none of that process's functions is attached, so
    /// no device can observe the leaves exit hides before it releases the table.
    pub fn wlock_iommu_table(&mut self, iommu_table_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).it_mp.dom().contains(iommu_table_ptr),
            !old(lctx).iommu_table_lock_map().dom().contains(iommu_table_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < IOMMU_TABLE_LOCK_MAJOR,
            forall|held_iommu_table: RwLockPageTableRoot| #![trigger old(lctx).iommu_table_lock_map().dom().contains(held_iommu_table)] old(lctx).iommu_table_lock_map().dom().contains(held_iommu_table) ==> held_iommu_table < iommu_table_ptr,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(self).it_mp.spec_index(iommu_table_ptr).view().proc_ptr, TypedLockMode::Write),
            forall|bus: usize, device: usize, function: usize| #![trigger old(self).irt.view().spec_index_iommu_root(bus, device, function)]
                pci_bdf_valid(bus, device, function) && old(self).irt.view().spec_index_owner(bus, device, function) == old(self).it_mp.spec_index(iommu_table_ptr).view().proc_ptr
                    ==> old(self).irt.view().spec_index_iommu_root(bus, device, function) is None,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { it_mp: final(self).it_mp, ..*old(self) }),
            final(self).it_mp.unchanged_except(&old(self).it_mp, iommu_table_ptr),
            final(self).it_mp.lock_id_by_key(iommu_table_ptr) == old(self).it_mp.lock_id_by_key(iommu_table_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).it_mp.spec_index(iommu_table_ptr), final(self).it_mp.spec_index(iommu_table_ptr), old(self).it_mp.lock_id_by_key(iommu_table_ptr), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::IommuTable(iommu_table_ptr), TypedHeldLock { lock_id: final(self).it_mp.lock_id_by_key(iommu_table_ptr), mode: TypedLockMode::Write }),
    {
        proof {
            iommu_table_perms_wf_at(old(self).it_mp, iommu_table_ptr);
            assert(old(lctx).lock_id_acyclic(old(self).it_mp.lock_id_by_key(iommu_table_ptr))) by {
                reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(iommu_table_perms_wf);
            };
            assert(!old(self).it_mp.spec_index(iommu_table_ptr).locked_by_thread(old(lctx).thread_id())) by {
                if old(self).it_mp.spec_index(iommu_table_ptr).locked_by_thread(old(lctx).thread_id()) {
                    assert(old(lctx).iommu_table_lock_map().dom().contains(iommu_table_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                }
            };
        }
        let ret = self.it_mp.wlock(iommu_table_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::IommuTable(iommu_table_ptr)));
        proof {
            assert(self.it_mp.spec_index(iommu_table_ptr).view().leaves_present()) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
            assert(iommu_table_perms_wf(self.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(pagetable_pages_wf); reveal(process_iommu_table_match); reveal(page_iommu_table_wf); };
            assert(iommu_root_table_process_wf(self.irt.view(), self.prc_mp, self.it_mp)) by { reveal(iommu_root_table_process_wf); };
            assert(iommu_tlb_wf_spec(self.iommu_tlb, self.irt.view(), self.prc_mp, self.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
            assert(iommu_table_lock_wf(self.irt.view(), self.prc_mp, self.it_mp)) by {
                reveal(iommu_table_lock_wf); reveal(process_iommu_table_match);
                old(self).prc_mp.typed_lock_map_aligned_write_at(old(lctx).process_lock_map(), old(lctx).thread_id(), old(self).it_mp.spec_index(iommu_table_ptr).view().proc_ptr);
            };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
        ret
    }

    pub fn wunlock_iommu_table(&mut self, iommu_table_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).it_mp.dom().contains(iommu_table_ptr),
            old(self).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
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
            assert(old(self).it_mp.perms_wf() && old(self).it_mp.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_at(old(self).it_mp, iommu_table_ptr); };
            assert(old(lctx).lock_entry_contains(old(self).it_mp.lock_id_by_key(iommu_table_ptr), KernelObjId::IommuTable(iommu_table_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.it_mp.spec_index(iommu_table_ptr).wlocked_by(&*lctx)) by { old(self).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table_ptr); };
        self.it_mp.wunlock(iommu_table_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::IommuTable(iommu_table_ptr)));
        proof {
            assert(iommu_table_perms_wf(self.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { pagetable_pages_wf_preserved_for_page_state_eq(old(self).it_mp, self.it_mp, old(self).pg_arr, self.pg_arr); reveal(process_iommu_table_match); reveal(page_iommu_table_wf); };
            assert(iommu_root_table_process_wf(self.irt.view(), self.prc_mp, self.it_mp)) by { reveal(iommu_root_table_process_wf); };
            assert(iommu_tlb_wf_spec(self.iommu_tlb, self.irt.view(), self.prc_mp, self.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
            assert(iommu_table_lock_wf(self.irt.view(), self.prc_mp, self.it_mp)) by { reveal(iommu_table_lock_wf); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
    }
}
} // verus!

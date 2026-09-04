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
            old(self).it_mp.spec_index(iommu_table_ptr).wlocked_by(old(lctx)),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(self).pt_mp == old(self).pt_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).it_mp.unchanged_except(&old(self).it_mp, iommu_table_ptr),
            final(self).it_mp.lock_id_by_key(iommu_table_ptr) == old(self).it_mp.lock_id_by_key(iommu_table_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            wunlock_ensures(old(self).it_mp.spec_index(iommu_table_ptr), final(self).it_mp.spec_index(iommu_table_ptr)),
            iommu_table_objects_unlocked_except(old(self).it_mp, old(lctx).thread_id(), set![iommu_table_ptr]) ==> iommu_table_objects_unlocked(final(self).it_mp, final(lctx).thread_id()),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).it_mp.lock_id_by_key(iommu_table_ptr), KernelObjId::IommuTable(iommu_table_ptr))),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::IommuTable(iommu_table_ptr)),
            forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)]
                old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)
                ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables.remove(iommu_table_ptr)),
    {
        proof {
            assert(old(self).it_mp.perms_wf() && old(self).it_mp.spec_index(iommu_table_ptr).inv()) by { reveal(iommu_table_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).it_mp.lock_id_by_key(iommu_table_ptr), KernelObjId::IommuTable(iommu_table_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(old(lctx).lock_id_set().contains((old(self).it_mp.lock_id_by_key(iommu_table_ptr), KernelObjId::IommuTable(iommu_table_ptr)))) by { reveal(lock_id_set_aligned); };
        }
        self.it_mp.wunlock(iommu_table_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::IommuTable(iommu_table_ptr)));
        proof {
            assert(iommu_table_perms_wf(self.it_mp)) by { reveal(iommu_table_perms_wf);  };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(iommu_table_pages_wf); reveal(process_iommu_table_match);   };
            assert(iommu_root_table_process_wf(&self.irt, self.prc_mp, self.it_mp)) by { reveal(iommu_root_table_process_wf);   };
            assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.irt, self.prc_mp, self.it_mp)) by { reveal(iommu_tlb_wf_spec);   };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            broadcast use vstd::map::lemma_map_remove_domain;
            broadcast use vstd::set::lemma_set_remove_same;
            broadcast use vstd::set::lemma_set_remove_different;
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
    }
}
} // verus!

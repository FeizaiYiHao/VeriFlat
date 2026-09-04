use vstd::prelude::*;
verus! {

use crate::*;

impl KernelK {
    pub fn retype_page_to_pagetable_and_insert(
        &mut self,
        page_ptr: PagePtr,
        pagetable_value: PageTable<PT_TYPE>,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).pt_mp.perms_wf(),
            !old(self).pt_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            pagetable_value.inv(),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).pt_mp.perms_wf(),
            final(self).pt_mp.dom() =~= old(self).pt_mp.dom().insert(page_ptr),
            forall|ptr: RwLockPageTableRoot| #![auto]
                old(self).pt_mp.dom().contains(ptr) ==> final(self).pt_mp.spec_index(ptr) == old(self).pt_mp.spec_index(ptr),
            forall|ptr: RwLockPageTableRoot|
                #![trigger old(self).pt_mp.lock_id_by_key(ptr)]
                #![trigger final(self).pt_mp.lock_id_by_key(ptr)]
                old(self).pt_mp.dom().contains(ptr) ==> final(self).pt_mp.lock_id_by_key(ptr) == old(self).pt_mp.lock_id_by_key(ptr),
            final(self).pt_mp.spec_index(page_ptr).is_init(),
            final(self).pt_mp.spec_index(page_ptr).view() == pagetable_value,
            !final(self).pt_mp.spec_index(page_ptr).being_killed(),
            final(self).pt_mp.spec_index(page_ptr).wlocked_by(final(lctx)),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).pt_mp.lock_id_by_key(page_ptr),
            final(self).pt_mp.lock_id_by_key(page_ptr) == (LockId {
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: pagetable_value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).pt_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pt_mp.lock_id_by_key(page_ptr), KernelObjId::PageTable(page_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(page_ptr), TypedHeldLock {
                lock_id: final(self).pt_mp.lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
    {
        proof { assert(!old(lctx).pagetable_lock_map().dom().contains(page_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        let (Tracked(pagetable_rwlock_perm), Tracked(pagetable_perm)) = retype_page_perm_to_rwlock::<PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>(
            page_ptr, pagetable_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::PageTable(page_ptr)),
        );
        self.pt_mp.insert_with_perm(page_ptr, Tracked(pagetable_rwlock_perm));
        proof { assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        Tracked(pagetable_perm)
    }

    pub fn retype_page_to_iommu_table_and_insert(
        &mut self,
        page_ptr: PagePtr,
        iommu_table_value: PageTable<IOMMU_TYPE>,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).it_mp.perms_wf(),
            !old(self).it_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            iommu_table_value.inv(),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).pt_mp == old(self).pt_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).it_mp.perms_wf(),
            final(self).it_mp.dom() =~= old(self).it_mp.dom().insert(page_ptr),
            forall|ptr: RwLockPageTableRoot| #![auto]
                old(self).it_mp.dom().contains(ptr) ==> final(self).it_mp.spec_index(ptr) == old(self).it_mp.spec_index(ptr),
            forall|ptr: RwLockPageTableRoot|
                #![trigger old(self).it_mp.lock_id_by_key(ptr)]
                #![trigger final(self).it_mp.lock_id_by_key(ptr)]
                old(self).it_mp.dom().contains(ptr) ==> final(self).it_mp.lock_id_by_key(ptr) == old(self).it_mp.lock_id_by_key(ptr),
            final(self).it_mp.spec_index(page_ptr).is_init(),
            final(self).it_mp.spec_index(page_ptr).view() == iommu_table_value,
            !final(self).it_mp.spec_index(page_ptr).being_killed(),
            final(self).it_mp.spec_index(page_ptr).wlocked_by(final(lctx)),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).it_mp.lock_id_by_key(page_ptr),
            final(self).it_mp.lock_id_by_key(page_ptr) == (LockId {
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: iommu_table_value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).it_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).it_mp.lock_id_by_key(page_ptr), KernelObjId::IommuTable(page_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::IommuTable(page_ptr), TypedHeldLock {
                lock_id: final(self).it_mp.lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
    {
        proof { assert(!old(lctx).iommu_table_lock_map().dom().contains(page_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        let (Tracked(iommu_table_rwlock_perm), Tracked(iommu_table_perm)) = retype_page_perm_to_rwlock::<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>(
            page_ptr, iommu_table_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::IommuTable(page_ptr)),
        );
        self.it_mp.insert_with_perm(page_ptr, Tracked(iommu_table_rwlock_perm));
        proof { assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        Tracked(iommu_table_perm)
    }
}
} // verus!

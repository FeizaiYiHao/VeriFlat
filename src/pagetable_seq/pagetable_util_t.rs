use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

/// TCB: retire a write-locked page table whose only table page is its root table, and reclaim the page that held the
/// object and the root table's page as raw memory.
///
/// This is the inverse of `retype_page_to_pagetable_and_insert` plus the root table it owned. The object has already
/// left `pagetable_map`, the caller exclusively write-holds its lock in the release phase, and its root table is its
/// only table page, so the object owns no other memory and no other thread can reach or wait on the lock. The held
/// lock disappears from `lctx` with the object.
#[verifier::external_body]
pub fn retype_pagetable_rwlock_to_4k_page_perms(
    pagetable_ptr: RwLockPageTableRoot, Tracked(pagetable_perm): Tracked<PointsTo<RwLock<PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>>, Tracked(lock_perm): Tracked<LockPerm>,
    Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: (Tracked<PagePerm4k>, Tracked<PagePerm4k>))
    requires
        pagetable_perm.is_init(),
        pagetable_perm.addr() == pagetable_ptr,
        pagetable_perm.value().is_init(),
        pagetable_perm.value().view().wf(),
        pagetable_perm.value().view().page_closure() =~= set![pagetable_perm.value().view().cr3],
        pagetable_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr)),
        ret.0.view().is_init(),
        ret.0.view().addr() == pagetable_ptr,
        ret.1.view().is_init(),
        ret.1.view().addr() == pagetable_perm.value().view().cr3,
{
    (Tracked::assume_new(), Tracked::assume_new())
}

/// TCB: retire a write-locked IOMMU table whose only table page is its root table, and reclaim the page that held the
/// object and the root table's page as raw memory.
///
/// This is the inverse of `retype_page_to_iommu_table_and_insert` plus the root table it owned, under the same
/// conditions as `retype_pagetable_rwlock_to_4k_page_perms`.
#[verifier::external_body]
pub fn retype_iommu_table_rwlock_to_4k_page_perms(
    iommu_table_ptr: RwLockPageTableRoot, Tracked(iommu_table_perm): Tracked<PointsTo<RwLock<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: (Tracked<PagePerm4k>, Tracked<PagePerm4k>))
    requires
        iommu_table_perm.is_init(),
        iommu_table_perm.addr() == iommu_table_ptr,
        iommu_table_perm.value().is_init(),
        iommu_table_perm.value().view().wf(),
        iommu_table_perm.value().view().page_closure() =~= set![iommu_table_perm.value().view().cr3],
        iommu_table_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::IommuTable(iommu_table_ptr)),
        ret.0.view().is_init(),
        ret.0.view().addr() == iommu_table_ptr,
        ret.1.view().is_init(),
        ret.1.view().addr() == iommu_table_perm.value().view().cr3,
{
    (Tracked::assume_new(), Tracked::assume_new())
}

impl KernelK {
    pub fn retype_page_to_pagetable_and_insert(&mut self, page_ptr: PagePtr, pagetable_value: PageTable<PT_TYPE>, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).pt_mp.perms_wf(),
            !old(self).pt_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            pagetable_value.inv(),
            old(self).pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).pcid_needflush == old(self).pcid_needflush,
            final(self).cpu_published == old(self).cpu_published,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).cpu_set_mp == old(self).cpu_set_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_offline_mp == old(self).cpu_offline_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).pt_mp.perms_wf(),
            pagetable_perms_wf(old(self).pt_mp) ==> pagetable_perms_wf(final(self).pt_mp),
            page_pagetable_wf(old(self).pt_mp, old(self).pg_arr) && pagetable_value.is_empty() ==> page_pagetable_wf(final(self).pt_mp, final(self).pg_arr),
            final(self).pt_mp.dom() =~= old(self).pt_mp.dom().insert(page_ptr),
            forall|ptr: RwLockPageTableRoot|
                #![trigger final(self).pt_mp.spec_index(ptr)]
                #![trigger old(self).pt_mp.spec_index(ptr)]
                #![trigger old(self).pt_mp.dom().contains(ptr)]
                #![trigger final(self).pt_mp.dom().contains(ptr)]
                old(self).pt_mp.dom().contains(ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(ptr)
                    &&& final(self).pt_mp.spec_index(ptr) == old(self).pt_mp.spec_index(ptr)
                },
            forall|ptr: RwLockPageTableRoot|
                #![trigger old(self).pt_mp.lock_id_by_key(ptr)]
                #![trigger final(self).pt_mp.lock_id_by_key(ptr)]
                old(self).pt_mp.dom().contains(ptr) ==> final(self).pt_mp.lock_id_by_key(ptr) == old(self).pt_mp.lock_id_by_key(ptr),
            final(self).pt_mp.spec_index(page_ptr).is_init(),
            final(self).pt_mp.spec_index(page_ptr).view() == pagetable_value,
            !final(self).pt_mp.spec_index(page_ptr).being_killed(),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), page_ptr, TypedLockMode::Write),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).pt_mp.lock_id_by_key(page_ptr),
            final(self).pt_mp.lock_id_by_key(page_ptr) == (LockId { container: pagetable_value.container_depth(), process: pagetable_value.process_depth(), major: pagetable_value.current_lock_major(), minor: page_ptr }),
            final(self).pt_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(page_ptr), TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
            final(self).pt_mp.typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
    {
        let (Tracked(pagetable_rwlock_perm), Tracked(pagetable_perm)) = retype_page_perm_to_rwlock::<PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>(page_ptr, pagetable_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::PageTable(page_ptr)));
        self.pt_mp.insert_with_perm(page_ptr, Tracked(pagetable_rwlock_perm));
        proof {
            assert(pagetable_perms_wf(old(self).pt_mp) ==> pagetable_perms_wf(self.pt_mp)) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
            assert(page_pagetable_wf(old(self).pt_mp, old(self).pg_arr) && pagetable_value.is_empty() ==> page_pagetable_wf(self.pt_mp, self.pg_arr)) by {
                reveal(mapped_4k_page_pagetable_wf);
                reveal(mapped_2m_page_pagetable_wf);
                reveal(mapped_1g_page_pagetable_wf);
            };
            assert(self.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        Tracked(pagetable_perm)
    }

    pub fn retype_page_to_iommu_table_and_insert(&mut self, page_ptr: PagePtr, iommu_table_value: PageTable<IOMMU_TYPE>, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).it_mp.perms_wf(),
            !old(self).it_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            iommu_table_value.inv(),
            old(self).it_mp.typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).pt_mp == old(self).pt_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).pcid_needflush == old(self).pcid_needflush,
            final(self).cpu_published == old(self).cpu_published,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).cpu_set_mp == old(self).cpu_set_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_offline_mp == old(self).cpu_offline_mp,
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
            typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), page_ptr, TypedLockMode::Write),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).it_mp.lock_id_by_key(page_ptr),
            final(self).it_mp.lock_id_by_key(page_ptr) == (LockId { container: iommu_table_value.container_depth(), process: iommu_table_value.process_depth(), major: iommu_table_value.current_lock_major(), minor: page_ptr }),
            final(self).it_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::IommuTable(page_ptr), TypedHeldLock { lock_id: final(self).it_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
            final(self).it_mp.typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
    {
        let (Tracked(iommu_table_rwlock_perm), Tracked(iommu_table_perm)) = retype_page_perm_to_rwlock::<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>(page_ptr, iommu_table_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::IommuTable(page_ptr)));
        self.it_mp.insert_with_perm(page_ptr, Tracked(iommu_table_rwlock_perm));
        proof { assert(self.it_mp.typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        Tracked(iommu_table_perm)
    }

    /// Remove the write-held page table `pagetable_ptr`, whose only table page is its root table, and reclaim the
    /// page that held it and its root table's page.
    pub fn remove_pagetable_and_reclaim_4k_page_perms(&mut self, pagetable_ptr: RwLockPageTableRoot, Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: (Tracked<PagePerm4k>, Tracked<PagePerm4k>))
        requires
            old(self).pt_mp.perms_wf(),
            old(self).pt_mp.dom().contains(pagetable_ptr),
            old(self).pt_mp.spec_index(pagetable_ptr).is_init(),
            old(self).pt_mp.spec_index(pagetable_ptr).view().wf(),
            old(self).pt_mp.spec_index(pagetable_ptr).view().page_closure() =~= set![old(self).pt_mp.spec_index(pagetable_ptr).view().cr3],
            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == old(lctx).thread_id(),
            lock_perm.lock_id() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr)),
            *final(self) == (KernelK { pt_mp: final(self).pt_mp, ..*old(self) }),
            final(self).pt_mp.perms_wf(),
            pagetable_perms_wf(old(self).pt_mp) ==> pagetable_perms_wf(final(self).pt_mp),
            final(self).pt_mp.dom() =~= old(self).pt_mp.dom().remove(pagetable_ptr),
            forall|p: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(p)] final(self).pt_mp.dom().contains(p) ==> final(self).pt_mp.spec_index(p) == old(self).pt_mp.spec_index(p),
            forall|p: RwLockPageTableRoot| #![trigger final(self).pt_mp.lock_id_by_key(p)] final(self).pt_mp.dom().contains(p) ==> final(self).pt_mp.lock_id_by_key(p) == old(self).pt_mp.lock_id_by_key(p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.0.view().is_init(),
            ret.0.view().addr() == pagetable_ptr,
            ret.1.view().is_init(),
            ret.1.view().addr() == old(self).pt_mp.spec_index(pagetable_ptr).view().cr3,
    {
        proof { self.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
        let Tracked(pagetable_perm) = self.pt_mp.remove_with_perm(pagetable_ptr);
        let ret = retype_pagetable_rwlock_to_4k_page_perms(pagetable_ptr, Tracked(pagetable_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof {
            assert(pagetable_perms_wf(old(self).pt_mp) ==> pagetable_perms_wf(self.pt_mp)) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        ret
    }

    /// Remove the write-held IOMMU table `iommu_table_ptr`, whose only table page is its root table, and reclaim the
    /// page that held it and its root table's page.
    pub fn remove_iommu_table_and_reclaim_4k_page_perms(&mut self, iommu_table_ptr: RwLockPageTableRoot, Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: (Tracked<PagePerm4k>, Tracked<PagePerm4k>))
        requires
            old(self).it_mp.perms_wf(),
            old(self).it_mp.dom().contains(iommu_table_ptr),
            old(self).it_mp.spec_index(iommu_table_ptr).is_init(),
            old(self).it_mp.spec_index(iommu_table_ptr).view().wf(),
            old(self).it_mp.spec_index(iommu_table_ptr).view().page_closure() =~= set![old(self).it_mp.spec_index(iommu_table_ptr).view().cr3],
            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == old(lctx).thread_id(),
            lock_perm.lock_id() == old(self).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::IommuTable(iommu_table_ptr)),
            *final(self) == (KernelK { it_mp: final(self).it_mp, ..*old(self) }),
            final(self).it_mp.perms_wf(),
            iommu_table_perms_wf(old(self).it_mp) ==> iommu_table_perms_wf(final(self).it_mp),
            final(self).it_mp.dom() =~= old(self).it_mp.dom().remove(iommu_table_ptr),
            forall|p: RwLockPageTableRoot| #![trigger final(self).it_mp.spec_index(p)] final(self).it_mp.dom().contains(p) ==> final(self).it_mp.spec_index(p) == old(self).it_mp.spec_index(p),
            forall|p: RwLockPageTableRoot| #![trigger final(self).it_mp.lock_id_by_key(p)] final(self).it_mp.dom().contains(p) ==> final(self).it_mp.lock_id_by_key(p) == old(self).it_mp.lock_id_by_key(p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.0.view().is_init(),
            ret.0.view().addr() == iommu_table_ptr,
            ret.1.view().is_init(),
            ret.1.view().addr() == old(self).it_mp.spec_index(iommu_table_ptr).view().cr3,
    {
        proof { self.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_ptr); }
        let Tracked(iommu_table_perm) = self.it_mp.remove_with_perm(iommu_table_ptr);
        let ret = retype_iommu_table_rwlock_to_4k_page_perms(iommu_table_ptr, Tracked(iommu_table_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof {
            assert(iommu_table_perms_wf(old(self).it_mp) ==> iommu_table_perms_wf(self.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        ret
    }
}
} // verus!

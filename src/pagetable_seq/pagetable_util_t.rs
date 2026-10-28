use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
pub use super::pagetable_window_stale_eof::*;

/// TCB: retire a write-locked page table whose only table page is its root table, and reclaim the page that held the
/// object and the root table's page as raw memory.
///
/// This is the inverse of `retype_page_to_pagetable_c_and_insert` plus the root table it owned. The object has already
/// left `pagetable_map`, the caller exclusively write-holds its lock in the release phase, and its big-lock half owns
/// only its root table; its window half owns no L2 or L1 page and has been dropped from `pt_lower`. So the object owns
/// no other memory and no other thread can reach or wait on the lock. The held lock disappears from `lctx` with the
/// object.
#[verifier::external_body]
pub fn retype_pagetable_rwlock_to_4k_page_perms(
    pagetable_ptr: RwLockPageTableRoot, Tracked(pagetable_perm): Tracked<PointsTo<RwLock<PageTableHigher<PT_TYPE>, (), PageTableLower<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: (Tracked<PagePerm4k>, Tracked<PagePerm4k>))
    requires
        pagetable_perm.is_init(),
        pagetable_perm.addr() == pagetable_ptr,
        pagetable_perm.value().is_init(),
        pagetable_perm.value().view().inv(),
        pagetable_perm.value().view().l3_tables.view().dom() + pagetable_perm.value().view().l4_table.view().dom() =~= set![pagetable_perm.value().view().cr3],
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
    /// Publish a fresh, empty page table: retype `page_ptr` into the write-held big lock around `higher`, insert it into
    /// `pt_mp`, and file its window half `lower` under the same root in `pt_lower`.
    pub fn retype_page_to_pagetable_and_insert(&mut self, page_ptr: PagePtr, higher: PageTableHigher<PT_TYPE>, Tracked(lower): Tracked<PageTableLower<PT_TYPE>>,
        Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).pt_mp.perms_wf(),
            !old(self).pt_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            (PageTableC { higher, lower }).wf(),
            (PageTableC { higher, lower }).is_empty(),
            old(self).pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            *final(self) == (KernelK { pt_mp: final(self).pt_mp, pt_lower: final(self).pt_lower, ..*old(self) }),
            final(self).pt_mp.perms_wf(),
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
            final(self).pt_lower.view() == old(self).pt_lower.view().insert(page_ptr, lower),
            final(self).pt_mp.spec_index(page_ptr).is_init(),
            final(self).pt_mp.spec_index(page_ptr).view() == higher,
            final(self).pt_mp.spec_index(page_ptr).view_ghost() == lower,
            forall|r: RwLockPageTableRoot|
                #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), r)]
                old(self).pt_mp.dom().contains(r) ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), r) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), r),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), page_ptr) == (PageTableC { higher, lower }),
            !final(self).pt_mp.spec_index(page_ptr).being_killed(),
            pagetable_perms_wf(old(self).pt_mp) ==> pagetable_perms_wf(final(self).pt_mp),
            pagetable_lower_wf(old(self).pt_mp, old(self).pt_lower.view()) ==> pagetable_lower_wf(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_window_holders_hold_pagetable(old(self).pt_mp, old(self).pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_hidden_leaves_only_when_locked(old(self).pt_mp, old(self).pt_lower.view())
                ==> pagetable_hidden_leaves_only_when_locked(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_window_stale_cpus_only_when_locked(old(self).pt_mp, old(self).pt_lower.view())
                ==> pagetable_window_stale_cpus_only_when_locked(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_lower_backup_wf(old(self).pt_mp, old(self).pt_lower.view()) ==> pagetable_lower_backup_wf(final(self).pt_mp, final(self).pt_lower.view()),
            page_pagetable_wf(old(self).pt_mp, old(self).pt_lower.view(), old(self).pg_arr) ==> page_pagetable_wf(final(self).pt_mp, final(self).pt_lower.view(), final(self).pg_arr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), page_ptr, TypedLockMode::Write),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).pt_mp.lock_id_by_key(page_ptr),
            final(self).pt_mp.lock_id_by_key(page_ptr) == (LockId { container: LockOwnerId::None, process: LockOwnerId::None, major: PAGE_TABLE_LOCK_MAJOR, minor: seq![page_ptr] }),
            final(self).pt_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(page_ptr), TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
            final(self).pt_mp.typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
            pagetable_window_typed_lock_map_aligned(old(self).pt_mp, old(self).pt_lower.view(), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                ==> pagetable_window_typed_lock_map_aligned(final(self).pt_mp, final(self).pt_lower.view(), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
    {
        let ret = retype_page_to_pagetable_c_and_insert(&mut self.pt_mp, Tracked(self.pt_lower.borrow_mut()), page_ptr, higher, Tracked(lower), Tracked(page_perm), Tracked(&mut *lctx));
        proof { retype_page_to_pagetable_and_insert_eof(*old(self), *self, *old(lctx), *lctx, page_ptr, higher, lower, ret.view()); }
        ret
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
            final(self).pt_lower == old(self).pt_lower,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).pcid_needflush == old(self).pcid_needflush,
            final(self).cpu_hw_cr3_pcid == old(self).cpu_hw_cr3_pcid,
            final(self).cpu_op == old(self).cpu_op,
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
            final(self).it_mp.lock_id_by_key(page_ptr) == (LockId { container: iommu_table_value.container_depth(), process: iommu_table_value.process_depth(), major: iommu_table_value.current_lock_major(), minor: seq![page_ptr] }),
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

    /// Remove the write-held page table `pagetable_ptr` and reclaim the page that held it and its root table's page.
    /// Its root table is its only table page: its L3, L2, and L1 pages, and so its whole window half, are already gone.
    pub fn remove_pagetable_and_reclaim_4k_page_perms(&mut self, pagetable_ptr: RwLockPageTableRoot, Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: (Tracked<PagePerm4k>, Tracked<PagePerm4k>))
        requires
            old(self).pt_mp.perms_wf(),
            old(self).pt_mp.dom().contains(pagetable_ptr),
            old(self).pt_mp.spec_index(pagetable_ptr).is_init(),
            old(self).pt_lower.view().dom().contains(pagetable_ptr),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr).page_closure() =~= set![old(self).pt_mp.spec_index(pagetable_ptr).view().cr3],
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
            *final(self) == (KernelK { pt_mp: final(self).pt_mp, pt_lower: final(self).pt_lower, ..*old(self) }),
            final(self).pt_mp.perms_wf(),
            final(self).pt_mp.dom() =~= old(self).pt_mp.dom().remove(pagetable_ptr),
            forall|p: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(p)] final(self).pt_mp.dom().contains(p) ==> final(self).pt_mp.spec_index(p) == old(self).pt_mp.spec_index(p),
            forall|p: RwLockPageTableRoot| #![trigger final(self).pt_mp.lock_id_by_key(p)] final(self).pt_mp.dom().contains(p) ==> final(self).pt_mp.lock_id_by_key(p) == old(self).pt_mp.lock_id_by_key(p),
            final(self).pt_lower.view() == old(self).pt_lower.view().remove(pagetable_ptr),
            pagetable_perms_wf(old(self).pt_mp) ==> pagetable_perms_wf(final(self).pt_mp),
            pagetable_lower_wf(old(self).pt_mp, old(self).pt_lower.view()) ==> pagetable_lower_wf(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_window_holders_hold_pagetable(old(self).pt_mp, old(self).pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_hidden_leaves_only_when_locked(old(self).pt_mp, old(self).pt_lower.view())
                ==> pagetable_hidden_leaves_only_when_locked(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_window_stale_cpus_only_when_locked(old(self).pt_mp, old(self).pt_lower.view())
                ==> pagetable_window_stale_cpus_only_when_locked(final(self).pt_mp, final(self).pt_lower.view()),
            pagetable_lower_backup_wf(old(self).pt_mp, old(self).pt_lower.view()) ==> pagetable_lower_backup_wf(final(self).pt_mp, final(self).pt_lower.view()),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.0.view().is_init(),
            ret.0.view().addr() == pagetable_ptr,
            ret.1.view().is_init(),
            ret.1.view().addr() == old(self).pt_mp.spec_index(pagetable_ptr).view().cr3,
    {
        proof {
            self.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
            let c = pagetable_c(self.pt_mp, self.pt_lower.view(), pagetable_ptr);
            assert(c.higher.l3_tables.view().dom() + c.higher.l4_table.view().dom() =~= set![c.cr3()]) by { c.higher.wf_l4_cr3_at(); };
        }
        let Tracked(pagetable_perm) = self.pt_mp.remove_with_perm(pagetable_ptr);
        proof { let tracked _lower = self.pt_lower.borrow_mut().tracked_remove(pagetable_ptr); }
        let ret = retype_pagetable_rwlock_to_4k_page_perms(pagetable_ptr, Tracked(pagetable_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof { remove_pagetable_and_reclaim_4k_page_perms_eof(*old(self), *self, *old(lctx), *lctx, pagetable_ptr); }
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

    /// Apply `update` to the stale-CPU map of page table `root`. A `Set` names a window this thread holds unless it
    /// write-holds the table; `RemoveCpu` and `ClearEmpty` touch only the records this thread may change. The TLB
    /// invariant holds for the new map. A write-held table's ghost slot follows the window half.
    pub fn replace_window_stale_cpus(&mut self, root: RwLockPageTableRoot, Ghost(update): Ghost<WindowStaleUpdate>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            typed_lock_maps_aligned(old(self), lctx),
            update is Set ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write) || lctx.pagetable_window_lock_map().dom().contains((root, update->Set_window)),
            update is Set ==> (pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_view(update->Set_window).stale_cpus is Some
                ==> pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_view(update->Set_window).stale_cpus->Some_0.subset_of(update->Set_cpus))
                || tlb_wf_spec(old(self).cpu_tlb, old(self).pt_mp, old(self).pt_lower.view().insert(root, PageTableLower {
                window_stale_cpus: window_stale_cpus_after(update, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root), typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write), lctx.thread_id()),
                ..pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower }), old(self).cpu_arr, old(self).pcid_needflush),
            update is RemoveCpu ==> ({
                let cpu_id = update->RemoveCpu_cpu_id;
                let pcid = old(self).pt_mp.spec_index(root).view().pcid->Some_0;
                &&& old(self).pt_mp.spec_index(root).view().pcid is Some
                &&& index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                &&& old(self).cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
                    || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
                    || (old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != root)
                || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root))
            }) || tlb_wf_spec(old(self).cpu_tlb, old(self).pt_mp, old(self).pt_lower.view().insert(root, PageTableLower {
                window_stale_cpus: window_stale_cpus_after(update, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root), typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write), lctx.thread_id()),
                ..pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower }), old(self).cpu_arr, old(self).pcid_needflush),
        ensures
            final(self).inv(),
            typed_lock_maps_aligned(final(self), lctx),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            *final(self) == (KernelK { pt_mp: final(self).pt_mp, pt_lower: final(self).pt_lower, ..*old(self) }),
            final(self).pt_mp.unchanged_except(&old(self).pt_mp, root),
            forall|k: RwLockPageTableRoot| #![trigger final(self).pt_mp.lock_id_by_key(k)] old(self).pt_mp.dom().contains(k) ==> final(self).pt_mp.lock_id_by_key(k) == old(self).pt_mp.lock_id_by_key(k),
            update_ghost_ensures(old(self).pt_mp.spec_index(root), final(self).pt_mp.spec_index(root),
                if old(self).pt_mp.spec_index(root).wlocked() { final(self).pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
            final(self).pt_lower.view() =~= old(self).pt_lower.view().insert(root, PageTableLower {
                window_stale_cpus: window_stale_cpus_after(update, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root), typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write), lctx.thread_id()),
                ..pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower }),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
            forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((root, w))] lctx.pagetable_window_lock_map().dom().contains((root, w)) ==> {
                let before = pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root);
                let l2_page = before.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va));
                &&& before.lower.l2_lock.dom().contains(l2_page)
                &&& pei_valid(spec_v2l2index(w.va))
                &&& before.lower.l2_lock_of(l2_page).locked_by_thread(spec_v2l2index(w.va), lctx.thread_id())
            },
    {
        proof { window_stale_cpus_update_eof_held_windows(*old(self), root, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id()); }
        proof {
            pagetable_perms_wf_map(old(self).pt_mp);
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            let ghost new_map = window_stale_cpus_after(update, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root), typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write), lctx.thread_id());
            let tracked mut lower = self.pt_lower.borrow_mut().tracked_remove(root);
            lower.window_stale_cpus = new_map;
            self.pt_lower.borrow_mut().tracked_insert(root, lower);
            if old(self).pt_mp.spec_index(root).wlocked() { self.pt_mp.update_ghost(root, self.pt_lower.view().spec_index(root)); }
            assert(self.pt_lower.view() =~= old(self).pt_lower.view().insert(root, PageTableLower { window_stale_cpus: new_map, ..pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower }));
            assert(pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g());
            assert(pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).leaves_present() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).leaves_present());
            assert(window_stale_cpus_update_eof_transition_framing(*old(self), *self, root)) by { reveal(window_stale_cpus_update_eof_transition_framing); };
            assert(typed_lock_maps_aligned(self, lctx)) by {
                reveal(window_stale_cpus_update_eof_transition_framing); reveal(pagetable_window_typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write) {
                old(self).pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), root);
            }
            window_stale_cpus_update_eof(*old(self), *self, root, update, typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write), lctx.thread_id());
        }
    }
}

/// EOF closure of `KernelK::retype_page_to_pagetable_and_insert`: the new table is empty and write-held by this thread,
/// so it has no window, and the page-table invariants and the window alignment carry over.
proof fn retype_page_to_pagetable_and_insert_eof(
    old_k: KernelK, new_k: KernelK, old_lctx: LocalContext, new_lctx: LocalContext, page_ptr: PagePtr, higher: PageTableHigher<PT_TYPE>,
    lower: PageTableLower<PT_TYPE>, lock_perm: LockPerm,
)
    requires
        !old_k.pt_mp.dom().contains(page_ptr),
        (PageTableC { higher, lower }).wf(),
        (PageTableC { higher, lower }).is_empty(),
        new_k == (KernelK { pt_mp: new_k.pt_mp, pt_lower: new_k.pt_lower, ..old_k }),
        new_k.pt_mp.dom() =~= old_k.pt_mp.dom().insert(page_ptr),
        forall|ptr: RwLockPageTableRoot|
            #![trigger new_k.pt_mp.spec_index(ptr)]
            #![trigger old_k.pt_mp.spec_index(ptr)]
            old_k.pt_mp.dom().contains(ptr) ==> new_k.pt_mp.spec_index(ptr) == old_k.pt_mp.spec_index(ptr),
        new_k.pt_mp.spec_index(page_ptr).is_init(),
        new_k.pt_mp.spec_index(page_ptr).view() == higher,
        new_k.pt_mp.spec_index(page_ptr).view_ghost() == lower,
        new_k.pt_mp.spec_index(page_ptr).write_lock_perm_match(&lock_perm),
        lock_perm.thread_id() == new_lctx.thread_id(),
        new_k.pt_lower.view() == old_k.pt_lower.view().insert(page_ptr, lower),
        forall|r: RwLockPageTableRoot|
            #![trigger pagetable_c(new_k.pt_mp, new_k.pt_lower.view(), r)]
            old_k.pt_mp.dom().contains(r) ==> pagetable_c(new_k.pt_mp, new_k.pt_lower.view(), r) == pagetable_c(old_k.pt_mp, old_k.pt_lower.view(), r),
        new_lctx.thread_id() == old_lctx.thread_id(),
        typed_lock_maps_inserted(&old_lctx, &new_lctx, KernelObjId::PageTable(page_ptr), TypedHeldLock { lock_id: new_k.pt_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
    ensures
        pagetable_c(new_k.pt_mp, new_k.pt_lower.view(), page_ptr) == (PageTableC { higher, lower }),
        pagetable_perms_wf(old_k.pt_mp) && new_k.pt_mp.perms_wf() ==> pagetable_perms_wf(new_k.pt_mp),
        pagetable_lower_wf(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_lower_wf(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_hidden_leaves_only_when_locked(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_stale_cpus_only_when_locked(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_lower_backup_wf(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_lower_backup_wf(new_k.pt_mp, new_k.pt_lower.view()),
        page_pagetable_wf(old_k.pt_mp, old_k.pt_lower.view(), old_k.pg_arr) ==> page_pagetable_wf(new_k.pt_mp, new_k.pt_lower.view(), new_k.pg_arr),
        pagetable_window_typed_lock_map_aligned(old_k.pt_mp, old_k.pt_lower.view(), old_lctx.pagetable_window_lock_map(), old_lctx.pagetable_lock_map(), old_lctx.thread_id())
            ==> pagetable_window_typed_lock_map_aligned(new_k.pt_mp, new_k.pt_lower.view(), new_lctx.pagetable_window_lock_map(), new_lctx.pagetable_lock_map(), new_lctx.thread_id()),
{
    assert(pagetable_perms_wf(old_k.pt_mp) && new_k.pt_mp.perms_wf() ==> pagetable_perms_wf(new_k.pt_mp)) by { reveal(pagetable_perms_wf); };
    assert(pagetable_lower_wf(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_lower_wf(new_k.pt_mp, new_k.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(new_k.pt_mp, new_k.pt_lower.view())) by {
        reveal(pagetable_window_holders_hold_pagetable); reveal(PageTableHigher::wf_l4);
    };
    assert(pagetable_hidden_leaves_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_hidden_leaves_only_when_locked(new_k.pt_mp, new_k.pt_lower.view())) by {
        reveal(pagetable_hidden_leaves_only_when_locked);
    };
    assert(pagetable_window_stale_cpus_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_stale_cpus_only_when_locked(new_k.pt_mp, new_k.pt_lower.view())) by {
        reveal(pagetable_window_stale_cpus_only_when_locked);
    };
    assert(page_pagetable_wf(old_k.pt_mp, old_k.pt_lower.view(), old_k.pg_arr) ==> page_pagetable_wf(new_k.pt_mp, new_k.pt_lower.view(), new_k.pg_arr)) by {
        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    };
    assert(pagetable_window_typed_lock_map_aligned(old_k.pt_mp, old_k.pt_lower.view(), old_lctx.pagetable_window_lock_map(), old_lctx.pagetable_lock_map(), old_lctx.thread_id())
        ==> pagetable_window_typed_lock_map_aligned(new_k.pt_mp, new_k.pt_lower.view(), new_lctx.pagetable_window_lock_map(), new_lctx.pagetable_lock_map(), new_lctx.thread_id())) by {
        reveal(pagetable_window_typed_lock_map_aligned); reveal(PageTableHigher::wf_l4);
    };
}

/// EOF closure of `KernelK::remove_pagetable_and_reclaim_4k_page_perms`: the removed table owned no window page, so
/// this thread held none of its windows and the page-table invariants and lock alignment carry over.
proof fn remove_pagetable_and_reclaim_4k_page_perms_eof(old_k: KernelK, new_k: KernelK, old_lctx: LocalContext, new_lctx: LocalContext, pagetable_ptr: RwLockPageTableRoot)
    requires
        typed_lock_maps_aligned(&old_k, &old_lctx),
        old_k.pt_mp.dom().contains(pagetable_ptr),
        old_k.pt_lower.view().dom().contains(pagetable_ptr),
        pagetable_c(old_k.pt_mp, old_k.pt_lower.view(), pagetable_ptr).wf(),
        pagetable_c(old_k.pt_mp, old_k.pt_lower.view(), pagetable_ptr).page_closure() =~= set![old_k.pt_mp.spec_index(pagetable_ptr).view().cr3],
        new_k == (KernelK { pt_mp: new_k.pt_mp, pt_lower: new_k.pt_lower, ..old_k }),
        new_k.pt_mp.dom() =~= old_k.pt_mp.dom().remove(pagetable_ptr),
        forall|p: RwLockPageTableRoot| #![trigger new_k.pt_mp.spec_index(p)] new_k.pt_mp.dom().contains(p) ==> new_k.pt_mp.spec_index(p) == old_k.pt_mp.spec_index(p),
        forall|p: RwLockPageTableRoot| #![trigger new_k.pt_mp.lock_id_by_key(p)] new_k.pt_mp.dom().contains(p) ==> new_k.pt_mp.lock_id_by_key(p) == old_k.pt_mp.lock_id_by_key(p),
        new_k.pt_mp.perms_wf(),
        new_k.pt_lower.view() == old_k.pt_lower.view().remove(pagetable_ptr),
        forall|r: RwLockPageTableRoot|
            #![trigger pagetable_c(new_k.pt_mp, new_k.pt_lower.view(), r)]
            new_k.pt_mp.dom().contains(r) ==> pagetable_c(new_k.pt_mp, new_k.pt_lower.view(), r) == pagetable_c(old_k.pt_mp, old_k.pt_lower.view(), r),
        new_lctx.cpu_id() == old_lctx.cpu_id(),
        new_lctx.thread_id() == old_lctx.thread_id(),
        typed_lock_maps_removed(&old_lctx, &new_lctx, KernelObjId::PageTable(pagetable_ptr)),
    ensures
        pagetable_perms_wf(old_k.pt_mp) ==> pagetable_perms_wf(new_k.pt_mp),
        pagetable_lower_wf(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_lower_wf(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_hidden_leaves_only_when_locked(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_stale_cpus_only_when_locked(new_k.pt_mp, new_k.pt_lower.view()),
        pagetable_lower_backup_wf(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_lower_backup_wf(new_k.pt_mp, new_k.pt_lower.view()),
        typed_lock_maps_aligned(&new_k, &new_lctx),
{
    assert(pagetable_perms_wf(old_k.pt_mp) ==> pagetable_perms_wf(new_k.pt_mp)) by { reveal(pagetable_perms_wf); };
    assert(pagetable_lower_wf(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_lower_wf(new_k.pt_mp, new_k.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(new_k.pt_mp, new_k.pt_lower.view())) by {
        reveal(pagetable_window_holders_hold_pagetable);
    };
    assert(pagetable_hidden_leaves_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_hidden_leaves_only_when_locked(new_k.pt_mp, new_k.pt_lower.view())) by {
        reveal(pagetable_hidden_leaves_only_when_locked);
    };
    assert(pagetable_window_stale_cpus_only_when_locked(old_k.pt_mp, old_k.pt_lower.view()) ==> pagetable_window_stale_cpus_only_when_locked(new_k.pt_mp, new_k.pt_lower.view())) by {
        reveal(pagetable_window_stale_cpus_only_when_locked);
    };
    let removed = old_k.pt_mp.spec_index(pagetable_ptr).view();
    assert(removed.l3_tables.view().dom().subset_of(pagetable_c(old_k.pt_mp, old_k.pt_lower.view(), pagetable_ptr).page_closure())
        && removed.l4_table.view().dom().disjoint(removed.l3_tables.view().dom())) by { reveal(PageTableHigher::table_pages_wf); };
    assert(removed.l3_tables.view().dom() =~= Set::<PageMapPtr>::empty()) by { reveal(PageTableHigher::wf_l4); };
    assert(pagetable_window_typed_lock_map_aligned(new_k.pt_mp, new_k.pt_lower.view(), new_lctx.pagetable_window_lock_map(), new_lctx.pagetable_lock_map(), new_lctx.thread_id())) by {
        broadcast use spec_va_2m_valid_index_roundtrip; reveal(pagetable_window_typed_lock_map_aligned); reveal(PageTableHigher::wf_l4);
    };
    assert(typed_lock_maps_aligned(&new_k, &new_lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
}
} // verus!

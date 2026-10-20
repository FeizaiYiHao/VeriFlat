use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

pub type PageTableHigherLockedMap = PageTableLockedMap;

/// Publish a fresh page table: retype `page_ptr` into the write-held big lock around `higher_value`, insert it into
/// `pt_mp`, and file its window half under the same root in `pt_lower`.
pub fn retype_page_to_pagetable_c_and_insert(pt_mp: &mut PageTableHigherLockedMap, Tracked(pt_lower): Tracked<&mut Map<RwLockPageTableRoot, PageTableLower<PT_TYPE>>>,
    page_ptr: PagePtr, higher_value: PageTableHigher<PT_TYPE>, Tracked(lower_value): Tracked<PageTableLower<PT_TYPE>>, Tracked(page_perm): Tracked<PagePerm4k>,
    Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(pt_mp).perms_wf(),
        !old(pt_mp).dom().contains(page_ptr),
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        (PageTableC { higher: higher_value, lower: lower_value }).wf(),
        old(pt_mp).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        final(pt_mp).perms_wf(),
        final(pt_mp).dom() =~= old(pt_mp).dom().insert(page_ptr),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(pt_mp).spec_index(ptr)]
            #![trigger old(pt_mp).spec_index(ptr)]
            #![trigger old(pt_mp).dom().contains(ptr)]
            #![trigger final(pt_mp).dom().contains(ptr)]
            old(pt_mp).dom().contains(ptr) ==> {
                &&& final(pt_mp).dom().contains(ptr)
                &&& final(pt_mp).spec_index(ptr) == old(pt_mp).spec_index(ptr)
            },
        forall|ptr: RwLockPageTableRoot|
            #![trigger old(pt_mp).lock_id_by_key(ptr)]
            #![trigger final(pt_mp).lock_id_by_key(ptr)]
            old(pt_mp).dom().contains(ptr) ==> final(pt_mp).lock_id_by_key(ptr) == old(pt_mp).lock_id_by_key(ptr),
        final(pt_mp).spec_index(page_ptr).is_init(),
        final(pt_mp).spec_index(page_ptr).view() == higher_value,
        final(pt_mp).spec_index(page_ptr).view_ghost() == lower_value,
        !final(pt_mp).spec_index(page_ptr).being_killed(),
        *final(pt_lower) == old(pt_lower).insert(page_ptr, lower_value),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), page_ptr, TypedLockMode::Write),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(pt_mp).lock_id_by_key(page_ptr),
        final(pt_mp).lock_id_by_key(page_ptr) == (LockId { container: LockOwnerId::None, process: LockOwnerId::None, major: PAGE_TABLE_LOCK_MAJOR, minor: seq![page_ptr] }),
        final(pt_mp).spec_index(page_ptr).write_lock_perm_match(&ret.view()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(page_ptr), TypedHeldLock { lock_id: final(pt_mp).lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
        final(pt_mp).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
{
    let (Tracked(pagetable_rwlock_perm), Tracked(pagetable_perm)) = retype_page_perm_to_rwlock::<PageTableHigher<PT_TYPE>, (), PageTableLower<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>(
        page_ptr, higher_value, (), Ghost(lower_value), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::PageTable(page_ptr)));
    pt_mp.insert_with_perm(page_ptr, Tracked(pagetable_rwlock_perm));
    proof {
        pt_lower.tracked_insert(page_ptr, lower_value);
        assert(pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    Tracked(pagetable_perm)
}

impl PageTableHigher<PT_TYPE> {
    /// Copy this table's kernel-half root entries into an unpublished root page.
    pub fn copy_kernel_entries_to_unpublished_root(&self, target_ptr: PageMapPtr, Tracked(target_perm): Tracked<&mut PointsTo<PageMap>>)
        requires
            self.inv(),
            old(target_perm).addr() == target_ptr,
            old(target_perm).is_init(),
            old(target_perm).value().wf(),
            forall|i: usize| #![trigger old(target_perm).value().spec_index(i).is_empty()] pei_valid(i) ==> old(target_perm).value().spec_index(i).is_empty(),
        ensures
            final(target_perm).addr() == target_ptr,
            final(target_perm).is_init(),
            final(target_perm).value().wf(),
            forall|i: usize|
                #![trigger final(target_perm).value().spec_index(i).is_empty()]
                self.kernel_l4_end <= i && pei_valid(i) ==> final(target_perm).value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger final(target_perm).value().spec_index(i)]
                0 <= i < self.kernel_l4_end ==> final(target_perm).value().spec_index(i) =~= self.l4_table.view().spec_index(self.cr3).value().spec_index(i),
    {
        proof {
            self.wf_l4_cr3_at();
            self.kernel_entries_wf_len_at();
        }
        let tracked source_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        page_map_copy_kernel_entry_range(self.cr3, Tracked(source_perm), target_ptr, Tracked(&mut *target_perm), self.kernel_l4_end);
    }
}
} // verus!

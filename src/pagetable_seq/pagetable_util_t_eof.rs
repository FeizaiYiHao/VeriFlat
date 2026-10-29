use vstd::prelude::*;
verus! {
use crate::*;

/// EOF closure of `KernelK::retype_page_to_pagetable_and_insert`: the new table is empty and write-held by this thread,
/// so it has no window, and the page-table invariants and the window alignment carry over.
pub(super) proof fn retype_page_to_pagetable_and_insert_eof(
    old_k: KernelK, new_k: KernelK, old_lctx: LocalContext, new_lctx: LocalContext, page_ptr: PagePtr, higher: PageTableHigher<PT_TYPE>,
    lower: PageTableLower<PT_TYPE>, lock_perm: LockPerm,
)
    requires
        !old_k.pt_mp.dom().contains(page_ptr),
        (PageTableC { higher, lower }).wf(),
        (PageTableC { higher, lower }).is_empty(),
        new_k == (KernelK { pt_mp: new_k.pt_mp, pt_lower: new_k.pt_lower, ..old_k }),
        new_k.pt_mp.dom() =~= old_k.pt_mp.dom().insert(page_ptr),
        forall|ptr: RwLockPageTableRoot| #![trigger new_k.pt_mp.spec_index(ptr)] #![trigger old_k.pt_mp.spec_index(ptr)] old_k.pt_mp.dom().contains(ptr) ==> new_k.pt_mp.spec_index(ptr) == old_k.pt_mp.spec_index(ptr),
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

/// EOF closure of `remove_iommu_table_and_reclaim_4k_page_perms`: removing IOMMU table `iommu_table_ptr` keeps `iommu_table_perms_wf`.
pub(super) proof fn remove_iommu_table_and_reclaim_4k_page_perms_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().remove(iommu_table_ptr),
        forall|p: RwLockPageTableRoot| #![trigger post.spec_index(p)] post.dom().contains(p) ==> post.spec_index(p) == pre.spec_index(p),
    ensures iommu_table_perms_wf(pre) ==> iommu_table_perms_wf(post),
{ reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// EOF closure of `KernelK::remove_pagetable_and_reclaim_4k_page_perms`: the removed table owned no window page, so
/// this thread held none of its windows and the page-table invariants and lock alignment carry over.
pub(super) proof fn remove_pagetable_and_reclaim_4k_page_perms_eof(old_k: KernelK, new_k: KernelK, old_lctx: LocalContext, new_lctx: LocalContext, pagetable_ptr: RwLockPageTableRoot)
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

use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::locker_unlocker_pagetable_range_windows::window_successor_implies_path_le_drops_only_predecessor;

verus! {
/// Loop state of `lock_pagetable_range_windows` before window index `cursor`: only the page-table map and lower half changed
/// and table `root` keeps its leaves, higher half, L2 entries, L1 links, reverse map, stale CPUs and page closure; the windows
/// of `range` before `cursor` were unlocked and are now write-locked; `perms` holds exactly those windows, each held by this
/// thread in the window lock map; if only write-locked L2 entries hid L1 pages before, that still holds and no window in
/// `perms` hides one; every other typed lock map is unchanged.
#[verifier::opaque]
pub(super) open spec fn lock_pagetable_range_windows_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext,
    root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, big: &LockPerm, cursor: (L4Index, L3Index, L2Index)) -> bool
{
    let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root);
    &&& cur_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& cur_lctx.thread_id() == pre_lctx.thread_id()
    &&& cur_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state()
    &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &cur)
    &&& cur == (KernelK { pt_mp: cur.pt_mp, pt_lower: cur.pt_lower, ..pre })
    &&& cur.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), cur.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { cur.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& cur.pt_lower.view() =~= pre.pt_lower.view().insert(root, cur.pt_lower.view().spec_index(root))
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.higher == before.higher
    &&& after.lower.l2_perms.dom() == before.lower.l2_perms.dom()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
        whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
            && whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1()
    &&& after.lower.l1_rev_map == before.lower.l1_rev_map
    &&& after.lower.window_stale_cpus == before.lower.window_stale_cpus
    &&& after.lower.pagetable_window_locks.dom() =~= before.lower.pagetable_window_locks.dom()
    &&& forall|w: WindowVa| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)
            == if va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) { LockStateU::WriteLocked }
                else { whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w) }
    &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
        va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w)
            && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks[w] is Unlocked
    &&& after.page_closure() == before.page_closure()
    &&& before.lower.hidden_l1_tables_in_locked_windows() ==> after.lower.hidden_l1_tables_in_locked_windows()
    &&& cur_lctx.page_lock_map() == pre_lctx.page_lock_map()
    &&& cur_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map()
    &&& cur_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map()
    &&& cur_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map()
    &&& cur_lctx.container_lock_map() == pre_lctx.container_lock_map()
    &&& cur_lctx.process_lock_map() == pre_lctx.process_lock_map()
    &&& cur_lctx.thread_lock_map() == pre_lctx.thread_lock_map()
    &&& cur_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map()
    &&& cur_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map()
    &&& cur_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map()
    &&& cur_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map()
    &&& cur_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map()
    &&& cur_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map()
    &&& cur_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map()
    &&& cur_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps()
    &&& cur_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps()
    &&& cur_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps()
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) || (p == root && perms.dom().contains(w)))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == (TypedHeldLock { lock_id: window_lock_id_of(p, w), mode: TypedLockMode::Write })
    &&& forall|w: WindowVa| #![trigger perms.dom().contains(w)]
        perms.dom().contains(w) ==> {
            &&& va_range_2m_windows(*range).contains(w)
            &&& !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va))
        }
    &&& forall|w: WindowVa| #![trigger perms.index(w)]
        perms.dom().contains(w) ==> {
            &&& perms.index(w).state() is WriteLock
            &&& perms.index(w).thread_id() == pre_lctx.thread_id()
            &&& typed_lock_map_contains_mode(cur_lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
            &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_view(w).lock_state == (RwLockState::Write { thread_id: pre_lctx.thread_id(), lock_id: perms.index(w).lock_id() })
            &&& big.state() is ReadLock ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_leaves_present(w)
            &&& big.state() is ReadLock ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            &&& big.state() is ReadLock ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry_hides_l1(
                whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry_hides_l1(
                whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        }
    &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
        va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) ==> perms.dom().contains(w)
}

/// Loop state of `lock_pagetable_range_windows` before window index `next`, the successor of `cursor`, from the state before
/// `cursor` and the effect of `lock_pagetable_window` on window `window_va` at `cursor`.
pub(super) proof fn lock_pagetable_range_windows_eol_step(pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext,
    post_lctx: &LocalContext, root: RwLockPageTableRoot, range: &VaRange4K, mid_perms: Map<WindowVa, LockPerm>, post_perms: Map<WindowVa, LockPerm>, big: &LockPerm,
    window_va: WindowVa, cursor: (L4Index, L3Index, L2Index), next: (L4Index, L3Index, L2Index))
    requires
        lock_pagetable_range_windows_eol_loop_framing(pre, mid, pre_lctx, mid_lctx, root, range, mid_perms, big, cursor),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))] pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> p < root,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
        cursor.0 < 512 && cursor.1 < 512 && cursor.2 < 512,
        next == (if cursor.2 < 511 { (cursor.0, cursor.1, (cursor.2 + 1) as usize) } else if cursor.1 < 511 { (cursor.0, (cursor.1 + 1) as usize, 0usize) }
            else { ((cursor.0 + 1) as usize, 0usize, 0usize) }),
        window_va == (WindowVa { va: spec_index2va((cursor.0, cursor.1, cursor.2, 0usize)) }),
        spec_va2index(window_va.va) == (cursor.0, cursor.1, cursor.2, 0usize),
        va_range_2m_windows(*range).contains(window_va),
        post_perms == mid_perms.insert(window_va, post_perms.index(window_va)),
        post_lctx.cpu_id() == mid_lctx.cpu_id(),
        post_lctx.thread_id() == mid_lctx.thread_id(),
        post_lctx.kernel_view_locking_state() == mid_lctx.kernel_view_locking_state(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&mid, &post),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..mid }),
        post.pt_mp.unchanged_except(&mid.pt_mp, root),
        update_ghost_ensures(mid.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
            if mid.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { mid.pt_mp.spec_index(root).view_ghost() }),
        post.pt_lower.view() =~= mid.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l1_rev_map,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.window_stale_cpus,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
            == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.insert(window_va, LockStateU::WriteLocked),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(window_va),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks[window_va] is Unlocked,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).page_closure(),
        forall|w: WindowVa| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w)]
            page_table_key_2m_valid::<PT_TYPE>(w.va) && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != window_va.va
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_view(w),
        big.state() is ReadLock ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_leaves_present(window_va),
        big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)),
        big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_owner(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)
            == (RwLockState::Write { thread_id: post_perms.index(window_va).thread_id(), lock_id: post_perms.index(window_va).lock_id() }),
        post_perms.index(window_va).state() is WriteLock,
        post_perms.index(window_va).thread_id() == post_lctx.thread_id(),
        typed_lock_maps_inserted(mid_lctx, post_lctx, KernelObjId::PageTableWindow(root, window_va),
            TypedHeldLock { lock_id: window_lock_id_of(root, window_va), mode: TypedLockMode::Write }),
    ensures
        lock_pagetable_range_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, post_perms, big, next),
{
    reveal(lock_pagetable_range_windows_eol_loop_framing);
    window_successor_implies_path_le_drops_only_predecessor((cursor.0, cursor.1, cursor.2, 0usize), (next.0, next.1, next.2, 0usize));
    broadcast use spec_va_2m_valid_index_roundtrip, kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
}

/// The ensures of `lock_pagetable_range_windows`, other than the kernel invariant and lock-map alignment, from its loop
/// state once `cursor` has passed the last window of `range`.
pub(super) proof fn lock_pagetable_range_windows_eol_exit(pre: KernelK, post: KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext, root: RwLockPageTableRoot,
    range: &VaRange4K, perms: Map<WindowVa, LockPerm>, big: &LockPerm, cursor: (L4Index, L3Index, L2Index))
    requires
        lock_pagetable_range_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, perms, big, cursor),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
        {
            let last = spec_va2index(range.view().spec_index(range.len - 1));
            !(cursor.0 < last.0 || (cursor.0 == last.0 && (cursor.1 < last.1 || (cursor.1 == last.1 && cursor.2 <= last.2))))
        },
    ensures
        post_lctx.cpu_id() == pre_lctx.cpu_id(),
        post_lctx.thread_id() == pre_lctx.thread_id(),
        post_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, root),
        update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
            if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() }),
        post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l1_rev_map,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.window_stale_cpus,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
            == pagetable_window_locks_after_locking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w)
                ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks[w] is Unlocked,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).page_closure(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        post_lctx.page_lock_map() == pre_lctx.page_lock_map(),
        post_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map(),
        post_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map(),
        post_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map(),
        post_lctx.container_lock_map() == pre_lctx.container_lock_map(),
        post_lctx.process_lock_map() == pre_lctx.process_lock_map(),
        post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
        post_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map(),
        post_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map(),
        post_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map(),
        post_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map(),
        post_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map(),
        post_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map(),
        post_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map(),
        post_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps(),
        post_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps(),
        post_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            post_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) || (p == root && va_range_2m_windows(*range).contains(w))),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> post_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger perms.dom().contains(w)] perms.dom().contains(w) ==> va_range_2m_windows(*range).contains(w),
        forall|w: WindowVa|
            #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) ==> {
                &&& perms.dom().contains(w)
                &&& perms.index(w).state() is WriteLock
                &&& perms.index(w).thread_id() == post_lctx.thread_id()
                &&& typed_lock_map_contains_mode(post_lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), post_lctx.thread_id())
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_owner(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)),
                    spec_v2l2index(w.va)) == (RwLockState::Write { thread_id: perms.index(w).thread_id(), lock_id: perms.index(w).lock_id() })
                &&& big.state() is ReadLock ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_leaves_present(w)
                &&& big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                    whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                &&& big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(
                    whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(
                    whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            },
{
    reveal(lock_pagetable_range_windows_eol_loop_framing);
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
        =~= pagetable_window_locks_after_locking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range));
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Loop state of `lock_pagetable_range_existing_windows` before window index `cursor`: only the page-table map and lower half
/// changed and table `root` keeps its leaves, higher half, L2 entries, L1 links, reverse map, stale CPUs and page closure; the
/// windows of `range` before `cursor` were unlocked and are now write-locked; `perms` holds exactly those of them whose L3 entry
/// links an L2 page, each held by this thread in the window lock map; if only write-locked L2 entries hid L1 pages before, that
/// still holds and no window in `perms` hides one; every other typed lock map is unchanged.
#[verifier::opaque]
pub(super) open spec fn lock_pagetable_range_existing_windows_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext,
    root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, big: &LockPerm, cursor: (L4Index, L3Index, L2Index)) -> bool
{
    let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root);
    &&& cur_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& cur_lctx.thread_id() == pre_lctx.thread_id()
    &&& cur_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state()
    &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &cur)
    &&& cur == (KernelK { pt_mp: cur.pt_mp, pt_lower: cur.pt_lower, ..pre })
    &&& cur.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), cur.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { cur.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& cur.pt_lower.view() =~= pre.pt_lower.view().insert(root, cur.pt_lower.view().spec_index(root))
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.higher == before.higher
    &&& after.lower.l2_perms.dom() == before.lower.l2_perms.dom()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
        whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
            && whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1()
    &&& after.lower.l1_rev_map == before.lower.l1_rev_map
    &&& after.lower.window_stale_cpus == before.lower.window_stale_cpus
    &&& after.lower.pagetable_window_locks.dom() =~= before.lower.pagetable_window_locks.dom()
    &&& forall|w: WindowVa| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)
            == if va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) { LockStateU::WriteLocked }
                else { whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w) }
    &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
        va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w)
            && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks[w] is Unlocked
    &&& after.page_closure() == before.page_closure()
    &&& before.lower.hidden_l1_tables_in_locked_windows() ==> after.lower.hidden_l1_tables_in_locked_windows()
    &&& cur_lctx.page_lock_map() == pre_lctx.page_lock_map()
    &&& cur_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map()
    &&& cur_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map()
    &&& cur_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map()
    &&& cur_lctx.container_lock_map() == pre_lctx.container_lock_map()
    &&& cur_lctx.process_lock_map() == pre_lctx.process_lock_map()
    &&& cur_lctx.thread_lock_map() == pre_lctx.thread_lock_map()
    &&& cur_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map()
    &&& cur_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map()
    &&& cur_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map()
    &&& cur_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map()
    &&& cur_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map()
    &&& cur_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map()
    &&& cur_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map()
    &&& cur_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps()
    &&& cur_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps()
    &&& cur_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps()
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) || (p == root && perms.dom().contains(w)))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == (TypedHeldLock { lock_id: window_lock_id_of(p, w), mode: TypedLockMode::Write })
    &&& forall|w: WindowVa| #![trigger perms.dom().contains(w)]
        perms.dom().contains(w) ==> {
            &&& va_range_2m_windows(*range).contains(w)
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va))
        }
    &&& forall|w: WindowVa| #![trigger perms.index(w)]
        perms.dom().contains(w) ==> {
            &&& perms.index(w).state() is WriteLock
            &&& perms.index(w).thread_id() == pre_lctx.thread_id()
            &&& typed_lock_map_contains_mode(cur_lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
            &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_view(w).lock_state == (RwLockState::Write { thread_id: pre_lctx.thread_id(), lock_id: perms.index(w).lock_id() })
            &&& big.state() is ReadLock ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_leaves_present(w)
            &&& big.state() is ReadLock ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            &&& big.state() is ReadLock ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry_hides_l1(
                whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> !whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry_hides_l1(
                whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        }
    &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
        va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) ==> perms.dom().contains(w)
}

/// Loop state of `lock_pagetable_range_existing_windows` before window index `next`, the successor of `cursor`, from the state
/// before `cursor` and either the effect of `lock_pagetable_window` on window `window_va` at `cursor`, when its L3 entry links an
/// L2 page, or no change otherwise.
pub(super) proof fn lock_pagetable_range_existing_windows_eol_step(pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext,
    post_lctx: &LocalContext, root: RwLockPageTableRoot, range: &VaRange4K, mid_perms: Map<WindowVa, LockPerm>, post_perms: Map<WindowVa, LockPerm>, big: &LockPerm,
    window_va: WindowVa, cursor: (L4Index, L3Index, L2Index), next: (L4Index, L3Index, L2Index), linked: bool)
    requires
        lock_pagetable_range_existing_windows_eol_loop_framing(pre, mid, pre_lctx, mid_lctx, root, range, mid_perms, big, cursor),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))] pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> p < root,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
        cursor.0 < 512 && cursor.1 < 512 && cursor.2 < 512,
        next == (if cursor.2 < 511 { (cursor.0, cursor.1, (cursor.2 + 1) as usize) } else if cursor.1 < 511 { (cursor.0, (cursor.1 + 1) as usize, 0usize) }
            else { ((cursor.0 + 1) as usize, 0usize, 0usize) }),
        window_va == (WindowVa { va: spec_index2va((cursor.0, cursor.1, cursor.2, 0usize)) }),
        spec_va2index(window_va.va) == (cursor.0, cursor.1, cursor.2, 0usize),
        va_range_2m_windows(*range).contains(window_va),
        linked == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher.spec_resolve_mapping_l3(cursor.0, cursor.1) is Some,
        !linked ==> post == mid && *post_lctx == *mid_lctx && post_perms == mid_perms,
        !linked ==> !whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(window_va),
        linked ==> {
            &&& post_perms == mid_perms.insert(window_va, post_perms.index(window_va))
            &&& post_lctx.cpu_id() == mid_lctx.cpu_id()
            &&& post_lctx.thread_id() == mid_lctx.thread_id()
            &&& post_lctx.kernel_view_locking_state() == mid_lctx.kernel_view_locking_state()
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&mid, &post)
            &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..mid })
            &&& post.pt_mp.unchanged_except(&mid.pt_mp, root)
            &&& update_ghost_ensures(mid.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
                if mid.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { mid.pt_mp.spec_index(root).view_ghost() })
            &&& post.pt_lower.view() =~= mid.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_4k()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_2m()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_1g()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_perms.dom()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
                whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_entry(p, i)
                    && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l1_rev_map
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.window_stale_cpus
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
                == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.insert(window_va, LockStateU::WriteLocked)
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(window_va)
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks[window_va] is Unlocked
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).page_closure()
            &&& forall|w: WindowVa| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w)]
                page_table_key_2m_valid::<PT_TYPE>(w.va) && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                    && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != window_va.va
                    ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_view(w)
            &&& big.state() is ReadLock ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_leaves_present(window_va)
            &&& big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2))
            &&& big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
                ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_owner(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)
                == (RwLockState::Write { thread_id: post_perms.index(window_va).thread_id(), lock_id: post_perms.index(window_va).lock_id() })
            &&& post_perms.index(window_va).state() is WriteLock
            &&& post_perms.index(window_va).thread_id() == post_lctx.thread_id()
            &&& typed_lock_maps_inserted(mid_lctx, post_lctx, KernelObjId::PageTableWindow(root, window_va),
                TypedHeldLock { lock_id: window_lock_id_of(root, window_va), mode: TypedLockMode::Write })
        },
    ensures
        lock_pagetable_range_existing_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, post_perms, big, next),
{
    reveal(lock_pagetable_range_existing_windows_eol_loop_framing);
    window_successor_implies_path_le_drops_only_predecessor((cursor.0, cursor.1, cursor.2, 0usize), (next.0, next.1, next.2, 0usize));
    broadcast use spec_va_2m_valid_index_roundtrip, kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
}

/// The ensures of `lock_pagetable_range_existing_windows`, other than the kernel invariant and lock-map alignment, from its loop
/// state once `cursor` has passed the last window of `range`.
pub(super) proof fn lock_pagetable_range_existing_windows_eol_exit(pre: KernelK, post: KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext, root: RwLockPageTableRoot,
    range: &VaRange4K, perms: Map<WindowVa, LockPerm>, big: &LockPerm, cursor: (L4Index, L3Index, L2Index))
    requires
        lock_pagetable_range_existing_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, perms, big, cursor),
        {
            let last = spec_va2index(range.view().spec_index(range.len - 1));
            !(cursor.0 < last.0 || (cursor.0 == last.0 && (cursor.1 < last.1 || (cursor.1 == last.1 && cursor.2 <= last.2))))
        },
    ensures
        post_lctx.cpu_id() == pre_lctx.cpu_id(),
        post_lctx.thread_id() == pre_lctx.thread_id(),
        post_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, root),
        update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
            if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() }),
        post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l1_rev_map,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.window_stale_cpus,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
            == pagetable_window_locks_after_locking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w)
                ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks[w] is Unlocked,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).page_closure(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        post_lctx.page_lock_map() == pre_lctx.page_lock_map(),
        post_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map(),
        post_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map(),
        post_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map(),
        post_lctx.container_lock_map() == pre_lctx.container_lock_map(),
        post_lctx.process_lock_map() == pre_lctx.process_lock_map(),
        post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
        post_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map(),
        post_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map(),
        post_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map(),
        post_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map(),
        post_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map(),
        post_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map(),
        post_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map(),
        post_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps(),
        post_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps(),
        post_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            post_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) || (p == root && perms.dom().contains(w))),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> post_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                ==> perms.dom().contains(w),
        forall|w: WindowVa| #![trigger perms.dom().contains(w)]
            perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*range).contains(w)
                &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& perms.index(w).state() is WriteLock
                &&& perms.index(w).thread_id() == post_lctx.thread_id()
                &&& typed_lock_map_contains_mode(post_lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), post_lctx.thread_id())
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_owner(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)),
                    spec_v2l2index(w.va)) == (RwLockState::Write { thread_id: perms.index(w).thread_id(), lock_id: perms.index(w).lock_id() })
                &&& big.state() is ReadLock ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_leaves_present(w)
                &&& big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                    whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                &&& big.state() is ReadLock ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(
                    whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(
                    whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            },
{
    reveal(lock_pagetable_range_existing_windows_eol_loop_framing);
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
        =~= pagetable_window_locks_after_locking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range));
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Loop state of `unlock_pagetable_range_windows` before window index `cursor`: only the page-table map and lower half changed
/// and table `root` keeps its leaves, higher half, L2 entries, L1 links, reverse map, stale CPUs and page closure; the windows
/// of `range` before `cursor` are now unlocked and left the window lock map, and once one was released the kernel view is in
/// its release phase; every later window of `range` is still held through `remaining`, which agrees with `perms` there, and
/// keeps its view; every other typed lock map is unchanged. If only write-locked L2 entries hid L1 pages before and no window
/// of `range` hid one, that still holds.
#[verifier::opaque]
pub(super) open spec fn unlock_pagetable_range_windows_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext,
    root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, remaining: Map<WindowVa, LockPerm>, cursor: (L4Index, L3Index, L2Index)) -> bool
{
    let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root);
    &&& cur_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& cur_lctx.thread_id() == pre_lctx.thread_id()
    &&& (cursor.0, cursor.1, cursor.2) != (spec_va2index(range.start).0, spec_va2index(range.start).1, spec_va2index(range.start).2) ==> cur_lctx.kernel_view_locking_state() is Release
    &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &cur)
    &&& cur == (KernelK { pt_mp: cur.pt_mp, pt_lower: cur.pt_lower, ..pre })
    &&& cur.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), cur.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { cur.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& cur.pt_lower.view() =~= pre.pt_lower.view().insert(root, cur.pt_lower.view().spec_index(root))
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.higher == before.higher
    &&& after.lower.l2_perms.dom() == before.lower.l2_perms.dom()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
        whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
            && whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1()
    &&& after.lower.l1_rev_map == before.lower.l1_rev_map
    &&& after.lower.window_stale_cpus == before.lower.window_stale_cpus
    &&& after.lower.pagetable_window_locks.dom() =~= before.lower.pagetable_window_locks.dom()
    &&& forall|w: WindowVa| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)
            == if va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) { LockStateU::Unlocked }
                else { whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w) }
    &&& after.page_closure() == before.page_closure()
    &&& before.lower.hidden_l1_tables_in_locked_windows()
        && (forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)] va_range_2m_windows(*range).contains(w) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry_hides_l1(
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        ==> after.lower.hidden_l1_tables_in_locked_windows()
    &&& cur_lctx.page_lock_map() == pre_lctx.page_lock_map()
    &&& cur_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map()
    &&& cur_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map()
    &&& cur_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map()
    &&& cur_lctx.container_lock_map() == pre_lctx.container_lock_map()
    &&& cur_lctx.process_lock_map() == pre_lctx.process_lock_map()
    &&& cur_lctx.thread_lock_map() == pre_lctx.thread_lock_map()
    &&& cur_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map()
    &&& cur_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map()
    &&& cur_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map()
    &&& cur_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map()
    &&& cur_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map()
    &&& cur_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map()
    &&& cur_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map()
    &&& cur_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps()
    &&& cur_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps()
    &&& cur_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps()
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w))
            == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va))))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w))
    &&& forall|k: (RwLockPageTableRoot, WindowVa)| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains(k)]
        cur_lctx.pagetable_window_lock_map().dom().contains(k) ==> cur_lctx.pagetable_window_lock_map().dom().contains((k.0, k.1))
    &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
        va_range_2m_windows(*range).contains(w) && spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) ==> {
            &&& remaining.dom().contains(w)
            &&& typed_lock_map_contains_mode(cur_lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
            &&& remaining.index(w) == perms.index(w)
            &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_view(w) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_view(w)
        }
}

/// Loop state of `unlock_pagetable_range_windows` before window index `next`, the successor of `cursor`, from the state before
/// `cursor` and the effect of `unlock_pagetable_window` on window `window_va` at `cursor`.
pub(super) proof fn unlock_pagetable_range_windows_eol_step(pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext,
    post_lctx: &LocalContext, root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, mid_remaining: Map<WindowVa, LockPerm>,
    post_remaining: Map<WindowVa, LockPerm>, window_va: WindowVa, cursor: (L4Index, L3Index, L2Index), next: (L4Index, L3Index, L2Index))
    requires
        unlock_pagetable_range_windows_eol_loop_framing(pre, mid, pre_lctx, mid_lctx, root, range, perms, mid_remaining, cursor),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
        cursor.0 < 512 && cursor.1 < 512 && cursor.2 < 512,
        next == (if cursor.2 < 511 { (cursor.0, cursor.1, (cursor.2 + 1) as usize) } else if cursor.1 < 511 { (cursor.0, (cursor.1 + 1) as usize, 0usize) }
            else { ((cursor.0 + 1) as usize, 0usize, 0usize) }),
        window_va == (WindowVa { va: spec_index2va((cursor.0, cursor.1, cursor.2, 0usize)) }),
        spec_va2index(window_va.va) == (cursor.0, cursor.1, cursor.2, 0usize),
        va_range_2m_windows(*range).contains(window_va),
        post_remaining == mid_remaining.remove(window_va),
        post_lctx.cpu_id() == mid_lctx.cpu_id(),
        post_lctx.thread_id() == mid_lctx.thread_id(),
        post_lctx.kernel_view_locking_state() is Release,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&mid, &post),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..mid }),
        post.pt_mp.unchanged_except(&mid.pt_mp, root),
        update_ghost_ensures(mid.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
            if mid.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { mid.pt_mp.spec_index(root).view_ghost() }),
        post.pt_lower.view() =~= mid.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l1_rev_map,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.window_stale_cpus,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
            == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.insert(window_va, LockStateU::Unlocked),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(window_va),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).page_closure(),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            && !whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        typed_lock_maps_removed(mid_lctx, post_lctx, KernelObjId::PageTableWindow(root, window_va)),
        forall|w: WindowVa| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w)]
            page_table_key_2m_valid::<PT_TYPE>(w.va) && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != window_va.va
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_view(w),
    ensures
        unlock_pagetable_range_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, perms, post_remaining, next),
{
    reveal(unlock_pagetable_range_windows_eol_loop_framing);
    window_successor_implies_path_le_drops_only_predecessor((cursor.0, cursor.1, cursor.2, 0usize), (next.0, next.1, next.2, 0usize));
    broadcast use spec_va_2m_valid_index_roundtrip, kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
}

/// The ensures of `unlock_pagetable_range_windows`, other than the kernel invariant and lock-map alignment, from its loop state
/// once `cursor` has passed the last window of `range`, which does not end before its first window.
pub(super) proof fn unlock_pagetable_range_windows_eol_exit(pre: KernelK, post: KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, remaining: Map<WindowVa, LockPerm>, cursor: (L4Index, L3Index, L2Index))
    requires
        unlock_pagetable_range_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, perms, remaining, cursor),
        {
            let first = spec_va2index(range.start);
            let last = spec_va2index(range.view().spec_index(range.len - 1));
            &&& first.0 < last.0 || (first.0 == last.0 && (first.1 < last.1 || (first.1 == last.1 && first.2 <= last.2)))
            &&& !(cursor.0 < last.0 || (cursor.0 == last.0 && (cursor.1 < last.1 || (cursor.1 == last.1 && cursor.2 <= last.2))))
        },
    ensures
        post_lctx.cpu_id() == pre_lctx.cpu_id(),
        post_lctx.thread_id() == pre_lctx.thread_id(),
        post_lctx.kernel_view_locking_state() is Release,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, root),
        update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
            if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() }),
        post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l1_rev_map,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.window_stale_cpus,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
            == pagetable_window_locks_after_unlocking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).page_closure(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            && (forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)] va_range_2m_windows(*range).contains(w) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry_hides_l1(
                whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        post_lctx.page_lock_map() == pre_lctx.page_lock_map(),
        post_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map(),
        post_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map(),
        post_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map(),
        post_lctx.container_lock_map() == pre_lctx.container_lock_map(),
        post_lctx.process_lock_map() == pre_lctx.process_lock_map(),
        post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
        post_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map(),
        post_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map(),
        post_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map(),
        post_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map(),
        post_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map(),
        post_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map(),
        post_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map(),
        post_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps(),
        post_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps(),
        post_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            post_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && va_range_2m_windows(*range).contains(w))),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            post_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> post_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w)),
        (forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> p == root && va_range_2m_windows(*range).contains(w)) ==> post_lctx.pagetable_window_lock_map().dom().is_empty(),
{
    reveal(unlock_pagetable_range_windows_eol_loop_framing);
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
        =~= pagetable_window_locks_after_unlocking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range));
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Loop state of `unlock_pagetable_range_existing_windows` before window index `cursor`: only the page-table map and lower half
/// changed and table `root` keeps its leaves, higher half, L2 entries, L1 links, reverse map, stale CPUs and page closure; the
/// windows of `range` before `cursor` are now unlocked and the linked ones left the window lock map; every later linked window of
/// `range` is still held through `remaining`, which agrees with `perms` there, and keeps its view; every other typed lock map is
/// unchanged. If only write-locked L2 entries hid L1 pages before and no window in `perms` hid one, that still holds.
#[verifier::opaque]
pub(super) open spec fn unlock_pagetable_range_existing_windows_eol_loop_framing(pre: KernelK, cur: KernelK, pre_lctx: &LocalContext, cur_lctx: &LocalContext,
    root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, remaining: Map<WindowVa, LockPerm>, cursor: (L4Index, L3Index, L2Index)) -> bool
{
    let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root);
    &&& cur_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& cur_lctx.thread_id() == pre_lctx.thread_id()
    &&& cur_lctx.kernel_view_locking_state() is Release || cur_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state()
    &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &cur)
    &&& cur == (KernelK { pt_mp: cur.pt_mp, pt_lower: cur.pt_lower, ..pre })
    &&& cur.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), cur.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { cur.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& cur.pt_lower.view() =~= pre.pt_lower.view().insert(root, cur.pt_lower.view().spec_index(root))
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.higher == before.higher
    &&& after.lower.l2_perms.dom() == before.lower.l2_perms.dom()
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
        whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
            && whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1()
    &&& after.lower.l1_rev_map == before.lower.l1_rev_map
    &&& after.lower.window_stale_cpus == before.lower.window_stale_cpus
    &&& after.lower.pagetable_window_locks.dom() =~= before.lower.pagetable_window_locks.dom()
    &&& forall|w: WindowVa| #![trigger whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(w) ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w)
            == if va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) { LockStateU::Unlocked }
                else { whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.spec_index(w) }
    &&& after.page_closure() == before.page_closure()
    &&& before.lower.hidden_l1_tables_in_locked_windows()
        && (forall|w: WindowVa| #![trigger perms.dom().contains(w)] perms.dom().contains(w) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry_hides_l1(
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        ==> after.lower.hidden_l1_tables_in_locked_windows()
    &&& cur_lctx.page_lock_map() == pre_lctx.page_lock_map()
    &&& cur_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map()
    &&& cur_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map()
    &&& cur_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map()
    &&& cur_lctx.container_lock_map() == pre_lctx.container_lock_map()
    &&& cur_lctx.process_lock_map() == pre_lctx.process_lock_map()
    &&& cur_lctx.thread_lock_map() == pre_lctx.thread_lock_map()
    &&& cur_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map()
    &&& cur_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map()
    &&& cur_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map()
    &&& cur_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map()
    &&& cur_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map()
    &&& cur_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map()
    &&& cur_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map()
    &&& cur_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps()
    &&& cur_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps()
    &&& cur_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps()
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && va_range_2m_windows(*range).contains(w)
            && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            && !spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va))))
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains((p, w))]
        cur_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> cur_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w))
    &&& forall|k: (RwLockPageTableRoot, WindowVa)| #![trigger cur_lctx.pagetable_window_lock_map().dom().contains(k)]
        cur_lctx.pagetable_window_lock_map().dom().contains(k) ==> cur_lctx.pagetable_window_lock_map().dom().contains((k.0, k.1))
    &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
        va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            && spec_l4_index_path_le((cursor.0, cursor.1, cursor.2, 0usize), spec_va2index(w.va)) ==> {
            &&& remaining.dom().contains(w)
            &&& perms.dom().contains(w)
            &&& typed_lock_map_contains_mode(cur_lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
            &&& remaining.index(w) == perms.index(w)
            &&& whole_pagetable(cur.pt_mp, cur.pt_lower.view(), root).window_view(w) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_view(w)
        }
}

/// Loop state of `unlock_pagetable_range_existing_windows` before window index `next`, the successor of `cursor`, from the state
/// before `cursor` and either the effect of `unlock_pagetable_window` on window `window_va` at `cursor`, when its L3 entry links an
/// L2 page, or no change otherwise.
pub(super) proof fn unlock_pagetable_range_existing_windows_eol_step(pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext,
    post_lctx: &LocalContext, root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, mid_remaining: Map<WindowVa, LockPerm>,
    post_remaining: Map<WindowVa, LockPerm>, window_va: WindowVa, cursor: (L4Index, L3Index, L2Index), next: (L4Index, L3Index, L2Index), linked: bool)
    requires
        unlock_pagetable_range_existing_windows_eol_loop_framing(pre, mid, pre_lctx, mid_lctx, root, range, perms, mid_remaining, cursor),
        whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
        cursor.0 < 512 && cursor.1 < 512 && cursor.2 < 512,
        next == (if cursor.2 < 511 { (cursor.0, cursor.1, (cursor.2 + 1) as usize) } else if cursor.1 < 511 { (cursor.0, (cursor.1 + 1) as usize, 0usize) }
            else { ((cursor.0 + 1) as usize, 0usize, 0usize) }),
        window_va == (WindowVa { va: spec_index2va((cursor.0, cursor.1, cursor.2, 0usize)) }),
        spec_va2index(window_va.va) == (cursor.0, cursor.1, cursor.2, 0usize),
        va_range_2m_windows(*range).contains(window_va),
        linked == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher.spec_resolve_mapping_l3(cursor.0, cursor.1) is Some,
        !linked ==> post == mid && *post_lctx == *mid_lctx && post_remaining == mid_remaining,
        !linked ==> !whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(window_va),
        linked ==> {
            &&& post_remaining == mid_remaining.remove(window_va)
            &&& post_lctx.cpu_id() == mid_lctx.cpu_id()
            &&& post_lctx.thread_id() == mid_lctx.thread_id()
            &&& post_lctx.kernel_view_locking_state() is Release
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&mid, &post)
            &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..mid })
            &&& post.pt_mp.unchanged_except(&mid.pt_mp, root)
            &&& update_ghost_ensures(mid.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
                if mid.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { mid.pt_mp.spec_index(root).view_ghost() })
            &&& post.pt_lower.view() =~= mid.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_4k()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_2m()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).mapping_1g()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).higher
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_perms.dom()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
                whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_entry(p, i)
                    && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l1_rev_map
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.window_stale_cpus
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
                == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.insert(window_va, LockStateU::Unlocked)
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(window_va)
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).page_closure()
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
                && !whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_l2_page(cursor.0, cursor.1), cursor.2)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            &&& typed_lock_maps_removed(mid_lctx, post_lctx, KernelObjId::PageTableWindow(root, window_va))
            &&& forall|w: WindowVa| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w)]
                page_table_key_2m_valid::<PT_TYPE>(w.va) && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                    && whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != window_va.va
                    ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), root).window_view(w)
        },
    ensures
        unlock_pagetable_range_existing_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, perms, post_remaining, next),
{
    reveal(unlock_pagetable_range_existing_windows_eol_loop_framing);
    window_successor_implies_path_le_drops_only_predecessor((cursor.0, cursor.1, cursor.2, 0usize), (next.0, next.1, next.2, 0usize));
    broadcast use spec_va_2m_valid_index_roundtrip, kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
}

/// The ensures of `unlock_pagetable_range_existing_windows`, other than the kernel invariant and lock-map alignment, from its loop
/// state once `cursor` has passed the last window of `range`, where `perms` holds exactly the linked windows of `range`.
pub(super) proof fn unlock_pagetable_range_existing_windows_eol_exit(pre: KernelK, post: KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    root: RwLockPageTableRoot, range: &VaRange4K, perms: Map<WindowVa, LockPerm>, remaining: Map<WindowVa, LockPerm>, cursor: (L4Index, L3Index, L2Index))
    requires
        unlock_pagetable_range_existing_windows_eol_loop_framing(pre, post, pre_lctx, post_lctx, root, range, perms, remaining, cursor),
        {
            let last = spec_va2index(range.view().spec_index(range.len - 1));
            !(cursor.0 < last.0 || (cursor.0 == last.0 && (cursor.1 < last.1 || (cursor.1 == last.1 && cursor.2 <= last.2))))
        },
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                ==> perms.dom().contains(w),
        forall|w: WindowVa| #![trigger perms.dom().contains(w)]
            perms.dom().contains(w) ==> va_range_2m_windows(*range).contains(w)
                && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some,
    ensures
        post_lctx.cpu_id() == pre_lctx.cpu_id(),
        post_lctx.thread_id() == pre_lctx.thread_id(),
        post_lctx.kernel_view_locking_state() is Release || post_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, root),
        update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
            if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() }),
        post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).higher == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_perms.dom() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l1_rev_map == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l1_rev_map,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.window_stale_cpus,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
            == pagetable_window_locks_after_unlocking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).page_closure() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).page_closure(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            && (forall|w: WindowVa| #![trigger perms.dom().contains(w)] perms.dom().contains(w) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry_hides_l1(
                whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        post_lctx.page_lock_map() == pre_lctx.page_lock_map(),
        post_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map(),
        post_lctx.pcid_needflush_lock_map() == pre_lctx.pcid_needflush_lock_map(),
        post_lctx.cpu_offline_flag_lock_map() == pre_lctx.cpu_offline_flag_lock_map(),
        post_lctx.container_lock_map() == pre_lctx.container_lock_map(),
        post_lctx.process_lock_map() == pre_lctx.process_lock_map(),
        post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
        post_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map(),
        post_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map(),
        post_lctx.pcid_allocator_lock_map() == pre_lctx.pcid_allocator_lock_map(),
        post_lctx.cpu_set_lock_map() == pre_lctx.cpu_set_lock_map(),
        post_lctx.pagetable_lock_map() == pre_lctx.pagetable_lock_map(),
        post_lctx.iommu_table_lock_map() == pre_lctx.iommu_table_lock_map(),
        post_lctx.iommu_root_table_lock_map() == pre_lctx.iommu_root_table_lock_map(),
        post_lctx.allocator_4k_lock_maps() == pre_lctx.allocator_4k_lock_maps(),
        post_lctx.allocator_2m_lock_maps() == pre_lctx.allocator_2m_lock_maps(),
        post_lctx.allocator_1g_lock_maps() == pre_lctx.allocator_1g_lock_maps(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            post_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && perms.dom().contains(w))),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            post_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> post_lctx.pagetable_window_lock_map().index((p, w)) == pre_lctx.pagetable_window_lock_map().index((p, w)),
        (forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> p == root && perms.dom().contains(w)) ==> post_lctx.pagetable_window_lock_map().dom().is_empty(),
{
    reveal(unlock_pagetable_range_existing_windows_eol_loop_framing);
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks
        =~= pagetable_window_locks_after_unlocking_range(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks, *range));
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}
} // verus!

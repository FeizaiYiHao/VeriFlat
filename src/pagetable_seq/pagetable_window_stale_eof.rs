use vstd::prelude::*;
verus! {
use crate::*;

/// The stale-CPU map after window `(l2_page, l2i)` is recorded with the stale CPUs `cpus`.
pub open spec fn window_stale_cpus_after_set(stale: Map<(PageMapPtr, L2Index), Set<CpuId>>, l2_page: PageMapPtr, l2i: L2Index, cpus: Set<CpuId>) -> Map<(PageMapPtr, L2Index), Set<CpuId>> {
    stale.insert((l2_page, l2i), cpus)
}

/// The stale-CPU map after `cpu_id` is dropped from every record the thread may change: all of them while it write-holds
/// the table, otherwise the records of the windows it holds in `lower`.
pub open spec fn window_stale_cpus_after_remove_cpu(stale: Map<(PageMapPtr, L2Index), Set<CpuId>>, lower: PageTableLower<PT_TYPE>, root_write_held: bool, thread_id: LockThreadId, cpu_id: CpuId)
    -> Map<(PageMapPtr, L2Index), Set<CpuId>>
{
    Map::new(stale.dom(), |k: (PageMapPtr, L2Index)| if root_write_held || (lower.l2_lock.dom().contains(k.0) && pei_valid(k.1) && lower.l2_lock_of(k.0).locked_by_thread(k.1, thread_id)) {
        stale.spec_index(k).remove(cpu_id)
    } else {
        stale.spec_index(k)
    })
}

/// The stale-CPU map after the empty records the thread may change are deleted: all of them while it write-holds the table,
/// otherwise those of the windows it holds in `lower`.
pub open spec fn window_stale_cpus_after_clear_empty(stale: Map<(PageMapPtr, L2Index), Set<CpuId>>, lower: PageTableLower<PT_TYPE>, root_write_held: bool, thread_id: LockThreadId) -> Map<(PageMapPtr, L2Index), Set<CpuId>> {
    stale.filter_keys(|k: (PageMapPtr, L2Index)| !(stale.spec_index(k) == Set::<CpuId>::empty() && (root_write_held || (lower.l2_lock.dom().contains(k.0) && pei_valid(k.1) && lower.l2_lock_of(k.0).locked_by_thread(k.1, thread_id)))))
}

/// One update of a page table's stale-CPU map by `KernelK::replace_window_stale_cpus`.
pub ghost enum WindowStaleUpdate {
    Set { window: WindowVa, cpus: Set<CpuId> },
    RemoveCpu { cpu_id: CpuId },
    ClearEmpty,
}

/// The stale-CPU map of `table` after `update`, applied by thread `thread_id` that write-holds the table iff
/// `root_write_held`; a `Set` records the window under its L2 page and entry, as `window_view` reads it.
pub open spec fn window_stale_cpus_after(update: WindowStaleUpdate, table: PageTableC<PT_TYPE>, root_write_held: bool, thread_id: LockThreadId) -> Map<(PageMapPtr, L2Index), Set<CpuId>> {
    match update {
        WindowStaleUpdate::Set { window, cpus } => window_stale_cpus_after_set(table.lower.window_stale_cpus, table.window_l2_page(spec_v2l4index(window.va), spec_v2l3index(window.va)), spec_v2l2index(window.va), cpus),
        WindowStaleUpdate::RemoveCpu { cpu_id } => window_stale_cpus_after_remove_cpu(table.lower.window_stale_cpus, table.lower, root_write_held, thread_id, cpu_id),
        WindowStaleUpdate::ClearEmpty => window_stale_cpus_after_clear_empty(table.lower.window_stale_cpus, table.lower, root_write_held, thread_id),
    }
}

/// S of `KernelK::replace_window_stale_cpus`: only the stale-CPU map of page table `root` moved, with a write-held table's
/// ghost slot following; its big-lock payload, the rest of its window half, and every other table stay.
#[verifier::opaque]
pub open spec fn window_stale_cpus_update_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot) -> bool {
    let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), root);
    let after = pagetable_c(post.pt_mp, post.pt_lower.view(), root);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
    &&& post.pt_lower.view().dom() =~= pre.pt_lower.view().dom()
    &&& after.higher == before.higher
    &&& after.lower == (PageTableLower { window_stale_cpus: after.lower.window_stale_cpus, ..before.lower })
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.page_closure() == before.page_closure()
    &&& after.leaves_present() == before.leaves_present()
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
        #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
        pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
    &&& forall|l4: L4Index, l3: L3Index, l2: L2Index, t: LockThreadId|
        #![trigger after.window_locked_by_thread(l4, l3, l2, t)]
        #![trigger before.window_locked_by_thread(l4, l3, l2, t)]
        after.window_locked_by_thread(l4, l3, l2, t) == before.window_locked_by_thread(l4, l3, l2, t)
}

/// EOF closure of `KernelK::replace_window_stale_cpus`: `update` adds a record only for the window `Set` names, which a
/// table that is not write-held has locked; a `Set` that only grows a record and a `ClearEmpty` keep every listed CPU listed,
/// so the TLB invariant carries over; a `RemoveCpu` drops only `cpu_id`, whose TLB under the table's PCID is empty,
/// exempt until its activation flush, or recorded under another table; any other update brings the invariant for the new map.
pub(super) proof fn window_stale_cpus_update_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, update: WindowStaleUpdate, root_write_held: bool, thread_id: LockThreadId)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        post.pt_mp.perms_wf(),
        window_stale_cpus_update_eof_transition_framing(pre, post, root),
        pagetable_c(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus == window_stale_cpus_after(update, pagetable_c(pre.pt_mp, pre.pt_lower.view(), root), root_write_held, thread_id),
        root_write_held ==> pre.pt_mp.spec_index(root).locking_thread() is Write,
        update is Set ==> root_write_held || ({
            let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), root);
            let l2_page = before.window_l2_page(spec_v2l4index(update->Set_window.va), spec_v2l3index(update->Set_window.va));
            &&& before.lower.l2_lock.dom().contains(l2_page)
            &&& pei_valid(spec_v2l2index(update->Set_window.va))
            &&& before.lower.l2_lock_of(l2_page).locked_by_thread(spec_v2l2index(update->Set_window.va), thread_id)
        }),
        update is Set ==> (pagetable_c(pre.pt_mp, pre.pt_lower.view(), root).window_view(update->Set_window).stale_cpus is Some
            ==> pagetable_c(pre.pt_mp, pre.pt_lower.view(), root).window_view(update->Set_window).stale_cpus->Some_0.subset_of(update->Set_cpus))
            || tlb_wf_spec(pre.cpu_tlb, pre.pt_mp, post.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush),
        update is RemoveCpu ==> ({
            let cpu_id = update->RemoveCpu_cpu_id;
            let pcid = pre.pt_mp.spec_index(root).view().pcid->Some_0;
            &&& pre.pt_mp.spec_index(root).view().pcid is Some
            &&& index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            &&& pre.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
                || (pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
                || (pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != root)
        }) || tlb_wf_spec(pre.cpu_tlb, pre.pt_mp, post.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush),
    ensures
        post.inv(),
{
    reveal(window_stale_cpus_update_eof_transition_framing);
    if update is RemoveCpu {
        assert(tlb_wf_spec(pre.cpu_tlb, pre.pt_mp, post.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush)) by {
            reveal(tlb_wf_spec);
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        };
    } else if !tlb_wf_spec(pre.cpu_tlb, pre.pt_mp, post.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush) {
        window_stale_cpus_update_eof_tlb_wf(pre.cpu_tlb, pre.pt_mp, pre.pt_lower.view(), post.pt_lower.view(), root, pre.cpu_arr, pre.pcid_needflush);
    }
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    window_stale_cpus_update_eof_table_wf(pagetable_c(pre.pt_mp, pre.pt_lower.view(), root), pagetable_c(post.pt_mp, post.pt_lower.view(), root));
    pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root);
    pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), root);
    assert(pagetable_perms_wf(post.pt_mp)) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
}

/// EOF closure of `KernelK::replace_window_stale_cpus` for the windows of `root` this thread holds: each names an L2 lock
/// slot this thread holds, so `RemoveCpu` and `ClearEmpty` may change its record.
pub(super) proof fn window_stale_cpus_update_eof_held_windows(pre: KernelK, root: RwLockPageTableRoot, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        pagetable_window_typed_lock_map_aligned(pre.pt_mp, pre.pt_lower.view(), window_lock_map, pagetable_lock_map, thread_id),
    ensures
        forall|w: WindowVa| #![trigger window_lock_map.dom().contains((root, w))] window_lock_map.dom().contains((root, w)) ==> {
            let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), root);
            let l2_page = before.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va));
            &&& before.lower.l2_lock.dom().contains(l2_page)
            &&& pei_valid(spec_v2l2index(w.va))
            &&& before.lower.l2_lock_of(l2_page).locked_by_thread(spec_v2l2index(w.va), thread_id)
        },
{
    broadcast use spec_va_2m_valid_index_roundtrip;
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    reveal(pagetable_window_typed_lock_map_aligned); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); reveal(PageTableC::l2_tokens_paired);
}

/// EOF closure of `KernelK::replace_window_stale_cpus` for the table itself: no table invariant reads the stale-CPU map.
proof fn window_stale_cpus_update_eof_table_wf(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>)
    requires
        pre.wf(),
        post.higher == pre.higher,
        post.lower == (PageTableLower { window_stale_cpus: post.lower.window_stale_cpus, ..pre.lower }),
    ensures
        post.wf(),
{
    assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
    assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
    assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
    assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
    assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
    assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); };
    assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); };
    assert(post.user_only()) by { reveal(PageTableC::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
    assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); };
    assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); };
}

/// EOF closure of `KernelK::replace_window_stale_cpus` for an update that keeps every listed CPU listed: the TLB
/// invariant carries over to the new map.
pub(super) proof fn window_stale_cpus_update_eof_tlb_wf(
    cpu_tlb: CpuTLB, pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, root: RwLockPageTableRoot, cpu_arr: CpuLockedArray, needflush: PcidNeedFlushArray,
)
    requires
        tlb_wf_spec(cpu_tlb, pt_mp, pre_lower, cpu_arr, needflush),
        post_lower =~= pre_lower.insert(root, PageTableLower { window_stale_cpus: post_lower.spec_index(root).window_stale_cpus, ..pre_lower.spec_index(root) }),
        forall|k: (PageMapPtr, L2Index), c: CpuId|
            #![trigger pre_lower.spec_index(root).window_stale_cpus.spec_index(k).contains(c)]
            pre_lower.spec_index(root).window_stale_cpus.dom().contains(k) && pre_lower.spec_index(root).window_stale_cpus.spec_index(k).contains(c)
                ==> post_lower.spec_index(root).window_stale_cpus.dom().contains(k) && post_lower.spec_index(root).window_stale_cpus.spec_index(k).contains(c),
    ensures
        tlb_wf_spec(cpu_tlb, pt_mp, post_lower, cpu_arr, needflush),
{ reveal(tlb_wf_spec); }
} // verus!

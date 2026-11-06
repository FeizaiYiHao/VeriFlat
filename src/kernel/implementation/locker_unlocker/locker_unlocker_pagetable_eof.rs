use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_pagetable` and `rlock_pagetable`: only the target table's lock state moved and every
/// holder kept it, a new writer's ghost slot backs up the window half; it was not write-locked, so its hidden leaves lie in
/// locked windows, and if it was not locked at all no window of it is held, so its leaves and TLB entries are present and
/// it lists no stale CPU.
pub(super) proof fn pagetable_lock_state_eof(pre: KernelK, post: KernelK, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).inv(),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        post.pt_mp.spec_index(pagetable_ptr).view_rodata() == pre.pt_mp.spec_index(pagetable_ptr).view_rodata(),
        post.pt_mp.spec_index(pagetable_ptr).wlocked() ==> post.pt_mp.spec_index(pagetable_ptr).view_ghost() == post.pt_lower.view().spec_index(pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed(),
        post.pt_mp.spec_index(pagetable_ptr).killer_info() == pre.pt_mp.spec_index(pagetable_ptr).killer_info(),
        !pre.pt_mp.spec_index(pagetable_ptr).wlocked(),
        forall|thread_id: LockThreadId|
            #![trigger post.pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id)]
            pre.pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id) ==> post.pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id),
    ensures
        post.inv(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).hidden_leaves_in_locked_windows(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        !pre.pt_mp.spec_index(pagetable_ptr).locked() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).leaves_present(),
        !pre.pt_mp.spec_index(pagetable_ptr).locked()
            ==> pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable_ptr, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr)),
        !pre.pt_mp.spec_index(pagetable_ptr).locked() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        post.pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        !(post.prc_mp.spec_index(post.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(post.prc_mp.spec_index(post.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
            #![trigger post.pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i)]
            post.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && post.pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i) is Some
                ==> post.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(l4i) is Some,
        !(post.prc_mp.spec_index(post.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(post.prc_mp.spec_index(post.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
            #![trigger post.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
            post.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && post.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                ==> post.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    pagetable_table_stale_cpus_only_when_write_locked_at(pre.pt_mp, pagetable_ptr);
    pagetable_hidden_roots_only_when_write_locked_or_emptied_at(pre.pt_mp, pre.prc_mp, pagetable_ptr);
    assert(!pre.pt_mp.spec_index(pagetable_ptr).locked() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).leaves_present()) by {
        pagetable_hidden_leaves_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
        pre.default_pagetable_wf_at(pagetable_ptr); reveal(pagetable_window_holders_hold_pagetable); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).hidden_leaves_in_locked_windows()) by { pagetable_hidden_leaves_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); };
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows()) by { pagetable_hidden_l1_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); };
    assert(!pre.pt_mp.spec_index(pagetable_ptr).locked() ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()) by {
        broadcast use pagetable_unlocked_stale_key_absent_at;
    };
    assert(!pre.pt_mp.spec_index(pagetable_ptr).locked()
        ==> pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable_ptr, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr))) by {
        if !pre.pt_mp.spec_index(pagetable_ptr).locked() { tlb_wf_pagetable_entries_present_at(pre, pagetable_ptr); }
    };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_hidden_leaves_only_when_locked); reveal(pagetable_hidden_l1_only_when_locked); reveal(pagetable_window_stale_cpus_only_when_locked);
        reveal(pagetable_table_stale_cpus_only_when_write_locked);
    };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied);
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        container_process_page_pagetable_wf_preserved_for_pagetable_fields();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}

/// No window of a page table that no thread locks has a holder: a window holder would hold the table too.
proof fn wlock_pagetable_eof_windows_unheld(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
    requires
        pagetable_lower_wf(pt_mp, pt_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pt_lower),
        pt_mp.dom().contains(pagetable_ptr),
        !pt_mp.spec_index(pagetable_ptr).locked(),
    ensures
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.l2_perms.dom().contains(p) && pei_valid(i)
                ==> !whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(whole_pagetable(pt_mp, pt_lower, pagetable_ptr).higher.l2_rev_map.view().spec_index(p).0,
                    whole_pagetable(pt_mp, pt_lower, pagetable_ptr).higher.l2_rev_map.view().spec_index(p).1, i, whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.l2_owner(p, i)->Write_thread_id),
{
    pagetable_lower_wf_at(pt_mp, pt_lower, pagetable_ptr);
    reveal(pagetable_window_holders_hold_pagetable); reveal(WholePageTable::tables_reachable_wf);
}

/// After `wlock_pagetable` took the big lock of `pagetable_ptr` while no thread locked it, no L2 entry of the table has a
/// holder: a window holder would hold the table, an entry under an unresolvable L3 path is unheld, and an L2 entry is never
/// read-held.
pub(super) proof fn wlock_pagetable_eof_l2_entries_unlocked(pre: KernelK, post: KernelK, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        !pre.pt_mp.spec_index(pagetable_ptr).locked(),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        post.pt_lower == pre.pt_lower,
    ensures
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.l2_perms.dom().contains(p) && pei_valid(i)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i) is None,
{
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr));
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    wlock_pagetable_eof_windows_unheld(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    reveal(WholePageTable::tables_reachable_wf); reveal(WholePageTable::wf_window_locks); reveal(WholePageTable::wf_l2);
    broadcast use PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
}

/// A page table that no thread locks lists no stale CPU under key `k`: a listed window is locked, and its holder would
/// hold the table.
broadcast proof fn pagetable_unlocked_stale_key_absent_at(pre: KernelK, pagetable_ptr: RwLockPageTableRoot, k: (PageMapPtr, L2Index))
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        !pre.pt_mp.spec_index(pagetable_ptr).locked(),
    ensures !#[trigger] whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus.dom().contains(k),
{
    let c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    if c.lower.window_stale_cpus.dom().contains(k) {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
        pagetable_window_stale_cpus_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr, k.0, k.1);
        c.tables_reachable_wf_l2_at(k.0);
        let (l4i, l3i) = c.higher.l2_rev_map.view().spec_index(k.0);
        if c.spec_resolve_mapping_l3(l4i, l3i) is Some {
            c.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(l4i, l3i);
            pagetable_window_holders_hold_pagetable_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr, l4i, l3i, k.1, c.lower.l2_owner(k.0, k.1)->Write_thread_id);
        } else {
            c.wf_window_locks_l2_entry_at(k.0, k.1);
        }
    }
}

/// Closes `inv()` after `runlock_pagetable`: the releasing reader holds no window of the table, every other holder
/// keeps it, and the table stays out of write mode, so its hidden leaves stay in locked windows.
pub(super) proof fn runlock_pagetable_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        pre.pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(pre_lctx.thread_id()),
        runlock_ensures(pre.pt_mp.spec_index(pagetable_ptr), post.pt_mp.spec_index(pagetable_ptr), pre_lctx.thread_id()),
        pagetable_window_typed_lock_map_aligned(pre.pt_mp, pre.pt_lower.view(), pre_lctx.pagetable_window_lock_map(), pre_lctx.pagetable_lock_map(), pre_lctx.thread_id()),
        forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] !pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)),
    ensures
        post.inv(),
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(pagetable_hidden_leaves_only_when_locked); reveal(pagetable_hidden_l1_only_when_locked);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_window_typed_lock_map_aligned); reveal(pagetable_window_stale_cpus_only_when_locked);
        reveal(pagetable_table_stale_cpus_only_when_write_locked);
    };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied);
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        container_process_page_pagetable_wf_preserved_for_pagetable_fields();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}

/// Closes `inv()` after `wunlock_pagetable`: the writer holds no window of the released table, so no thread does, the
/// table's leaves are present, and it lists no stale CPU.
pub(super) proof fn wunlock_pagetable_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).leaves_present(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pre.pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
            #![trigger pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i)]
            pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i) is Some
                ==> pre.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(l4i) is Some,
        !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
            #![trigger pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
            pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                ==> pre.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        pre.pt_mp.spec_index(pagetable_ptr).wlocked_by_thread(pre_lctx.thread_id()),
        wunlock_ensures(pre.pt_mp.spec_index(pagetable_ptr), post.pt_mp.spec_index(pagetable_ptr)),
        pagetable_window_typed_lock_map_aligned(pre.pt_mp, pre.pt_lower.view(), pre_lctx.pagetable_window_lock_map(), pre_lctx.pagetable_lock_map(), pre_lctx.thread_id()),
        forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] !pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)),
    ensures
        post.inv(),
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(pagetable_hidden_leaves_only_when_locked); reveal(pagetable_hidden_l1_only_when_locked);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_window_typed_lock_map_aligned); reveal(pagetable_window_stale_cpus_only_when_locked);
        reveal(pagetable_table_stale_cpus_only_when_write_locked);
    };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied);
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        container_process_page_pagetable_wf_preserved_for_pagetable_fields();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}

/// `downgrade_pagetable` moved only the lock of table `pagetable_ptr`: `thread_id`'s write lock became its sole read
/// lock under the same token, and the payload, ghost slot, kill state, and window half stayed.
#[verifier::opaque]
pub(super) open spec fn downgrade_pagetable_eof_transition_framing(pre: KernelK, post: KernelK, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot) -> bool {
    &&& post == (KernelK { pt_mp: post.pt_mp, ..pre })
    &&& post.pt_mp.perms_wf()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& pre.pt_mp.spec_index(pagetable_ptr).wlocked_by_thread(thread_id)
    &&& post.pt_mp.spec_index(pagetable_ptr).locking_thread() == RwLockState::Read {
        reader_map: Map::empty().insert(thread_id, pre.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id) }
    &&& post.pt_mp.spec_index(pagetable_ptr).inv()
    &&& post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view()
    &&& post.pt_mp.spec_index(pagetable_ptr).view_rodata() == pre.pt_mp.spec_index(pagetable_ptr).view_rodata()
    &&& post.pt_mp.spec_index(pagetable_ptr).view_ghost() == pre.pt_mp.spec_index(pagetable_ptr).view_ghost()
    &&& post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed()
    &&& post.pt_mp.spec_index(pagetable_ptr).killer_info() == pre.pt_mp.spec_index(pagetable_ptr).killer_info()
}

/// Closes `inv()` after `downgrade_pagetable`: the holder keeps the table in read mode, so every window owner still
/// holds it, the table's leaves are present, and it lists no stale CPU, so no table invariant needs a writer.
pub(super) proof fn downgrade_pagetable_eof(pre: KernelK, post: KernelK, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).leaves_present(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pre.pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
            #![trigger pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i)]
            pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i) is Some
                ==> pre.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(l4i) is Some,
        !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
            #![trigger pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
            pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                ==> pre.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        downgrade_pagetable_eof_transition_framing(pre, post, thread_id, pagetable_ptr),
    ensures
        post.inv(),
{
    reveal(downgrade_pagetable_eof_transition_framing);
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(pagetable_hidden_leaves_only_when_locked); reveal(pagetable_hidden_l1_only_when_locked);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_window_stale_cpus_only_when_locked); reveal(pagetable_table_stale_cpus_only_when_write_locked);
    };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied);
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        container_process_page_pagetable_wf_preserved_for_pagetable_fields();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}
} // verus!

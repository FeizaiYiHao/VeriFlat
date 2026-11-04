use vstd::prelude::*;
use crate::*;
use crate::pagetable_concurrent::pagetable_concurrent_lock_eof::*;

verus! {
/// `lock_pagetable_window` moved only the window half of table `root`: window `(l4i, l3i, l2i)` is now owned by
/// `thread_id`, every other window keeps its holder, a write-held table's ghost slot follows its window half, and the
/// leaves and table pages are unchanged.
#[verifier::opaque]
pub(super) open spec fn lock_pagetable_window_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
    thread_id: LockThreadId, lock_token: LockToken) -> bool
{
    let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after = whole_pagetable(post.pt_mp, post.pt_lower.view(), root);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
    &&& post.pt_lower.view().dom() =~= pre.pt_lower.view().dom()
    &&& lock_window_eof_transition_framing(before, after, l4i, l3i, l2i, thread_id, lock_token)
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.page_closure() == before.page_closure()
    &&& after.leaves_present() == before.leaves_present()
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index|
        #![trigger after.spec_held_4k_l1(i4, i3, i2, i1)]
        before.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> after.spec_held_4k_l1(i4, i3, i2, i1) == before.spec_held_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index|
        #![trigger after.spec_held_2m_l2(i4, i3, i2)]
        before.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> after.spec_held_2m_l2(i4, i3, i2) == before.spec_held_2m_l2(i4, i3, i2)
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
        #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
        pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
    &&& forall|l4: L4Index, l3: L3Index, l2: L2Index, t: LockThreadId|
        #![trigger after.window_locked_by_thread(l4, l3, l2, t)]
        before.kernel_l4_end() <= l4 && pei_valid(l4) && pei_valid(l3) && pei_valid(l2) ==> after.window_locked_by_thread(l4, l3, l2, t)
            == if l4 == l4i && l3 == l3i && l2 == l2i { t == thread_id } else { before.window_locked_by_thread(l4, l3, l2, t) }
    &&& forall|w: WindowVa|
        #![trigger after.window_view(w)]
        page_table_key_2m_valid::<PT_TYPE>(w.va) && before.kernel_l4_end() <= spec_v2l4index(w.va) && before.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
            && w.va != spec_index2va((l4i, l3i, l2i, 0)) ==> after.window_view(w) == before.window_view(w)
}

/// `unlock_pagetable_window` moved only the window half of table `root`: window `(l4i, l3i, l2i)` is free, every other
/// window keeps its holder, a write-held table's ghost slot follows its window half, and the leaves and table pages
/// are unchanged.
#[verifier::opaque]
pub(super) open spec fn unlock_pagetable_window_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool {
    let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after = whole_pagetable(post.pt_mp, post.pt_lower.view(), root);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
    &&& post.pt_lower.view().dom() =~= pre.pt_lower.view().dom()
    &&& unlock_window_eof_transition_framing(before, after, l4i, l3i, l2i)
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.page_closure() == before.page_closure()
    &&& after.leaves_present() == before.leaves_present()
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index|
        #![trigger after.spec_held_4k_l1(i4, i3, i2, i1)]
        before.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> after.spec_held_4k_l1(i4, i3, i2, i1) == before.spec_held_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index|
        #![trigger after.spec_held_2m_l2(i4, i3, i2)]
        before.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> after.spec_held_2m_l2(i4, i3, i2) == before.spec_held_2m_l2(i4, i3, i2)
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
        #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
        pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
    &&& forall|l4: L4Index, l3: L3Index, l2: L2Index, t: LockThreadId|
        #![trigger after.window_locked_by_thread(l4, l3, l2, t)]
        before.kernel_l4_end() <= l4 && pei_valid(l4) && pei_valid(l3) && pei_valid(l2) ==> after.window_locked_by_thread(l4, l3, l2, t)
            == (!(l4 == l4i && l3 == l3i && l2 == l2i) && before.window_locked_by_thread(l4, l3, l2, t))
    &&& forall|w: WindowVa|
        #![trigger after.window_view(w)]
        page_table_key_2m_valid::<PT_TYPE>(w.va) && before.kernel_l4_end() <= spec_v2l4index(w.va) && before.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
            && w.va != spec_index2va((l4i, l3i, l2i, 0)) ==> after.window_view(w) == before.window_view(w)
}

/// Page-to-table records, table pages and emptied-process tables after `lock_pagetable_window`: the leaves, held entries
/// and page closure of every table are unchanged.
proof fn lock_pagetable_window_eof_page_tables(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        lock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(lock_pagetable_window_eof_transition_framing);
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        pre.default_pagetable_wf_at(root); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root); reveal(process_emptied_tables_wf); reveal(process_pagetable_wf);
    };
}

/// TLB and paging-structure caches after `lock_pagetable_window`: moving one window's owner changes nothing a cached
/// translation or paging-structure entry is checked against.
proof fn lock_pagetable_window_eof_tlb_caches(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        lock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(lock_pagetable_window_eof_transition_framing);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}

/// Closes `inv()` after `lock_pagetable_window`: the new window owner holds the table's big lock and nothing a table
/// invariant reads besides window ownership moved. The window was free, so a table that is not write-locked hides no
/// leaf in it and lists no stale CPU for it, and its L2 entry hides no L1 page while every hiding entry is write-locked.
pub(super) proof fn lock_pagetable_window_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        pre.pt_mp.spec_index(root).locked_by_thread(thread_id),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_exists(l4i, l3i),
        spec_v2l4index(spec_index2va((l4i, l3i, l2i, 0))) == l4i && spec_v2l3index(spec_index2va((l4i, l3i, l2i, 0))) == l3i && spec_v2l2index(spec_index2va((l4i, l3i, l2i, 0))) == l2i,
        post.pt_mp.perms_wf(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).wf(),
        lock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.inv(),
        !(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_leaves_present(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
        !(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)),
        !(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_held_2m_l2(i4, i3, i2),
        forall|w: WindowVa|
            #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w)]
            page_table_key_2m_valid::<PT_TYPE>(w.va) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != spec_index2va((l4i, l3i, l2i, 0))
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_view(w),
{
    reveal(lock_pagetable_window_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root);
    assert(pagetable_perms_wf(post.pt_mp)) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root); pre.default_pagetable_wf_at(root); reveal(pagetable_hidden_leaves_only_when_locked);
        broadcast use spec_va_4k_valid_index_roundtrip;
    };
    assert(pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(!(pre.pt_mp.spec_index(root).locking_thread() is Write)
        ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_leaves_present(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) })) by {
        pagetable_hidden_leaves_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), root);
    };
    assert(!(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i))) by {
        pagetable_window_stale_cpus_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), root, whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i);
    };
    assert(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows() ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).higher.wf_l4_at(l4i); whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).l3_links_l2_wf_at(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_resolve_mapping_l4(l4i)->0.addr, l3i);
    };
    assert(!(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)) by {
        pagetable_hidden_l1_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), root);
    };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    lock_pagetable_window_eof_page_tables(pre, post, root, l4i, l3i, l2i, thread_id, lock_token);
    lock_pagetable_window_eof_tlb_caches(pre, post, root, l4i, l3i, l2i, thread_id, lock_token);
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        container_process_page_pagetable_wf_preserved_for_pagetable_fields();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
}

/// Page-to-table records, table pages and emptied-process tables after `unlock_pagetable_window`: the leaves, held entries
/// and page closure of every table are unchanged.
proof fn unlock_pagetable_window_eof_page_tables(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        unlock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(unlock_pagetable_window_eof_transition_framing);
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        pre.default_pagetable_wf_at(root); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root); reveal(process_emptied_tables_wf); reveal(process_pagetable_wf);
    };
}

/// Closes `inv()` after `unlock_pagetable_window`: releasing a window only drops one window owner, a table that is not
/// write-locked hides no leaf in that window and lists no stale CPU for it, and nothing a table invariant reads besides
/// window ownership moved.
pub(super) proof fn unlock_pagetable_window_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_exists(l4i, l3i),
        spec_v2l4index(spec_index2va((l4i, l3i, l2i, 0))) == l4i && spec_v2l3index(spec_index2va((l4i, l3i, l2i, 0))) == l3i && spec_v2l2index(spec_index2va((l4i, l3i, l2i, 0))) == l2i,
        !(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_leaves_present(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
        !(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)),
        !(pre.pt_mp.spec_index(root).locking_thread() is Write) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i),
        post.pt_mp.perms_wf(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).wf(),
        unlock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i),
    ensures
        post.inv(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows()
            && !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry_hides_l1(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_entry(p, i)
                && whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).spec_held_2m_l2(i4, i3, i2),
        forall|w: WindowVa|
            #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w)]
            page_table_key_2m_valid::<PT_TYPE>(w.va) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != spec_index2va((l4i, l3i, l2i, 0))
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), root).window_view(w) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).window_view(w),
{
    reveal(unlock_pagetable_window_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root);
    assert(pagetable_perms_wf(post.pt_mp)) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root); pre.default_pagetable_wf_at(root); reveal(pagetable_hidden_leaves_only_when_locked);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at;
    };
    assert(pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    unlock_pagetable_window_eof_page_tables(pre, post, root, l4i, l3i, l2i);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        container_process_page_pagetable_wf_preserved_for_pagetable_fields();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
}
} // verus!

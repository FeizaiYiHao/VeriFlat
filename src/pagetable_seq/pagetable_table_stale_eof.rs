use vstd::prelude::*;
verus! {
use crate::*;

/// S of `KernelK::replace_table_stale_cpus`: only the table stale-CPU record of page table `root` moved; its lock state,
/// ghost slot, the rest of its big-lock payload, and so its mappings, held 4K and 2M leaves, root resolution, pages, and window
/// holders, every window half, and every other table stay.
#[verifier::opaque]
pub open spec fn table_stale_cpus_update_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot) -> bool {
    let before = pre.pt_mp.spec_index(root);
    let after = post.pt_mp.spec_index(root);
    let before_table = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
    let after_table = whole_pagetable(post.pt_mp, post.pt_lower.view(), root);
    &&& post == (KernelK { pt_mp: post.pt_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& after.is_init()
    &&& after.locking_thread() == before.locking_thread()
    &&& after.view_rodata() == before.view_rodata()
    &&& after.view_ghost() == before.view_ghost()
    &&& after.being_killed() == before.being_killed()
    &&& after.killer_info() == before.killer_info()
    &&& after.control() == before.control()
    &&& after.view() == (PageTableHigher { table_stale_cpus: after.view().table_stale_cpus, ..before.view() })
    &&& after_table.kernel_l4_end() == before_table.kernel_l4_end()
    &&& after_table.mapping_4k() == before_table.mapping_4k()
    &&& after_table.mapping_2m() == before_table.mapping_2m()
    &&& after_table.mapping_1g() == before_table.mapping_1g()
    &&& after_table.page_closure() == before_table.page_closure()
    &&& after_table.leaves_present() == before_table.leaves_present()
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger after_table.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger before_table.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        before_table.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> after_table.window_locked_by_thread(l4i, l3i, l2i, thread_id) == before_table.window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger after_table.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        after_table.spec_held_4k_l1(l4i, l3i, l2i, l1i) == before_table.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger after_table.spec_held_2m_l2(l4i, l3i, l2i)] after_table.spec_held_2m_l2(l4i, l3i, l2i) == before_table.spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index| #![trigger after_table.spec_resolve_mapping_l4(l4i)] after_table.spec_resolve_mapping_l4(l4i) == before_table.spec_resolve_mapping_l4(l4i)
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
        #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
        pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
}

/// EOF closure of `KernelK::replace_table_stale_cpus`: the table is write-held, so it may list CPUs; its roots, page
/// records, and process are unchanged; a `Set` only grows the record and a `RemoveCpu` drops a CPU that keeps nothing a
/// flush would remove, so the TLB and paging-structure invariants carry over.
pub(super) proof fn table_stale_cpus_update_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, update: TableStaleUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        table_stale_cpus_update_eof_transition_framing(pre, post, root),
        post.pt_mp.spec_index(root).view().table_stale_cpus.view() == table_stale_cpus_after(update, pre.pt_mp.spec_index(root).view().table_stale_cpus.view()),
        update is Set ==> pre.pt_mp.spec_index(root).view().table_stale_cpus.view().subset_of(update->Set_cpus),
        update is RemoveCpu ==> ({
            let cpu_id = update->RemoveCpu_cpu_id;
            let pcid = pre.pt_mp.spec_index(root).view().pcid->Some_0;
            &&& pre.pt_mp.spec_index(root).view().pcid is Some
            &&& index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            &&& pre.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
                || (pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
                || (pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != root)
                || single_cpu_single_pcid_tlb_subset_of_present_pagetable(pre.cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root))
        }),
        update is RemoveCpu ==> ({
            let cpu_id = update->RemoveCpu_cpu_id;
            let pcid = pre.pt_mp.spec_index(root).view().pcid->Some_0;
            let dirty_entry = pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
            ||| pre.cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
            ||| pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
            ||| dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != root
            ||| single_structure_cache_subset_of_present_pagetable(pre.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root))
        }),
    ensures
        post.inv(),
{
    table_stale_cpus_update_eof_tlb_wf(pre, post, root, update);
    table_stale_cpus_update_eof_structure_cache_wf(pre, post, root, update);
    reveal(table_stale_cpus_update_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    table_stale_cpus_update_eof_table_wf(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root), whole_pagetable(post.pt_mp, post.pt_lower.view(), root));
    assert(pagetable_perms_wf(post.pt_mp)) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
}

/// EOF closure of `KernelK::replace_table_stale_cpus` for the big-lock payload: no payload invariant reads the table record.
proof fn table_stale_cpus_update_eof_higher_inv(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        pre.inv(),
        post == (PageTableHigher { table_stale_cpus: post.table_stale_cpus, ..pre }),
    ensures
        post.inv(),
{
    assert(post.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
    assert(post.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
    assert(post.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
    assert(post.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
    assert(post.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); };
    assert(post.user_only()) by { reveal(PageTableHigher::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
    assert(post.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
    assert(post.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
}

/// EOF closure of `KernelK::replace_table_stale_cpus` for the table itself: no table invariant reads the table record.
proof fn table_stale_cpus_update_eof_table_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        pre.wf(),
        post.higher == (PageTableHigher { table_stale_cpus: post.higher.table_stale_cpus, ..pre.higher }),
        post.lower == pre.lower,
    ensures
        post.higher.inv(),
        post.wf(),
{
    table_stale_cpus_update_eof_higher_inv(pre.higher, post.higher);
    assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
    assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
    assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
    assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
    assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); };
    assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
    assert(post.user_only()) by { reveal(WholePageTable::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
}

/// EOF closure of `KernelK::replace_table_stale_cpus` for the TLB invariant: a `Set` keeps every listed CPU listed; a
/// `RemoveCpu` drops only `cpu_id`, whose TLB under the table's PCID is empty, exempt until its activation flush, recorded
/// under another table, or backed only by present leaves of the table.
proof fn table_stale_cpus_update_eof_tlb_wf(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, update: TableStaleUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        table_stale_cpus_update_eof_transition_framing(pre, post, root),
        post.pt_mp.spec_index(root).view().table_stale_cpus.view() == table_stale_cpus_after(update, pre.pt_mp.spec_index(root).view().table_stale_cpus.view()),
        update is Set ==> pre.pt_mp.spec_index(root).view().table_stale_cpus.view().subset_of(update->Set_cpus),
        update is RemoveCpu ==> ({
            let cpu_id = update->RemoveCpu_cpu_id;
            let pcid = pre.pt_mp.spec_index(root).view().pcid->Some_0;
            &&& pre.pt_mp.spec_index(root).view().pcid is Some
            &&& index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            &&& pre.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
                || (pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
                || (pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != root)
                || single_cpu_single_pcid_tlb_subset_of_present_pagetable(pre.cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root))
        }),
    ensures
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(table_stale_cpus_update_eof_transition_framing);
    reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match);
}

/// EOF closure of `KernelK::replace_table_stale_cpus` for the paging-structure invariant: a `Set` keeps every listed CPU
/// listed; a `RemoveCpu` drops only `cpu_id`, whose cached entries under the table's PCID are empty, exempt, kept for
/// another table, or live in this one.
proof fn table_stale_cpus_update_eof_structure_cache_wf(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, update: TableStaleUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        table_stale_cpus_update_eof_transition_framing(pre, post, root),
        post.pt_mp.spec_index(root).view().table_stale_cpus.view() == table_stale_cpus_after(update, pre.pt_mp.spec_index(root).view().table_stale_cpus.view()),
        update is Set ==> pre.pt_mp.spec_index(root).view().table_stale_cpus.view().subset_of(update->Set_cpus),
        update is RemoveCpu ==> ({
            let cpu_id = update->RemoveCpu_cpu_id;
            let pcid = pre.pt_mp.spec_index(root).view().pcid->Some_0;
            let dirty_entry = pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
            ||| pre.cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
            ||| pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
            ||| dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != root
            ||| single_structure_cache_subset_of_present_pagetable(pre.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root))
        }),
    ensures
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(table_stale_cpus_update_eof_transition_framing);
    reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match);
}
} // verus!

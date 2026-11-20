use vstd::prelude::*;
verus! {
use crate::*;
use vstd::{assert_seqs_equal, assert_seqs_equal_internal};

/// S of `KernelK::update_pci_entry`: only the PCI function array of page table `root` and the root table moved; the table's lock
/// state, ghost slot, the rest of its big-lock payload, every window half, and every other table stay.
/// `update_pci_entry_eof_tables_unchanged` derives that the table's mappings, held leaves, root resolution, pages, and window
/// holders stay; `update_pci_entry_eof_owner_update` states the root-table change.
#[verifier::opaque]
pub open spec fn update_pci_entry_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate) -> bool {
    let before = pre.pt_mp.spec_index(root);
    let after = post.pt_mp.spec_index(root);
    &&& post == (KernelK { irt: post.irt, pt_mp: post.pt_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& after.is_init()
    &&& after.locking_thread() == before.locking_thread()
    &&& after.view_rodata() == before.view_rodata()
    &&& after.view_ghost() == before.view_ghost()
    &&& after.being_killed() == before.being_killed()
    &&& after.killer_info() == before.killer_info()
    &&& after.control() == before.control()
    &&& after.view().higher == (PageTableHigher { pci: after.view().higher.pci, ..before.view().higher })
    &&& after.view().lower_backup == before.view().lower_backup
    &&& after.view().higher.pci.view() == pci_entry_update_view(before.view().higher.pci, index, update)
}

/// The tables of `KernelK::update_pci_entry`: no walk reads the PCI function array, so page table `root` keeps its mappings,
/// held leaves, root resolution, pages, and window holders, and every other table stays.
pub(super) proof fn update_pci_entry_eof_tables_unchanged(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires update_pci_entry_eof_transition_framing(pre, post, root, index, update),
    ensures
        ({
            let before_table = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root);
            let after_table = whole_pagetable(post.pt_mp, post.pt_lower.view(), root);
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
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger after_table.spec_held_1g_l3(l4i, l3i)] after_table.spec_held_1g_l3(l4i, l3i) == before_table.spec_held_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index| #![trigger after_table.spec_resolve_mapping_l4(l4i)] after_table.spec_resolve_mapping_l4(l4i) == before_table.spec_resolve_mapping_l4(l4i)
            &&& forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
                pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
        }),
{
    reveal(update_pci_entry_eof_transition_framing);
}

/// The root-table change of `KernelK::update_pci_entry`: only the owner of the updated function moved, to the table's process for
/// a `Claim` and to none for a `Release`; every context entry stays.
#[verifier::opaque]
pub open spec fn update_pci_entry_eof_owner_update(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate) -> bool {
    let before = pre.pt_mp.spec_index(root);
    let bdf = pci_entry_update_bdf(before.view().higher.pci, index, update);
    let owner = if update is Claim { Some(before.view().higher.proc_ptr) } else { None };
    &&& post.irt.view().table_base() == pre.irt.view().table_base()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.irt.view().iommu_dids() == pre.irt.view().iommu_dids()
    &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)]
        #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
        &&& post.irt.view().spec_index_owner(b, d, f) == if (b, d, f) == bdf { owner } else { pre.irt.view().spec_index_owner(b, d, f) }
        &&& post.irt.view().spec_index_iommu_root(b, d, f) == pre.irt.view().spec_index_iommu_root(b, d, f)
        &&& post.irt.view().spec_index_iommu_did(b, d, f) == pre.irt.view().spec_index_iommu_did(b, d, f)
    }
}

/// EOF closure of `KernelK::update_pci_entry` for the big-lock payload: only the PCI function array changed, and it stays well
/// formed.
proof fn update_pci_entry_eof_higher_inv(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        pre.inv(),
        post == (PageTableHigher { pci: post.pci, ..pre }),
        post.pci.wf(),
    ensures
        post.inv(),
{
    update_pci_entry_eof_entries(pre, post);
    update_pci_entry_eof_wf_l4(pre, post);
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

/// EOF closure of `KernelK::update_pci_entry` for `wf_l4`: the root entries read as before.
proof fn update_pci_entry_eof_wf_l4(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        pre.inv(),
        post == (PageTableHigher { pci: post.pci, ..pre }),
    ensures
        post.wf_l4(),
{
    update_pci_entry_eof_entries(pre, post);
    reveal(PageTableHigher::wf_l4);
}

/// EOF closure of `KernelK::update_pci_entry` for the root entries and the root and 1G walks, which do not read the PCI function
/// array: each reads as before.
proof fn update_pci_entry_eof_entries(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        post == (PageTableHigher { pci: post.pci, ..pre }),
    ensures
        forall|i: L4Index| #![trigger post.l4_entry(i)] post.l4_entry(i) == pre.l4_entry(i),
        forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)]
            post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
{}

/// EOF closure of `KernelK::update_pci_entry` for the table itself: no table invariant other than the payload's reads the PCI
/// function array.
proof fn update_pci_entry_eof_table_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        pre.wf(),
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.higher.pci.wf(),
        post.lower == pre.lower,
    ensures
        post.higher.inv(),
        post.wf(),
{
    update_pci_entry_eof_higher_inv(pre.higher, post.higher);
    assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
    assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
    assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
    assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
    update_pci_entry_eof_wf_mapping_4k(pre, post);
    update_pci_entry_eof_resolve_2m(pre, post);
    assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
    assert(post.user_only()) by { reveal(WholePageTable::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
}

/// EOF closure of `KernelK::update_pci_entry` for `wf_mapping_4k`: the leaves and mappings are unchanged.
proof fn update_pci_entry_eof_wf_mapping_4k(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        pre.wf(),
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.higher.pci.wf(),
        post.lower == pre.lower,
    ensures post.wf_mapping_4k(),
{
    update_pci_entry_eof_resolve_4k(pre, post);
    reveal(WholePageTable::wf_mapping_4k);
}

/// EOF closure of `KernelK::update_pci_entry` for the 4K walks, which do not read the PCI function array: each resolves as
/// before.
proof fn update_pci_entry_eof_resolve_4k(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.lower == pre.lower,
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
{}

/// EOF closure of `KernelK::update_pci_entry` for the 2M walks, which do not read the PCI function array: each resolves as
/// before.
proof fn update_pci_entry_eof_resolve_2m(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.lower == pre.lower,
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
{}

/// EOF closure of `KernelK::update_pci_entry` for the PCI mapping records: no leaf moved, a claimed entry records no mapping, and a
/// released entry recorded none or the table maps nothing.
proof fn update_pci_entry_eof_pci_mappings(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        post.irt.inv(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        post.pt_mp.spec_index(root).view().higher.pci.wf(),
        update is Claim ==> {
            let process = pre.prc_mp.spec_index(pre.pt_mp.spec_index(root).view().higher.proc_ptr).view();
            &&& !(process.state.view() is TablesEmptied)
            &&& !(process.state.view() is Zombie)
        },
        update is Release ==> pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).used,
        update is Release ==> pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).count == 0
            || whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k().dom() == Set::<VAddr>::empty()
            && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m().dom() == Set::<VAddr>::empty(),
        update matches PciEntryUpdate::Claim { bus, device, function } ==> !pre.pt_mp.spec_index(root).view().higher.pci.view().dom().contains((bus, device, function)),
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at, vstd::set::lemma_set_contains_len;
    update_pci_entry_eof_tables_unchanged(pre, post, root, index, update);
    reveal(update_pci_entry_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    update_pci_entry_eof_table_wf(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root), whole_pagetable(post.pt_mp, post.pt_lower.view(), root));
    if update is Release { pre.pt_mp.spec_index(root).view().higher.pci.wf_entry_at(index); }
    reveal(pagetable_pci_mappings_wf);
}

/// The page records of the page tables close after the transition.
proof fn update_pci_entry_eof_page_tables_page_mappings(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        post.irt.inv(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        post.pt_mp.spec_index(root).view().higher.pci.wf(),
    ensures page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(update_pci_entry_eof_transition_framing);
    update_pci_entry_eof_tables_unchanged(pre, post, root, index, update);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    update_pci_entry_eof_table_wf(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root), whole_pagetable(post.pt_mp, post.pt_lower.view(), root));
    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
}

/// The CPU TLBs stay covered by the page tables after the transition.
proof fn update_pci_entry_eof_page_tables_cpu_tlb(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        post.irt.inv(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        post.pt_mp.spec_index(root).view().higher.pci.wf(),
    ensures cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(update_pci_entry_eof_transition_framing);
    update_pci_entry_eof_tables_unchanged(pre, post, root, index, update);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    update_pci_entry_eof_table_wf(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root), whole_pagetable(post.pt_mp, post.pt_lower.view(), root));
    reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match);
}

/// The paging-structure caches stay covered by the page tables after the transition.
proof fn update_pci_entry_eof_page_tables_structure_cache(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        post.irt.inv(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        post.pt_mp.spec_index(root).view().higher.pci.wf(),
    ensures structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(update_pci_entry_eof_transition_framing);
    update_pci_entry_eof_tables_unchanged(pre, post, root, index, update);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    update_pci_entry_eof_table_wf(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root), whole_pagetable(post.pt_mp, post.pt_lower.view(), root));
    reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match);
}

/// EOF closure of `KernelK::update_pci_entry` for the page-table invariants: no leaf, held entry, table page, or process link
/// moved, and the array of a process whose tables were emptied stays empty.
proof fn update_pci_entry_eof_page_tables(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        post.irt.inv(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        post.pt_mp.spec_index(root).view().higher.pci.wf(),
        update is Claim ==> {
            let process = pre.prc_mp.spec_index(pre.pt_mp.spec_index(root).view().higher.proc_ptr).view();
            &&& !(process.state.view() is TablesEmptied)
            &&& !(process.state.view() is Zombie)
        },
        update is Release ==> pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).used,
        update is Release ==> pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).count == 0
            || whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k().dom() == Set::<VAddr>::empty()
            && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m().dom() == Set::<VAddr>::empty(),
        update matches PciEntryUpdate::Claim { bus, device, function } ==> !pre.pt_mp.spec_index(root).view().higher.pci.view().dom().contains((bus, device, function)),
    ensures
        post.subsystems_inv(),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp),
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    update_pci_entry_eof_tables_unchanged(pre, post, root, index, update);
    reveal(update_pci_entry_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), root);
    update_pci_entry_eof_table_wf(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root), whole_pagetable(post.pt_mp, post.pt_lower.view(), root));
    assert(pagetable_perms_wf(post.pt_mp)) by { lock_op_implies_pagetable_perms_wf_preserved_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_backup_wf); };
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { update_pci_entry_eof_page_tables_page_mappings(pre, post, root, index, update); };
    assert(pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view())) by { update_pci_entry_eof_pci_mappings(pre, post, root, index, update); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { update_pci_entry_eof_page_tables_cpu_tlb(pre, post, root, index, update); };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { update_pci_entry_eof_page_tables_structure_cache(pre, post, root, index, update); };
}

/// A function of the array of a page table whose process has no IOMMU table is detached: a present context entry would name
/// the function's owner, the table's process, and that process's IOMMU table.
pub(super) proof fn update_pci_entry_eof_released_function_detached(pre: KernelK, root: RwLockPageTableRoot, f: PciBdf)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        pre.pt_mp.spec_index(root).view().higher.pci.view().dom().contains(f),
        pre.prc_mp.spec_index(pre.pt_mp.spec_index(root).view().higher.proc_ptr).view().iommu_table is None,
    ensures
        pre.irt.view().spec_index_iommu_root(f.0, f.1, f.2) is None,
{
    pci_function_ownership_wf_pagetable_at(pre.irt.view(), pre.prc_mp, pre.pt_mp, root, f);
    assert(pre.irt.view().spec_index_iommu_root(f.0, f.1, f.2) is None) by { reveal(iommu_root_table_process_wf); };
}

/// EOF closure of `KernelK::update_pci_entry` for the root-table invariants: a claimed function was unowned, hence detached, and
/// a released one is detached, so no context entry or DID anchor changes its owner; the owner and the array of the updated
/// function move together.
proof fn update_pci_entry_eof_root_table(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        update_pci_entry_eof_owner_update(pre, post, root, index, update),
        post.irt.inv(),
        update matches PciEntryUpdate::Claim { bus, device, function } ==> pre.irt.view().spec_index_owner(bus, device, function) is None,
        update is Release ==> {
            let bdf = pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).bdf;
            &&& pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).used
            &&& pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is None
        },
    ensures
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
        pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp),
        iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
{
    broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at;
    reveal(update_pci_entry_eof_transition_framing);
    reveal(update_pci_entry_eof_owner_update);
    pagetable_perms_wf_at(pre.pt_mp, root);
    process_pagetable_wf_pagetable_at(pre.prc_mp, pre.pt_mp, root);
    match update {
        PciEntryUpdate::Claim { bus, device, function } => {
            assert(pre.irt.view().spec_index_iommu_root(bus, device, function) is None) by { reveal(iommu_root_table_process_wf); };
        },
        PciEntryUpdate::Release => {
            let bdf = pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).bdf;
            pre.pt_mp.spec_index(root).view().higher.pci.wf_entry_at(index);
            pci_function_ownership_wf_pagetable_at(pre.irt.view(), pre.prc_mp, pre.pt_mp, root, bdf);
        },
    }
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); reveal(process_pagetable_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); };
}

/// EOF closure of `KernelK::update_pci_entry`: every kernel invariant holds after the update.
pub(super) proof fn update_pci_entry_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        0 <= index < PCI_FUNCTIONS_PER_PROCESS,
        pre.pt_mp.spec_index(root).locking_thread() is Write,
        post.pt_mp.perms_wf(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        post.pt_mp.spec_index(root).view().higher.pci.wf(),
        post.irt.inv(),
        update_pci_entry_eof_owner_update(pre, post, root, index, update),
        update is Claim ==> {
            let process = pre.prc_mp.spec_index(pre.pt_mp.spec_index(root).view().higher.proc_ptr).view();
            &&& !(process.state.view() is TablesEmptied)
            &&& !(process.state.view() is Zombie)
        },
        update matches PciEntryUpdate::Claim { bus, device, function } ==> pre.irt.view().spec_index_owner(bus, device, function) is None,
        update matches PciEntryUpdate::Claim { bus, device, function } ==> !pre.pt_mp.spec_index(root).view().higher.pci.view().dom().contains((bus, device, function)),
        update is Release ==> {
            let bdf = pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).bdf;
            &&& pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).used
            &&& pre.pt_mp.spec_index(root).view().higher.pci.spec_entry(index).count == 0
                || whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k().dom() == Set::<VAddr>::empty()
                && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m().dom() == Set::<VAddr>::empty()
            &&& pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is None
        },
    ensures
        post.inv(),
{
    update_pci_entry_eof_page_tables(pre, post, root, index, update);
    update_pci_entry_eof_root_table(pre, post, root, index, update);
    reveal(update_pci_entry_eof_transition_framing);
    reveal(update_pci_entry_eof_owner_update);
    process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
}

/// EOL closure of the `KernelK::release_pci_functions` loop for the root-table owners: releasing `g` after the functions
/// `done` leaves the owners with `done` and `g` released.
pub(super) proof fn release_pci_functions_eol_owners(
    old_owners: Seq3<Option<RwLockProcessPtr>>, cur: Seq3<Option<RwLockProcessPtr>>, new: Seq3<Option<RwLockProcessPtr>>, done: Set<PciBdf>, g: PciBdf,
)
    requires
        pci_bdf_valid(g.0, g.1, g.2),
        done == Set::<PciBdf>::empty() ==> cur == old_owners,
        done != Set::<PciBdf>::empty() ==> cur == pci_owners_released(old_owners, done),
        new == seq3_update(cur, g.0 as int, g.1 as int, g.2 as int, None),
    ensures
        new == pci_owners_released(old_owners, done.insert(g)),
{
    let target = pci_owners_released(old_owners, done.insert(g));
    assert_seqs_equal!(new == target, b => {
        assert_seqs_equal!(new[b] == target[b], d => {
            assert_seqs_equal!(new[b][d] == target[b][d], f => {});
        });
    });
}
} // verus!

use vstd::prelude::*;
use crate::*;

verus! {
/// The owner of the mapped page `p_i` that carries the record `(pt_ptr, va)` is the container of that table's process or one
/// of its ancestors.
pub proof fn container_process_page_pagetable_wf_at(container_map: ContainerLockedMap, process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, page_array: PageLockedArray,
    p_i: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        container_process_page_pagetable_wf(container_map, process_map, pagetable_map, page_array),
        index_valid(NUM_PAGES, p_i),
        page_array.spec_index(p_i).view().view().is_mapped(),
        page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va)),
    ensures
        ({
            let proc_ptr = pagetable_map.spec_index(pt_ptr).view().proc_ptr;
            let page_owner = page_array.spec_index(p_i).view().view().owning_container;
            &&& pagetable_map.dom().contains(pt_ptr)
            &&& process_map.dom().contains(proc_ptr)
            &&& container_map.dom().contains(page_owner)
            &&& process_map.spec_index(proc_ptr).view_rodata().view().owning_container == page_owner
                || container_map.spec_index(page_owner).view_ghost().subtree_set.view().contains(process_map.spec_index(proc_ptr).view_rodata().view().owning_container)
        }),
{ reveal(container_process_page_pagetable_wf); }

/// A member `sub_c_ptr` of the subtree of container `c_ptr` lists `c_ptr` at `c_ptr`'s depth in its upper tree.
pub proof fn container_subtree_set_wf_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr)
    requires
        container_subtree_set_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
    ensures
        container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr) ==> {
            &&& container_perms.dom().contains(sub_c_ptr)
            &&& container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().len() > container_perms.spec_index(c_ptr).view_rodata().view().depth
            &&& container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth as int) == c_ptr
        },
{ reveal(container_subtree_set_wf); }

/// Clears the record `(pagetable, va)` of a held 4K leaf from the page `page_ptr`, which keeps other references or is an
/// I/O page, and clears that unresolvable leaf; every other held entry of the table and every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_held_4k_mapping_without_free_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == old_c.higher
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view().mappings() == old_page.view().mappings().remove((pagetable, va))
    &&& new_page.view().iommu_mappings() == old_page.view().iommu_mappings()
    &&& new_page.view().ref_count == old_page.view().ref_count - 1
    &&& new_page.view().state == if old_page.view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable }
    &&& old_page.view().ref_count > 1 ==> new_page.view() == (Page { mappings: new_page.view().mappings, ref_count: new_page.view().ref_count, ..old_page.view() })
    &&& old_page.view().ref_count == 1 ==> new_page.view() == (Page { state: PageState::Unavailable, mappings: new_page.view().mappings, ref_count: 0, perm_4k: new_page.view().perm_4k, ..old_page.view() })
        && new_page.view().perm_4k.view() is None
}

/// The page-table relations close after dropping the held, unresolvable 4K leaf `va` and its mapping record on `page_ptr`.
proof fn remove_held_4k_mapping_without_free_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_4k_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, page_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == page_ptr,
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().contains((pagetable, va)),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.subsystems_inv(),
    ensures
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(remove_held_4k_mapping_without_free_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, page_index);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
        assert(pre.pg_arr.spec_index(page_index).view().view().ref_count == 1 ==> pre.pg_arr.spec_index(page_index).view().view().iommu_mappings().len() == 0);
        reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf);
    };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
}

/// The memory-management invariant closes after dropping the held, unresolvable 4K leaf `va` and its mapping record on `page_ptr`.
proof fn remove_held_4k_mapping_without_free_eof_memory_management_inv(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_4k_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, page_ptr),
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().contains((pagetable, va)),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.subsystems_inv(),
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
    ensures post.memory_management_inv(),
{
    reveal(remove_held_4k_mapping_without_free_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_held_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_held_or_emptied); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

/// EOF closure of `remove_held_4k_mapping_without_free`: the held leaf `va` and its record leave together, the leaf left
/// `mapping_4k` with its root, and no CPU caches it because the table lists no CPU stale while its root does not resolve.
pub(super) proof fn remove_held_4k_mapping_without_free_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_4k_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, page_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == page_ptr,
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().contains((pagetable, va)),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_held_4k_mapping_without_free_eof_transition_framing);
    assert(index_valid(NUM_PAGES, page_ptr2page_index(page_ptr))) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by { reveal(page_array_wf); reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_held); };
    remove_held_4k_mapping_without_free_eof_page_tables(pre, post, pagetable, va, page_ptr);
    remove_held_4k_mapping_without_free_eof_memory_management_inv(pre, post, pagetable, va, page_ptr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(tlb_wf_spec); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Clears the record `(pagetable, va)` of a held 4K leaf from the page `page_ptr`, whose last mapping it was, returns the
/// page through its free-list node at `node_addr` to shard `cpu_id` of the owner's 4K allocator `allocator_ptr`, and credits
/// the thread's pending free quota at `depth`, and clears that unresolvable leaf; every other held entry of the table is
/// unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_last_held_4k_mapping_to_allocator_eof_transition_framing(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    let old_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == old_c.higher
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex|
        #![trigger pre.pg_arr.spec_index(i).view().view().state]
        #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index {
                PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            } else {
                pre.pg_arr.spec_index(i).view().view().state
            }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& (i != page_index ==> post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings())
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        mappings: Ghost(old_page.view().mappings().remove((pagetable, va))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
    })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_2m]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g
        }
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view() == (Thread { direct_free_quota_pending_4k: new_thread.view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: new_thread.view().indirect_free_quota_pending_4k, ..old_thread.view() })
    &&& new_counter == old_counter + 1
    &&& new_thread.view().free_quota_pending_4k_at_depth(depth) == new_counter
    &&& new_thread.view().direct_free_quota_pending_4k.view() == old_thread.view().direct_free_quota_pending_4k.view() + if depth == old_thread.view().container_depth { 1int } else { 0int }
    &&& new_thread.view().indirect_free_quota_pending_4k.view() == if depth < old_thread.view().container_depth { old_thread.view().indirect_free_quota_pending_4k.view().update(depth as int, new_counter) } else { old_thread.view().indirect_free_quota_pending_4k.view() }
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger post.thr_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger thread_effective_quota_1g(pre.thr_mp.spec_index(t))]
        #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g]
        #![trigger pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().direct_free_quota_pending_2m == pre.thr_mp.spec_index(t).view().direct_free_quota_pending_2m
            &&& post.thr_mp.spec_index(t).view().direct_free_quota_pending_1g == pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g
            &&& post.thr_mp.spec_index(t).view().indirect_free_quota_pending_2m == pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_2m
            &&& post.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g == pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g
        }
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& new_allocator.quota == old_allocator.quota
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, page_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.global_pool == old_allocator.global_pool
    &&& new_allocator.owning_container == old_allocator.owning_container
}

/// The process-management invariant closes after the thread is credited one pending free 4K quota at `depth`.
proof fn remove_last_held_4k_mapping_to_allocator_eof_process_management_inv(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_held_4k_mapping_to_allocator_eof_transition_framing(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(remove_last_held_4k_mapping_to_allocator_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
}

/// The page-table relations close after the last mapping of `page_ptr`, the held leaf `va`, is dropped and cleared.
proof fn remove_last_held_4k_mapping_to_allocator_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_held_4k_mapping_to_allocator_eof_transition_framing(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_4k_valid(va)
            &&& !old_c.mapping_4k().dom().contains(va)
            &&& old_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some
            &&& old_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == page_ptr
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.mappings().contains((pagetable, va))
        }),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.subsystems_inv(),
    ensures
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(remove_last_held_4k_mapping_to_allocator_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, page_index);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
}

/// The 4K allocator relations close after `page_ptr` enters shard `cpu_id` of the owner allocator's CPU cache.
proof fn remove_last_held_4k_mapping_to_allocator_eof_free_4k_pages(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        remove_last_held_4k_mapping_to_allocator_eof_transition_framing(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& page_ptr_valid(page_ptr)
            &&& old_page.state is Mapped4k
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
        }),
        post.subsystems_inv(),
    ensures
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
{
    reveal(remove_last_held_4k_mapping_to_allocator_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr);
    };
}

/// The page ownership relations close after `page_ptr` turns from a mapped page into a free page of the owner allocator.
proof fn remove_last_held_4k_mapping_to_allocator_eof_page_owners(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_held_4k_mapping_to_allocator_eof_transition_framing(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        post.subsystems_inv(),
    ensures
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(remove_last_held_4k_mapping_to_allocator_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

/// The allocator quota and kill-retire relations close after the freed page's quota unit moves to the thread's pending free
/// counter at the owner's `depth`.
proof fn remove_last_held_4k_mapping_to_allocator_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        remove_last_held_4k_mapping_to_allocator_eof_transition_framing(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_thread = pre.thr_mp.spec_index(thread_ptr);
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& pre.thr_mp.dom().contains(thread_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_4k_at_depth(depth)
        }),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(remove_last_held_4k_mapping_to_allocator_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(thread_perms_wf);
        lemma_thread_effective_quota_4k_fold_sum_eq_forall();
        lemma_thread_pending_4k_folds_change_by_forall(thread_ptr, if depth == pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int }, depth as int,
            if depth < pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int });
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        let thread = pre.thr_mp.spec_index(thread_ptr).view();
        container_thread_wf_at(pre.ctn_mp, pre.thr_mp, thread_ptr); container_thread_wf_uppertree_at(pre.ctn_mp, pre.thr_mp, thread_ptr);
        if depth < thread.container_depth {
            container_perms_wf_at(pre.ctn_mp, thread.owning_container); assert(thread.upper_container_seq.view().contains(owner));
            container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, thread.owning_container, owner);
        }
        reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
}

/// EOF closure of `remove_last_held_4k_mapping_to_allocator`: the held leaf `va` and its record leave together, the leaf left
/// `mapping_4k` with its root, so the freed page carries no other record and no CPU caches it, and the page's quota unit moves
/// to the thread's pending counter at the owner's depth.
pub(super) proof fn remove_last_held_4k_mapping_to_allocator_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_held_4k_mapping_to_allocator_eof_transition_framing(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            let old_thread = pre.thr_mp.spec_index(thread_ptr);
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_4k_valid(va)
            &&& old_c.spec_resolve_mapping_l4(spec_v2l4index(va)) is None
            &&& pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& !old_c.mapping_4k().dom().contains(va)
            &&& old_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some
            &&& old_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == page_ptr
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.thr_mp.dom().contains(thread_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_4k_at_depth(depth)
        }),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_last_held_4k_mapping_to_allocator_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(allocator_perms_wf); reveal(thread_ipc_transit_wf); reveal(KernelK::default_pagetable_wf);
        reveal(pagetable_table_stale_cpus_only_when_write_held);
    };
    remove_last_held_4k_mapping_to_allocator_eof_page_relations(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    remove_last_held_4k_mapping_to_allocator_eof_free_4k_pages(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr, owner);
    remove_last_held_4k_mapping_to_allocator_eof_page_owners(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    remove_last_held_4k_mapping_to_allocator_eof_allocator_quota_wf(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr, owner);
    assert(post.memory_management_inv()) by { reveal(pagetable_hidden_roots_only_when_write_held_or_emptied); };
    remove_last_held_4k_mapping_to_allocator_eof_process_management_inv(pre, post, pagetable, va, page_ptr, thread_ptr, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(tlb_wf_spec); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
    broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
}

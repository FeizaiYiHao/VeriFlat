use vstd::prelude::*;
use crate::*;

verus! {
/// Copies the 4K leaf `va` of `source_pagetable` into IOMMU table `iommu_table_ptr` at `iova` and records `(iommu_table_ptr, iova)`
/// on the shared page `pg_idx`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn map_shared_page_into_iommu_4k_eof_transition_framing(
    pre: KernelK, post: KernelK, pg_idx: PageIndex, source_pagetable: RwLockPageTableRoot, va: VAddr, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
) -> bool {
    let old_it = pre.it_mp.spec_index(iommu_table_ptr);
    let new_it = post.it_mp.spec_index(iommu_table_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    &&& post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, ..pre })
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr)
    &&& new_it.locking_thread() == old_it.locking_thread()
    &&& new_it.being_killed() == old_it.being_killed()
    &&& new_it.view().mapping_4k() == old_it.view().mapping_4k().insert(iova, whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va))
    &&& new_it.view().mapping_2m() == old_it.view().mapping_2m()
    &&& new_it.view().mapping_1g() == old_it.view().mapping_1g()
    &&& new_it.view().page_closure() == old_it.view().page_closure()
    &&& new_it.view().cr3 == old_it.view().cr3
    &&& new_it.view().proc_ptr == old_it.view().proc_ptr
    &&& new_it.view().did == old_it.view().did
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().iommu_mappings() == old_page.view().iommu_mappings().insert((iommu_table_ptr, iova))
    &&& new_page.view().mappings() == old_page.view().mappings()
    &&& new_page.view().ref_count == old_page.view().ref_count + 1
    &&& new_page.view().addr == old_page.view().addr
    &&& new_page.view().state == old_page.view().state
    &&& new_page.view().is_io_page == old_page.view().is_io_page
    &&& new_page.view().owning_container == old_page.view().owning_container
}

/// A `(it_ptr, iova)` record on the mapped page `p_i` names a 4K leaf of IOMMU table `it_ptr`.
pub(super) proof fn page_iommu_table_wf_page_at(
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray, p_i: PageIndex, it_ptr: RwLockPageTableRoot, iova: VAddr,
)
    requires
        page_iommu_table_wf(container_map, process_map, iommu_table_map, page_array),
        index_valid(NUM_PAGES, p_i),
        page_array.spec_index(p_i).view().view().is_mapped(),
    ensures
        page_array.spec_index(p_i).view().view().state is Mapped4k && page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova))
            ==> iommu_table_map.dom().contains(it_ptr) && iommu_table_map.spec_index(it_ptr).view().mapping_4k().contains_key(iova),
{ reveal(page_iommu_table_wf); }

pub(super) proof fn map_shared_page_into_iommu_4k_eof(
    pre: KernelK, post: KernelK, pg_idx: PageIndex, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, source_pagetable: RwLockPageTableRoot, va: VAddr,
    iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
)
    requires
        pre.inv(),
        map_shared_page_into_iommu_4k_eof_transition_framing(pre, post, pg_idx, source_pagetable, va, iommu_table_ptr, iova),
        pre.pt_mp.dom().contains(source_pagetable),
        pre.pt_mp.spec_index(source_pagetable).view().proc_ptr == prc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va),
        page_ptr_valid(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        pg_idx == page_ptr2page_index(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        index_valid(NUM_PAGES, pg_idx),
        pre.pg_arr.spec_index(pg_idx).view().view().state is Mapped4k,
        pre.it_mp.dom().contains(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == prc_ptr,
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        !pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
    ensures post.inv(),
{
    reveal(map_shared_page_into_iommu_4k_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
        };
        assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
            thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        map_shared_page_into_iommu_4k_eof_page_pagetable(pre, post, pg_idx, prc_ptr, thrd_ptr, source_pagetable, va, iommu_table_ptr, iova);
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        map_shared_page_into_iommu_4k_eof_page_iommu_table(pre, post, pg_idx, prc_ptr, thrd_ptr, source_pagetable, va, iommu_table_ptr, iova);
        assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
        assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
            reveal(process_emptied_tables_wf); reveal(process_iommu_table_wf); process_thread_wf_thread_at(pre.prc_mp, pre.thrd_mp, thrd_ptr);
            process_perms_wf_at(pre.prc_mp, prc_ptr); process_emptied_threads_wf_at(pre.prc_mp, pre.thrd_mp, prc_ptr, thrd_ptr);
        };
        assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
        assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
        assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
}

/// The `(iommu_table_ptr, iova)` record added to the shared page names the new 4K leaf, and every other record is unchanged.
proof fn map_shared_page_into_iommu_4k_eof_page_iommu_table(
    pre: KernelK, post: KernelK, pg_idx: PageIndex, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, source_pagetable: RwLockPageTableRoot, va: VAddr,
    iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
)
    requires
        pre.inv(),
        map_shared_page_into_iommu_4k_eof_transition_framing(pre, post, pg_idx, source_pagetable, va, iommu_table_ptr, iova),
        pre.pt_mp.dom().contains(source_pagetable),
        pre.pt_mp.spec_index(source_pagetable).view().proc_ptr == prc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va),
        page_ptr_valid(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        pg_idx == page_ptr2page_index(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        index_valid(NUM_PAGES, pg_idx),
        pre.pg_arr.spec_index(pg_idx).view().view().state is Mapped4k,
        pre.it_mp.dom().contains(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == prc_ptr,
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        !pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
    ensures page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
{
    reveal(map_shared_page_into_iommu_4k_eof_transition_framing);
    let entry = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va);
    assert({
        &&& entry.addr == page_index2page_ptr(pg_idx)
        &&& entry.owning_container.view() == pre.pg_arr.spec_index(pg_idx).view().view().owning_container
        &&& pre.pg_arr.spec_index(pg_idx).view().view().mappings().contains((source_pagetable, va))
    }) by { reveal(mapped_4k_page_pagetable_wf); page_ptr_roundtrip(); };
    assert({
        let owner = pre.pg_arr.spec_index(pg_idx).view().view().owning_container;
        &&& pre.ctn_mp.dom().contains(owner)
        &&& (pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == owner
            || pre.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container))
    }) by { reveal(container_process_page_pagetable_wf); };
    reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf);
}

/// Page-table mapping records of all pages are preserved, since only the IOMMU record set of `pg_idx` changed.
proof fn map_shared_page_into_iommu_4k_eof_page_pagetable(
    pre: KernelK, post: KernelK, pg_idx: PageIndex, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, source_pagetable: RwLockPageTableRoot, va: VAddr,
    iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
)
    requires
        pre.inv(),
        map_shared_page_into_iommu_4k_eof_transition_framing(pre, post, pg_idx, source_pagetable, va, iommu_table_ptr, iova),
        pre.pt_mp.dom().contains(source_pagetable),
        pre.pt_mp.spec_index(source_pagetable).view().proc_ptr == prc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va),
        page_ptr_valid(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        pg_idx == page_ptr2page_index(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        index_valid(NUM_PAGES, pg_idx),
        pre.pg_arr.spec_index(pg_idx).view().view().state is Mapped4k,
        pre.it_mp.dom().contains(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == prc_ptr,
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        !pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
    ensures page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_shared_page_into_iommu_4k_eof_transition_framing);
    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf);
}
}

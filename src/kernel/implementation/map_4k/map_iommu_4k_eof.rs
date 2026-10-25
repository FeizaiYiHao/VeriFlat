use vstd::prelude::*;
use crate::*;

verus! {
/// Copies the 4K leaf `va` of `source_pagetable` into IOMMU table `iommu_table_ptr` at `iova` and records `(iommu_table_ptr, iova)`
/// on the shared page `page_index`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn map_shared_page_into_iommu_4k_eof_transition_framing(
    pre: KernelK, post: KernelK, page_index: PageIndex, source_pagetable: RwLockPageTableRoot, va: VAddr, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
) -> bool {
    let old_it = pre.it_mp.spec_index(iommu_table_ptr);
    let new_it = post.it_mp.spec_index(iommu_table_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, ..pre })
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr)
    &&& new_it.locking_thread() == old_it.locking_thread()
    &&& new_it.being_killed() == old_it.being_killed()
    &&& new_it.view().mapping_4k() == old_it.view().mapping_4k().insert(iova, pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va))
    &&& new_it.view().mapping_2m() == old_it.view().mapping_2m()
    &&& new_it.view().mapping_1g() == old_it.view().mapping_1g()
    &&& new_it.view().page_closure() == old_it.view().page_closure()
    &&& new_it.view().cr3 == old_it.view().cr3
    &&& new_it.view().proc_ptr == old_it.view().proc_ptr
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
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
    pre: KernelK, post: KernelK, page_index: PageIndex, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, source_pagetable: RwLockPageTableRoot, va: VAddr,
    iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
)
    requires
        pre.inv(),
        map_shared_page_into_iommu_4k_eof_transition_framing(pre, post, page_index, source_pagetable, va, iommu_table_ptr, iova),
        pre.pt_mp.dom().contains(source_pagetable),
        pre.pt_mp.spec_index(source_pagetable).view().proc_ptr == process_ptr,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va),
        page_index == page_ptr2page_index(pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        page_ptr_valid(pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr),
        index_valid(NUM_PAGES, page_index),
        pre.pg_arr.spec_index(page_index).view().view().state is Mapped4k,
        pre.it_mp.dom().contains(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == process_ptr,
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        !pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        !thread_is_dangling(pre.thr_mp.spec_index(thread_ptr)),
        !pre.thr_mp.spec_index(thread_ptr).view_ghost().exited,
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
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr);
        };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
            let entry = pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va);
            assert({
                &&& entry.addr == page_index2page_ptr(page_index)
                &&& entry.owning_container.view() == pre.pg_arr.spec_index(page_index).view().view().owning_container
                &&& pre.pg_arr.spec_index(page_index).view().view().mappings().contains((source_pagetable, va))
            }) by { reveal(mapped_4k_page_pagetable_wf); page_ptr_roundtrip(); };
            assert({
                let owner = pre.pg_arr.spec_index(page_index).view().view().owning_container;
                &&& pre.ctn_mp.dom().contains(owner)
                &&& (pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == owner
                    || pre.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container))
            }) by { reveal(container_process_page_pagetable_wf); };
            reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf);
        };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by {
            reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); process_thread_wf_at(pre.prc_mp, pre.thr_mp, thread_ptr);
            process_perms_wf_at(pre.prc_mp, process_ptr); process_emptied_threads_wf_at(pre.prc_mp, pre.thr_mp, process_ptr, thread_ptr);
        };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
}
}

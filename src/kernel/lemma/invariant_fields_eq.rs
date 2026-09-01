use vstd::prelude::*;
use crate::*;

verus! {

/// Process fields read by ownership and page-table reference invariants.
/// Quotas, staging sets, tree fields, threads, and lock state are excluded.
pub open spec fn process_reference_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger pre.spec_index(p_ptr)]
        #![trigger post.spec_index(p_ptr)]
        pre.dom().contains(p_ptr) ==>
        {
            &&& post.spec_index(p_ptr).view_rodata()
                == pre.spec_index(p_ptr).view_rodata()
            &&& post.spec_index(p_ptr).view().pagetable
                == pre.spec_index(p_ptr).view().pagetable
            &&& post.spec_index(p_ptr).view().pcid
                == pre.spec_index(p_ptr).view().pcid
            &&& post.spec_index(p_ptr).view().iommu_table
                == pre.spec_index(p_ptr).view().iommu_table
            &&& post.spec_index(p_ptr).view().pci_function_ref_counter
                == pre.spec_index(p_ptr).view().pci_function_ref_counter
            &&& post.spec_index(p_ptr).view().owned_pci_functions
                == pre.spec_index(p_ptr).view().owned_pci_functions
        }
}

pub proof fn container_process_wf_preserved_for_process_reference_fields(
    container_map: ContainerLockedMap,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
)
    requires
        container_process_wf(container_map, pre),
        process_reference_fields_unchanged(pre, post),
    ensures
        container_process_wf(container_map, post),
{
    reveal(container_process_wf);
}

pub proof fn process_pagetable_match_preserved_for_process_reference_fields(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    pagetable_map: PageTableLockedMap,
)
    requires
        process_pagetable_match(pre, pagetable_map),
        process_reference_fields_unchanged(pre, post),
    ensures
        process_pagetable_match(post, pagetable_map),
{
    reveal(process_pagetable_match);
}

pub proof fn process_iommu_table_match_preserved_for_process_reference_fields(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    iommu_table_map: IommuTableLockedMap,
)
    requires
        process_iommu_table_match(pre, iommu_table_map),
        process_reference_fields_unchanged(pre, post),
    ensures
        process_iommu_table_match(post, iommu_table_map),
{
    reveal(process_iommu_table_match);
}

pub proof fn iommu_root_table_process_wf_preserved_for_process_reference_fields(
    root_table: &IommuRootTable,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    iommu_table_map: IommuTableLockedMap,
)
    requires
        iommu_root_table_process_wf(root_table, pre, iommu_table_map),
        process_reference_fields_unchanged(pre, post),
    ensures
        iommu_root_table_process_wf(root_table, post, iommu_table_map),
{
    reveal(iommu_root_table_process_wf);
}

pub proof fn iommu_tlb_wf_spec_preserved_for_process_reference_fields(
    iommu_tlb: IommuTLB,
    root_table: &IommuRootTable,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    iommu_table_map: IommuTableLockedMap,
)
    requires
        iommu_tlb_wf_spec(iommu_tlb, root_table, pre, iommu_table_map),
        process_reference_fields_unchanged(pre, post),
    ensures
        iommu_tlb_wf_spec(iommu_tlb, root_table, post, iommu_table_map),
{
    reveal(iommu_tlb_wf_spec);
}

pub proof fn process_pci_function_ownership_wf_preserved_for_process_reference_fields(
    root_table: &IommuRootTable,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
)
    requires
        process_pci_function_ownership_wf(root_table, pre),
        process_reference_fields_unchanged(pre, post),
    ensures
        process_pci_function_ownership_wf(root_table, post),
{
    reveal(process_pci_function_ownership_wf);
}

pub proof fn container_process_page_pagetable_wf_preserved_for_process_reference_fields(
    container_map: ContainerLockedMap,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    pagetable_map: PageTableLockedMap,
    page_array: PageLockedArray,
)
    requires
        container_process_page_pagetable_wf(
            container_map,
            pre,
            pagetable_map,
            page_array,
        ),
        process_pagetable_match(pre, pagetable_map),
        page_pagetable_wf(pagetable_map, page_array),
        process_reference_fields_unchanged(pre, post),
    ensures
        container_process_page_pagetable_wf(
            container_map,
            post,
            pagetable_map,
            page_array,
        ),
{
    reveal(container_process_page_pagetable_wf);
    reveal(process_pagetable_match);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
}

/// Allocator fields read by `allocator_free_page_ptrs_wf`. Quota, total,
/// owning container, and every lock owner are excluded.
pub open spec fn allocator_free_page_fields_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|a_ptr: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(a_ptr)]
        #![trigger post.spec_index(a_ptr)]
        pre.dom().contains(a_ptr) ==>
        {
            &&& post.spec_index(a_ptr).global_pool.view()
                == pre.spec_index(a_ptr).global_pool.view()
            &&& forall|cpu_id: CpuId|
                #![trigger pre.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                #![trigger post.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                index_valid(NUM_CPUS, cpu_id) ==>
                    post.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
                    == pre.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
        }
}

pub proof fn allocator_free_page_ptrs_wf_preserved_for_fields_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
)
    requires
        allocator_free_page_ptrs_wf(pre),
        allocator_free_page_fields_unchanged(pre, post),
    ensures
        allocator_free_page_ptrs_wf(post),
{
    reveal(allocator_free_page_ptrs_wf);
}

/// Union of process fields read by invariants that frame a `quota_4k` update.
/// The changed `quota_4k` field and lock state are deliberately excluded.
pub open spec fn process_quota_4k_framed_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger pre.spec_index(p_ptr)]
        #![trigger post.spec_index(p_ptr)]
        pre.dom().contains(p_ptr) ==>
        {
            &&& post.spec_index(p_ptr).view_rodata()
                == pre.spec_index(p_ptr).view_rodata()
            &&& post.spec_index(p_ptr).view().pagetable
                == pre.spec_index(p_ptr).view().pagetable
            &&& post.spec_index(p_ptr).view().pcid
                == pre.spec_index(p_ptr).view().pcid
            &&& post.spec_index(p_ptr).view().iommu_table
                == pre.spec_index(p_ptr).view().iommu_table
            &&& post.spec_index(p_ptr).view().pci_function_ref_counter
                == pre.spec_index(p_ptr).view().pci_function_ref_counter
            &&& post.spec_index(p_ptr).view().owned_pci_functions
                == pre.spec_index(p_ptr).view().owned_pci_functions
            &&& post.spec_index(p_ptr).view().parent_linkedlist_node
                == pre.spec_index(p_ptr).view().parent_linkedlist_node
            &&& post.spec_index(p_ptr).view().children
                == pre.spec_index(p_ptr).view().children
            &&& post.spec_index(p_ptr).view().uppertree_seq
                == pre.spec_index(p_ptr).view().uppertree_seq
            &&& post.spec_index(p_ptr).view().subtree_set
                == pre.spec_index(p_ptr).view().subtree_set
            &&& post.spec_index(p_ptr).view().owned_threads
                == pre.spec_index(p_ptr).view().owned_threads
        }
}

/// Union of allocator fields read by invariants that frame a quota-value
/// update. The changed quota value and all lock owners are excluded.
pub open spec fn allocator_quota_value_framed_fields_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|a_ptr: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(a_ptr)]
        #![trigger post.spec_index(a_ptr)]
        pre.dom().contains(a_ptr) ==>
        {
            &&& post.spec_index(a_ptr).owning_container
                == pre.spec_index(a_ptr).owning_container
            &&& post.spec_index(a_ptr).quota.view().container_depth
                == pre.spec_index(a_ptr).quota.view().container_depth
            &&& post.spec_index(a_ptr).global_pool.view()
                == pre.spec_index(a_ptr).global_pool.view()
            &&& forall|cpu_id: CpuId|
                #![trigger pre.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                #![trigger post.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                index_valid(NUM_CPUS, cpu_id) ==>
                    post.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
                    == pre.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
        }
}

pub proof fn lemma_no_change_imply_allocator_pages_wf_forall()
    ensures
        forall|page_array: PageLockedArray,
            pre: PageAllocatorUnLockedMap,
            post: PageAllocatorUnLockedMap,
            allocator_2m_map: PageAllocatorUnLockedMap,
            allocator_1g_map: PageAllocatorUnLockedMap|
            #![trigger
                allocator_pages_wf(
                    page_array,
                    pre,
                    allocator_2m_map,
                    allocator_1g_map,
                ),
                allocator_pages_wf(
                    page_array,
                    post,
                    allocator_2m_map,
                    allocator_1g_map,
                )
            ]
            allocator_pages_wf(
                page_array,
                pre,
                allocator_2m_map,
                allocator_1g_map,
            )
            && allocator_quota_value_framed_fields_unchanged(pre, post)
            ==> allocator_pages_wf(
                page_array,
                post,
                allocator_2m_map,
                allocator_1g_map,
            ),
{
    reveal(allocator_4k_pages_wf);
}

pub proof fn lemma_no_change_imply_process_pages_wf_forall()
    ensures
        forall|page_array: PageLockedArray, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger
                process_pages_wf(page_array, pre),
                process_pages_wf(page_array, post)
            ]
            process_pages_wf(page_array, pre)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_pages_wf(page_array, post),
{
    reveal(process_pages_wf);
}

pub proof fn lemma_no_change_imply_container_process_page_pagetable_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: ProcessLockedMap,
            post: ProcessLockedMap,
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray|
            #![trigger
                container_process_page_pagetable_wf(
                    container_map,
                    pre,
                    pagetable_map,
                    page_array,
                ),
                container_process_page_pagetable_wf(
                    container_map,
                    post,
                    pagetable_map,
                    page_array,
                )
            ]
            container_process_page_pagetable_wf(
                container_map,
                pre,
                pagetable_map,
                page_array,
            )
            && process_pagetable_match(pre, pagetable_map)
            && page_pagetable_wf(pagetable_map, page_array)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> container_process_page_pagetable_wf(
                container_map,
                post,
                pagetable_map,
                page_array,
            ),
{
    reveal(container_process_page_pagetable_wf);
    reveal(process_pagetable_match);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
}

pub proof fn lemma_no_change_imply_allocator_free_page_ptrs_wf_forall()
    ensures
        forall|pre: PageAllocatorUnLockedMap, post: PageAllocatorUnLockedMap|
            #![trigger
                allocator_free_page_ptrs_wf(pre),
                allocator_free_page_ptrs_wf(post)
            ]
            allocator_free_page_ptrs_wf(pre)
            && allocator_quota_value_framed_fields_unchanged(pre, post)
            ==> allocator_free_page_ptrs_wf(post),
{
    reveal(allocator_free_page_ptrs_wf);
}

pub proof fn lemma_no_change_imply_process_pagetable_match_forall()
    ensures
        forall|pre: ProcessLockedMap,
            post: ProcessLockedMap,
            pagetable_map: PageTableLockedMap|
            #![trigger
                process_pagetable_match(pre, pagetable_map),
                process_pagetable_match(post, pagetable_map)
            ]
            process_pagetable_match(pre, pagetable_map)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_pagetable_match(post, pagetable_map),
{
    reveal(process_pagetable_match);
}

pub proof fn lemma_no_change_imply_process_iommu_table_match_forall()
    ensures
        forall|pre: ProcessLockedMap,
            post: ProcessLockedMap,
            iommu_table_map: IommuTableLockedMap|
            #![trigger
                process_iommu_table_match(pre, iommu_table_map),
                process_iommu_table_match(post, iommu_table_map)
            ]
            process_iommu_table_match(pre, iommu_table_map)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_iommu_table_match(post, iommu_table_map),
{
    reveal(process_iommu_table_match);
}

pub proof fn lemma_no_change_imply_iommu_root_table_process_wf_forall()
    ensures
        forall|root_table: IommuRootTable,
            pre: ProcessLockedMap,
            post: ProcessLockedMap,
            iommu_table_map: IommuTableLockedMap|
            #![trigger
                iommu_root_table_process_wf(&root_table, pre, iommu_table_map),
                iommu_root_table_process_wf(&root_table, post, iommu_table_map)
            ]
            iommu_root_table_process_wf(&root_table, pre, iommu_table_map)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> iommu_root_table_process_wf(&root_table, post, iommu_table_map),
{
    reveal(iommu_root_table_process_wf);
}

pub proof fn lemma_no_change_imply_process_pci_function_ownership_wf_forall()
    ensures
        forall|root_table: IommuRootTable,
            pre: ProcessLockedMap,
            post: ProcessLockedMap|
            #![trigger
                process_pci_function_ownership_wf(&root_table, pre),
                process_pci_function_ownership_wf(&root_table, post)
            ]
            process_pci_function_ownership_wf(&root_table, pre)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_pci_function_ownership_wf(&root_table, post),
{
    reveal(process_pci_function_ownership_wf);
}

pub proof fn lemma_no_change_imply_iommu_tlb_wf_spec_forall()
    ensures
        forall|iommu_tlb: IommuTLB,
            root_table: IommuRootTable,
            pre: ProcessLockedMap,
            post: ProcessLockedMap,
            iommu_table_map: IommuTableLockedMap|
            #![trigger
                iommu_tlb_wf_spec(iommu_tlb, &root_table, pre, iommu_table_map),
                iommu_tlb_wf_spec(iommu_tlb, &root_table, post, iommu_table_map)
            ]
            iommu_tlb_wf_spec(iommu_tlb, &root_table, pre, iommu_table_map)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> iommu_tlb_wf_spec(iommu_tlb, &root_table, post, iommu_table_map),
{
    reveal(iommu_tlb_wf_spec);
}

pub proof fn lemma_no_change_imply_container_process_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: ProcessLockedMap,
            post: ProcessLockedMap|
            #![trigger
                container_process_wf(container_map, pre),
                container_process_wf(container_map, post)
            ]
            container_process_wf(container_map, pre)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> container_process_wf(container_map, post),
{
    reveal(container_process_wf);
}

pub proof fn lemma_no_change_imply_container_allocator_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: PageAllocatorUnLockedMap,
            post: PageAllocatorUnLockedMap,
            allocator_2m_map: PageAllocatorUnLockedMap,
            allocator_1g_map: PageAllocatorUnLockedMap|
            #![trigger
                container_allocator_wf(
                    container_map,
                    pre,
                    allocator_2m_map,
                    allocator_1g_map,
                ),
                container_allocator_wf(
                    container_map,
                    post,
                    allocator_2m_map,
                    allocator_1g_map,
                )
            ]
            container_allocator_wf(
                container_map,
                pre,
                allocator_2m_map,
                allocator_1g_map,
            )
            && allocator_quota_value_framed_fields_unchanged(pre, post)
            ==> container_allocator_wf(
                container_map,
                post,
                allocator_2m_map,
                allocator_1g_map,
            ),
{
    reveal(container_allocator_wf);
}

pub proof fn lemma_no_change_imply_thread_staged_pages_wf_forall()
    ensures
        forall|pre: ThreadLockedMap,
            post: ThreadLockedMap,
            page_array: PageLockedArray|
            #![trigger
                thread_staged_pages_wf(pre, page_array),
                thread_staged_pages_wf(post, page_array)
            ]
            thread_staged_pages_wf(pre, page_array)
            && thread_invariant_fields_unchanged(pre, post)
            ==> thread_staged_pages_wf(post, page_array),
{
    reveal(thread_staged_pages_4k_wf);
    reveal(thread_staged_pages_2m_wf);
    reveal(thread_staged_pages_1g_wf);
}

pub proof fn lemma_no_change_imply_per_container_process_tree_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: ProcessLockedMap,
            post: ProcessLockedMap|
            #![trigger
                per_container_process_tree_wf(container_map, pre),
                per_container_process_tree_wf(container_map, post)
            ]
            per_container_process_tree_wf(container_map, pre)
            && container_process_wf(container_map, pre)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> per_container_process_tree_wf(container_map, post),
{
    reveal(per_container_process_tree_wf);
    reveal(container_process_wf);
    process_no_change_to_tree_fields_imply_wf_forall();
}

pub proof fn lemma_no_change_imply_process_cpu_wf_forall()
    ensures
        forall|pre: ProcessLockedMap,
            post: ProcessLockedMap,
            cpu_array: CpuLockedArray|
            #![trigger
                process_cpu_wf(pre, cpu_array),
                process_cpu_wf(post, cpu_array)
            ]
            process_cpu_wf(pre, cpu_array)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_cpu_wf(post, cpu_array),
{
    reveal(process_cpu_wf);
}

pub proof fn lemma_no_change_imply_process_thread_wf_forall()
    ensures
        forall|pre: ProcessLockedMap,
            post: ProcessLockedMap,
            thread_map: ThreadLockedMap|
            #![trigger
                process_thread_wf(pre, thread_map),
                process_thread_wf(post, thread_map)
            ]
            process_thread_wf(pre, thread_map)
            && process_empty_thread_list_wlocked(post)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_thread_wf(post, thread_map),
{
    reveal(process_thread_wf);
}

pub proof fn lemma_no_change_imply_cpu_dirty_map_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: ProcessLockedMap,
            post: ProcessLockedMap,
            cpu_array: CpuLockedArray,
            cpu_tlb: CpuTLB,
            pagetable_map: PageTableLockedMap|
            #![trigger
                cpu_dirty_map_wf(
                    container_map,
                    pre,
                    cpu_array,
                    cpu_tlb,
                    pagetable_map,
                ),
                cpu_dirty_map_wf(
                    container_map,
                    post,
                    cpu_array,
                    cpu_tlb,
                    pagetable_map,
                )
            ]
            cpu_dirty_map_wf(
                container_map,
                pre,
                cpu_array,
                cpu_tlb,
                pagetable_map,
            )
            && process_cpu_wf(pre, cpu_array)
            && container_cpu_wf(container_map, cpu_array)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> cpu_dirty_map_wf(
                container_map,
                post,
                cpu_array,
                cpu_tlb,
                pagetable_map,
            ),
{
    reveal(cpu_dirty_map_contains_container_processes);
    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    reveal(cpu_dirty_map_proc_pcid_match);
    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    reveal(process_cpu_wf);
    reveal(container_cpu_wf);
}

}

use vstd::prelude::*;
use crate::*;

verus! {

/// Process fields read by ownership and page-table reference invariants.
/// Quotas, staging sets, tree fields, threads, and lock state are excluded.
#[verifier::opaque]
pub open spec fn process_reference_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
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
    reveal(process_reference_fields_unchanged);
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
    reveal(process_reference_fields_unchanged);
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
    reveal(process_reference_fields_unchanged);
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
    reveal(process_reference_fields_unchanged);
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
    reveal(process_reference_fields_unchanged);
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
    reveal(process_reference_fields_unchanged);
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
    reveal(process_reference_fields_unchanged);
    reveal(container_process_page_pagetable_wf);
    reveal(process_pagetable_match);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
}

/// Allocator fields read by `allocator_free_page_ptrs_wf`. Quota, total,
/// owning container, and every lock owner are excluded.
#[verifier::opaque]
pub open spec fn allocator_free_page_fields_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|a_ptr: RwLockPageAllocatorPtr|
        #![trigger post.spec_index(a_ptr)]
        pre.dom().contains(a_ptr) ==>
        {
            &&& post.spec_index(a_ptr).global_pool.view()
                == pre.spec_index(a_ptr).global_pool.view()
            &&& forall|cpu_id: CpuId|
                #![trigger post.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                cpu_id_valid(cpu_id) ==>
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
    reveal(allocator_free_page_fields_unchanged);
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
            &&& post.spec_index(p_ptr).view().temp_alloc_cache_4k
                == pre.spec_index(p_ptr).view().temp_alloc_cache_4k
            &&& post.spec_index(p_ptr).view().temp_alloc_cache_2m
                == pre.spec_index(p_ptr).view().temp_alloc_cache_2m
            &&& post.spec_index(p_ptr).view().temp_alloc_cache_1g
                == pre.spec_index(p_ptr).view().temp_alloc_cache_1g
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
                #![trigger post.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                cpu_id_valid(cpu_id) ==>
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
    assert forall|page_array: PageLockedArray,
        pre: PageAllocatorUnLockedMap,
        post: PageAllocatorUnLockedMap,
        allocator_2m_map: PageAllocatorUnLockedMap,
        allocator_1g_map: PageAllocatorUnLockedMap| #![auto]
        allocator_pages_wf(page_array, pre, allocator_2m_map, allocator_1g_map)
        && allocator_quota_value_framed_fields_unchanged(pre, post)
    implies
        allocator_pages_wf(page_array, post, allocator_2m_map, allocator_1g_map)
    by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(
            page_array,
            page_array,
            pre,
            post,
        );
    };
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
    assert forall|page_array: PageLockedArray, pre: ProcessLockedMap, post: ProcessLockedMap|
        #![auto]
        process_pages_wf(page_array, pre)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        process_pages_wf(page_array, post)
    by {
        process_pages_wf_preserved_for_page_state_eq(
            page_array,
            page_array,
            pre,
            post,
        );
    };
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
    assert forall|container_map: ContainerLockedMap,
        pre: ProcessLockedMap,
        post: ProcessLockedMap,
        pagetable_map: PageTableLockedMap,
        page_array: PageLockedArray| #![auto]
        container_process_page_pagetable_wf(
            container_map,
            pre,
            pagetable_map,
            page_array,
        )
        && process_pagetable_match(pre, pagetable_map)
        && page_pagetable_wf(pagetable_map, page_array)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        container_process_page_pagetable_wf(
            container_map,
            post,
            pagetable_map,
            page_array,
        )
    by {
        assert(process_reference_fields_unchanged(pre, post)) by {
            reveal(process_reference_fields_unchanged);
        };
        container_process_page_pagetable_wf_preserved_for_process_reference_fields(
            container_map,
            pre,
            post,
            pagetable_map,
            page_array,
        );
    };
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
    assert forall|pre: PageAllocatorUnLockedMap, post: PageAllocatorUnLockedMap| #![auto]
        allocator_free_page_ptrs_wf(pre)
        && allocator_quota_value_framed_fields_unchanged(pre, post)
    implies
        allocator_free_page_ptrs_wf(post)
    by {
        assert(allocator_free_page_fields_unchanged(pre, post)) by {
            reveal(allocator_free_page_fields_unchanged);
        };
        allocator_free_page_ptrs_wf_preserved_for_fields_unchanged(pre, post);
    };
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
    assert forall|pre: ProcessLockedMap,
        post: ProcessLockedMap,
        pagetable_map: PageTableLockedMap| #![auto]
        process_pagetable_match(pre, pagetable_map)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        process_pagetable_match(post, pagetable_map)
    by {
        assert(process_reference_fields_unchanged(pre, post)) by {
            reveal(process_reference_fields_unchanged);
        };
        process_pagetable_match_preserved_for_process_reference_fields(
            pre,
            post,
            pagetable_map,
        );
    };
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
    assert forall|container_map: ContainerLockedMap,
        pre: ProcessLockedMap,
        post: ProcessLockedMap| #![auto]
        container_process_wf(container_map, pre)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        container_process_wf(container_map, post)
    by {
        assert(process_reference_fields_unchanged(pre, post)) by {
            reveal(process_reference_fields_unchanged);
        };
        container_process_wf_preserved_for_process_reference_fields(
            container_map,
            pre,
            post,
        );
    };
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
    assert forall|container_map: ContainerLockedMap,
        pre: PageAllocatorUnLockedMap,
        post: PageAllocatorUnLockedMap,
        allocator_2m_map: PageAllocatorUnLockedMap,
        allocator_1g_map: PageAllocatorUnLockedMap| #![auto]
        container_allocator_wf(
            container_map,
            pre,
            allocator_2m_map,
            allocator_1g_map,
        )
        && allocator_quota_value_framed_fields_unchanged(pre, post)
    implies
        container_allocator_wf(
            container_map,
            post,
            allocator_2m_map,
            allocator_1g_map,
        )
    by {
        reveal(container_allocator_wf);
    };
}

pub proof fn lemma_no_change_imply_process_staged_pages_wf_forall()
    ensures
        forall|pre: ProcessLockedMap,
            post: ProcessLockedMap,
            page_array: PageLockedArray|
            #![trigger
                process_staged_pages_wf(pre, page_array),
                process_staged_pages_wf(post, page_array)
            ]
            process_staged_pages_wf(pre, page_array)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_staged_pages_wf(post, page_array),
{
    assert forall|pre: ProcessLockedMap,
        post: ProcessLockedMap,
        page_array: PageLockedArray| #![auto]
        process_staged_pages_wf(pre, page_array)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        process_staged_pages_wf(post, page_array)
    by {
        lemma_process_staged_pages_wf_preserved_for_view_eq(
            pre,
            post,
            page_array,
        );
    };
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
    assert forall|container_map: ContainerLockedMap,
        pre: ProcessLockedMap,
        post: ProcessLockedMap| #![auto]
        per_container_process_tree_wf(container_map, pre)
        && container_process_wf(container_map, pre)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        per_container_process_tree_wf(container_map, post)
    by {
        per_container_process_tree_wf_preserved_for_tree_fields_eq(
            container_map,
            pre,
            post,
        );
    };
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
    assert forall|pre: ProcessLockedMap,
        post: ProcessLockedMap,
        cpu_array: CpuLockedArray| #![auto]
        process_cpu_wf(pre, cpu_array)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        process_cpu_wf(post, cpu_array)
    by {
        reveal(process_cpu_wf);
    };
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
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_thread_wf(post, thread_map),
{
    assert forall|pre: ProcessLockedMap,
        post: ProcessLockedMap,
        thread_map: ThreadLockedMap| #![auto]
        process_thread_wf(pre, thread_map)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        process_thread_wf(post, thread_map)
    by {
        reveal(process_thread_wf);
    };
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
    assert forall|container_map: ContainerLockedMap,
        pre: ProcessLockedMap,
        post: ProcessLockedMap,
        cpu_array: CpuLockedArray,
        cpu_tlb: CpuTLB,
        pagetable_map: PageTableLockedMap| #![auto]
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
    implies
        cpu_dirty_map_wf(
            container_map,
            post,
            cpu_array,
            cpu_tlb,
            pagetable_map,
        )
    by {
        reveal(cpu_dirty_map_contains_container_processes);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(process_cpu_wf);
        reveal(container_cpu_wf);
    };
}

}

use vstd::prelude::*;
use crate::*;

verus! {

/// Installing one freshly initialized page-table page grows exactly one
/// page-table closure and retags the backing `Page` with that closure's root.
/// This is the structural counterpart of the nonstructural mmap framing lemma.
pub proof fn pagetable_pages_wf_preserved_for_page_table_page_insert(
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
)
    requires
        pagetable_pages_wf(pre_pagetable_map, pre_page_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().page_closure()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                .insert(page_ptr),
        post_page_array.entries_unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            is Owned4k,
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            == (PageState::Allocated4k {
                state: Allocated4KPageState::PageTable {
                    pagetable_root: pagetable_ptr,
                },
            }),
    ensures
        pagetable_pages_wf(post_pagetable_map, post_page_array),
{
    reveal(pagetable_pages_wf);
}

/// A page-table structure-only change leaves all abstract mappings untouched;
/// changing one nonmapped backing page therefore preserves the page/mapping
/// bidirectional invariant.
pub proof fn page_pagetable_wf_preserved_for_page_table_page_insert(
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
)
    requires
        page_pagetable_wf(pre_pagetable_map, pre_page_array),
        pagetable_perms_wf(post_pagetable_map),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
        post_page_array.entries_unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        !pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
        !post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
    ensures
        page_pagetable_wf(post_pagetable_map, post_page_array),
{
    reveal(pagetable_perms_wf);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
}

/// The ownership relation reads only mapped pages and the mapping page table's
/// `proc_ptr`; installing a nonmapped table page changes neither.
pub proof fn container_process_page_pagetable_wf_preserved_for_page_table_page_insert(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
)
    requires
        container_process_page_pagetable_wf(
            container_map,
            process_map,
            pre_pagetable_map,
            pre_page_array,
        ),
        page_pagetable_wf(post_pagetable_map, post_page_array),
        process_pagetable_match(process_map, post_pagetable_map),
        container_page_owner_wf(container_map, post_page_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
            == pre_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr,
        post_page_array.entries_unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        !pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
        !post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
    ensures
        container_process_page_pagetable_wf(
            container_map,
            process_map,
            post_pagetable_map,
            post_page_array,
        ),
{
    reveal(container_process_page_pagetable_wf);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
    reveal(process_pagetable_match);
    reveal(container_page_owner_wf);
}

/// Page-table structure is invisible to the abstract TLB relation.  If all
/// three abstract mapping maps are equal, every cached translation keeps the
/// same backing entry.
pub proof fn tlb_wf_spec_preserved_for_pagetable_mappings_unchanged(
    cpu_tlb: CpuTLB,
    cpu_array: CpuLockedArray,
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        tlb_wf_spec(cpu_tlb, pre_pagetable_map, cpu_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
    ensures
        tlb_wf_spec(cpu_tlb, post_pagetable_map, cpu_array),
{
    reveal(tlb_wf_spec);
}

/// Retagging one ordinary page as a CPU page-table page cannot affect the
/// disjoint IOMMU-table/page correspondence.
pub proof fn iommu_table_pages_wf_preserved_for_non_iommu_page_change(
    iommu_table_map: IommuTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    page_ptr: PagePtr,
)
    requires
        iommu_table_pages_wf(iommu_table_map, pre_page_array),
        page_ptr_valid(page_ptr),
        post_page_array.entries_unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        !(pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsIommuTableRoot,
            }),
        !(post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsIommuTableRoot,
            }),
        !(pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state is IOMMUTable),
        !(post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state is IOMMUTable),
    ensures
        iommu_table_pages_wf(iommu_table_map, post_page_array),
{
    reveal(iommu_table_pages_wf);
}

/// Consume one staged 4K page from exactly one thread.  Quota is deliberately
/// absent: `thread_staged_pages_4k_wf` reads only the cache and `Page::state`;
/// quota conservation is handled by its separate field-framing lemma.
pub proof fn thread_staged_pages_4k_wf_preserved_for_single_consume(
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    thread_ptr: RwLockThreadPtr,
    page_ptr: PagePtr,
)
    requires
        thread_staged_pages_4k_wf(pre_thread_map, pre_page_array),
        pre_thread_map.dom().contains(thread_ptr),
        page_ptr_valid(page_ptr),
        post_thread_map.unchanged_except(&pre_thread_map, thread_ptr),
        post_thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
            == pre_thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
                .view().remove(page_ptr),
        post_page_array.entries_unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            == (PageState::Owned4k { thread_ptr }),
        !(post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state is Owned4k),
    ensures
        thread_staged_pages_4k_wf(post_thread_map, post_page_array),
{
    reveal(thread_staged_pages_4k_wf);
}

}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {
// Framing-lemma family for the `*_pages_wf` bidirectional invariants. Each
// point-wise lemma preserves one invariant without leaving a quantified fact
// in the caller's context.

// container_pages_wf: Allocated2m{AsContainer} <-> container_map.dom().
pub proof fn container_pages_wf_preserved_for_page_state_eq(
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    old_container_map: ContainerLockedMap,
    new_container_map: ContainerLockedMap,
)
    requires
        container_pages_wf(old_page_array, old_container_map),
        new_container_map.dom() == old_container_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        container_pages_wf(new_page_array, new_container_map),
{
    reveal(container_pages_wf);
}

// process_pages_wf: Allocated4k{AsProcess} <-> process_map.dom().
pub proof fn process_pages_wf_preserved_for_page_state_eq(
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    old_process_map: ProcessLockedMap,
    new_process_map: ProcessLockedMap,
)
    requires
        process_pages_wf(old_page_array, old_process_map),
        new_process_map.dom() == old_process_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        process_pages_wf(new_page_array, new_process_map),
{
    reveal(process_pages_wf);
}

// thread_pages_wf: Allocated4k{AsThread} <-> thread_map.dom().
pub proof fn thread_pages_wf_preserved_for_page_state_eq(
    old_thread_map: ThreadLockedMap,
    new_thread_map: ThreadLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        thread_pages_wf(old_thread_map, old_page_array),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        thread_pages_wf(new_thread_map, new_page_array),
{
    reveal(thread_pages_wf);
}

// scheduler_pages_wf: Allocated4k{AsScheduler} <-> scheduler_map.dom().
pub proof fn scheduler_pages_wf_preserved_for_page_state_eq(
    old_scheduler_map: SchedulerLockedMap,
    new_scheduler_map: SchedulerLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        scheduler_pages_wf(old_scheduler_map, old_page_array),
        new_scheduler_map.dom() == old_scheduler_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state
                    matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsScheduler,
                    })
                || (new_page_array.spec_index(p_i).view().view().state
                    matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsScheduler,
                    }))
            ==> new_page_array.spec_index(p_i).view().view().state
                == old_page_array.spec_index(p_i).view().view().state,
    ensures
        scheduler_pages_wf(new_scheduler_map, new_page_array),
{
    reveal(scheduler_pages_wf);
}

// endpoint_pages_wf: Allocated4k{AsEndpoint} <-> endpoint_map.dom().
pub proof fn endpoint_pages_wf_preserved_for_page_state_eq(
    old_endpoint_map: EndpointLockedMap,
    new_endpoint_map: EndpointLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
)
    requires
        endpoint_pages_wf(old_endpoint_map, old_page_array),
        new_endpoint_map.dom() == old_endpoint_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        endpoint_pages_wf(new_endpoint_map, new_page_array),
{
    reveal(endpoint_pages_wf);
}

// pagetable_pages_wf: Allocated4k{AsPageTableRoot} and Allocated4k{PageTable} <-> pagetable_map roots and page closures.
pub proof fn pagetable_pages_wf_preserved_for_page_state_eq(
    old_pagetable_map: PageTableLockedMap, new_pagetable_map: PageTableLockedMap, old_page_array: PageLockedArray, new_page_array: PageLockedArray,
)
    requires
        pagetable_pages_wf(old_pagetable_map, old_page_array),
        new_pagetable_map.dom() == old_pagetable_map.dom(),
        forall|p: RwLockPageTableRoot| #![trigger new_pagetable_map.spec_index(p).view().page_closure()]
            new_pagetable_map.dom().contains(p) ==> new_pagetable_map.spec_index(p).view().page_closure() == old_pagetable_map.spec_index(p).view().page_closure(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot })
                || (old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::PageTable { .. } })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::PageTable { .. } }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        pagetable_pages_wf(new_pagetable_map, new_page_array),
{
    reveal(pagetable_pages_wf);
}

// iommu_table_pages_wf: Allocated4k{AsIommuTableRoot} and IOMMUTable <-> iommu_table_map roots and page closures.
pub proof fn iommu_table_pages_wf_preserved_for_page_state_eq(
    old_iommu_table_map: IommuTableLockedMap, new_iommu_table_map: IommuTableLockedMap, old_page_array: PageLockedArray, new_page_array: PageLockedArray,
)
    requires
        iommu_table_pages_wf(old_iommu_table_map, old_page_array),
        new_iommu_table_map.dom() == old_iommu_table_map.dom(),
        forall|p: RwLockPageTableRoot| #![trigger new_iommu_table_map.spec_index(p).view().page_closure()]
            new_iommu_table_map.dom().contains(p) ==> new_iommu_table_map.spec_index(p).view().page_closure() == old_iommu_table_map.spec_index(p).view().page_closure(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsIommuTableRoot })
                || (old_page_array.spec_index(p_i).view().view().state matches PageState::IOMMUTable { .. })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsIommuTableRoot })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::IOMMUTable { .. }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        iommu_table_pages_wf(new_iommu_table_map, new_page_array),
{
    reveal(iommu_table_pages_wf);
}

// allocator_4k_pages_wf: Allocated4k{As4KAllocator} <-> allocator_4k_map.dom().
pub proof fn allocator_4k_pages_wf_preserved_for_page_state_eq(
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    old_allocator_map: PageAllocatorUnLockedMap,
    new_allocator_map: PageAllocatorUnLockedMap,
)
    requires
        allocator_4k_pages_wf(old_page_array, old_allocator_map),
        new_allocator_map.dom() == old_allocator_map.dom(),
        forall|p_i: PageIndex|
            // #![trigger index_valid(NUM_PAGES, p_i)]
            #![trigger old_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        allocator_4k_pages_wf(new_page_array, new_allocator_map),
{
    reveal(allocator_4k_pages_wf);
}

// allocator_2m_pages_wf: Allocated4k{As2MAllocator} <-> allocator_2m_map.dom().
pub proof fn allocator_2m_pages_wf_preserved_for_page_state_eq(
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    old_allocator_map: PageAllocatorUnLockedMap,
    new_allocator_map: PageAllocatorUnLockedMap,
)
    requires
        allocator_2m_pages_wf(old_page_array, old_allocator_map),
        new_allocator_map.dom() == old_allocator_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            #![trigger old_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        allocator_2m_pages_wf(new_page_array, new_allocator_map),
{
    reveal(allocator_2m_pages_wf);
}

// allocator_1g_pages_wf: Allocated4k{As1GAllocator} <-> allocator_1g_map.dom().
pub proof fn allocator_1g_pages_wf_preserved_for_page_state_eq(
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    old_allocator_map: PageAllocatorUnLockedMap,
    new_allocator_map: PageAllocatorUnLockedMap,
)
    requires
        allocator_1g_pages_wf(old_page_array, old_allocator_map),
        new_allocator_map.dom() == old_allocator_map.dom(),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        allocator_1g_pages_wf(new_page_array, new_allocator_map),
{
    reveal(allocator_1g_pages_wf);
}
}

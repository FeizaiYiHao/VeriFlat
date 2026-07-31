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
            page_index_wf(p_i)
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
            page_index_wf(p_i)
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
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        thread_pages_wf(new_thread_map, new_page_array),
{
    reveal(thread_pages_wf);
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
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        endpoint_pages_wf(new_endpoint_map, new_page_array),
{
    reveal(endpoint_pages_wf);
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
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
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
            page_index_wf(p_i)
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
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state,
    ensures
        allocator_1g_pages_wf(new_page_array, new_allocator_map),
{
    reveal(allocator_1g_pages_wf);
}

}

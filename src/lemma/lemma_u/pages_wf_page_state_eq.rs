use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

// Framing-lemma family for the `*_pages_wf` bidirectional invariants (each binds
// a single page-state control-block class to a map's `dom()`). Reusable by ANY
// syscall — parameterized on (old, new), not tied to a particular mutation. Each
// says: if the map domain is unchanged AND every page slot that is in-class (in
// the OLD or NEW array) keeps its `state`, then the invariant is preserved. The
// state-eq hypothesis is scoped to in-class slots (the only ones both directions
// read), so a retype that moves a slot BETWEEN other classes (e.g. Free4k->Owned4k)
// leaves the read-set untouched. Each lemma keeps its predicate OPAQUE at the call
// site, so its deep forall no longer leaks into the surrounding proof block.
//
// Each predicate has TWO forms (mirror of `hugepage_page_state_eq`):
//   - `*_preserved_for_page_state_eq` (POINT-WISE, PREFER THIS): takes concrete
//     (old, new); proves exactly one instance and leaves NO quantifier in context.
//     Measurably cheaper at a call site -- stacking many `_forall`s bloats
//     E-matching (each leaves a standing `forall`), while point-wise calls compose
//     with no cross-interaction.
//   - `*_preserved_for_page_state_eq_forall`: installs the fact for ALL (old, new)
//     in one call; use only when a caller can't name the concrete pair.

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

pub proof fn container_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
            old_container_map: ContainerLockedMap,
            new_container_map: ContainerLockedMap,
        |
            #![trigger container_pages_wf(old_page_array, old_container_map), container_pages_wf(new_page_array, new_container_map)]
            (container_pages_wf(old_page_array, old_container_map)
            && new_container_map.dom() == old_container_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            container_pages_wf(new_page_array, new_container_map),
{
    assert forall|
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
        old_container_map: ContainerLockedMap,
        new_container_map: ContainerLockedMap,
    |
        (container_pages_wf(old_page_array, old_container_map)
        && new_container_map.dom() == old_container_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        container_pages_wf(new_page_array, new_container_map)
    by {
        container_pages_wf_preserved_for_page_state_eq(old_page_array, new_page_array, old_container_map, new_container_map);
    };
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

pub proof fn process_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
            old_process_map: ProcessLockedMap,
            new_process_map: ProcessLockedMap,
        |
            #![trigger process_pages_wf(old_page_array, old_process_map), process_pages_wf(new_page_array, new_process_map)]
            (process_pages_wf(old_page_array, old_process_map)
            && new_process_map.dom() == old_process_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            process_pages_wf(new_page_array, new_process_map),
{
    assert forall|
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
        old_process_map: ProcessLockedMap,
        new_process_map: ProcessLockedMap,
    |
        (process_pages_wf(old_page_array, old_process_map)
        && new_process_map.dom() == old_process_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        process_pages_wf(new_page_array, new_process_map)
    by {
        process_pages_wf_preserved_for_page_state_eq(old_page_array, new_page_array, old_process_map, new_process_map);
    };
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

pub proof fn thread_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_thread_map: ThreadLockedMap,
            new_thread_map: ThreadLockedMap,
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
        |
            #![trigger thread_pages_wf(old_thread_map, old_page_array), thread_pages_wf(new_thread_map, new_page_array)]
            (thread_pages_wf(old_thread_map, old_page_array)
            && new_thread_map.dom() == old_thread_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            thread_pages_wf(new_thread_map, new_page_array),
{
    assert forall|
        old_thread_map: ThreadLockedMap,
        new_thread_map: ThreadLockedMap,
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
    |
        (thread_pages_wf(old_thread_map, old_page_array)
        && new_thread_map.dom() == old_thread_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        thread_pages_wf(new_thread_map, new_page_array)
    by {
        thread_pages_wf_preserved_for_page_state_eq(old_thread_map, new_thread_map, old_page_array, new_page_array);
    };
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

pub proof fn endpoint_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_endpoint_map: EndpointLockedMap,
            new_endpoint_map: EndpointLockedMap,
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
        |
            #![trigger endpoint_pages_wf(old_endpoint_map, old_page_array), endpoint_pages_wf(new_endpoint_map, new_page_array)]
            (endpoint_pages_wf(old_endpoint_map, old_page_array)
            && new_endpoint_map.dom() == old_endpoint_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            endpoint_pages_wf(new_endpoint_map, new_page_array),
{
    assert forall|
        old_endpoint_map: EndpointLockedMap,
        new_endpoint_map: EndpointLockedMap,
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
    |
        (endpoint_pages_wf(old_endpoint_map, old_page_array)
        && new_endpoint_map.dom() == old_endpoint_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        endpoint_pages_wf(new_endpoint_map, new_page_array)
    by {
        endpoint_pages_wf_preserved_for_page_state_eq(old_endpoint_map, new_endpoint_map, old_page_array, new_page_array);
    };
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

pub proof fn allocator_4k_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
            old_allocator_map: PageAllocatorUnLockedMap,
            new_allocator_map: PageAllocatorUnLockedMap,
        |
            #![trigger allocator_4k_pages_wf(old_page_array, old_allocator_map), allocator_4k_pages_wf(new_page_array, new_allocator_map)]
            (allocator_4k_pages_wf(old_page_array, old_allocator_map)
            && new_allocator_map.dom() == old_allocator_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            allocator_4k_pages_wf(new_page_array, new_allocator_map),
{
    assert forall|
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
        old_allocator_map: PageAllocatorUnLockedMap,
        new_allocator_map: PageAllocatorUnLockedMap,
    |
        (allocator_4k_pages_wf(old_page_array, old_allocator_map)
        && new_allocator_map.dom() == old_allocator_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        allocator_4k_pages_wf(new_page_array, new_allocator_map)
    by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(old_page_array, new_page_array, old_allocator_map, new_allocator_map);
    };
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

pub proof fn allocator_2m_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
            old_allocator_map: PageAllocatorUnLockedMap,
            new_allocator_map: PageAllocatorUnLockedMap,
        |
            #![trigger allocator_2m_pages_wf(old_page_array, old_allocator_map), allocator_2m_pages_wf(new_page_array, new_allocator_map)]
            (allocator_2m_pages_wf(old_page_array, old_allocator_map)
            && new_allocator_map.dom() == old_allocator_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            allocator_2m_pages_wf(new_page_array, new_allocator_map),
{
    assert forall|
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
        old_allocator_map: PageAllocatorUnLockedMap,
        new_allocator_map: PageAllocatorUnLockedMap,
    |
        (allocator_2m_pages_wf(old_page_array, old_allocator_map)
        && new_allocator_map.dom() == old_allocator_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        allocator_2m_pages_wf(new_page_array, new_allocator_map)
    by {
        allocator_2m_pages_wf_preserved_for_page_state_eq(old_page_array, new_page_array, old_allocator_map, new_allocator_map);
    };
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

pub proof fn allocator_1g_pages_wf_preserved_for_page_state_eq_forall()
    ensures
        forall|
            old_page_array: PageLockedArray,
            new_page_array: PageLockedArray,
            old_allocator_map: PageAllocatorUnLockedMap,
            new_allocator_map: PageAllocatorUnLockedMap,
        |
            #![trigger allocator_1g_pages_wf(old_page_array, old_allocator_map), allocator_1g_pages_wf(new_page_array, new_allocator_map)]
            (allocator_1g_pages_wf(old_page_array, old_allocator_map)
            && new_allocator_map.dom() == old_allocator_map.dom()
            && forall|p_i: PageIndex|
                #![trigger new_page_array.spec_index(p_i).view().view().state]
                page_index_wf(p_i)
                && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
                    || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }))
                ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
            ==>
            allocator_1g_pages_wf(new_page_array, new_allocator_map),
{
    assert forall|
        old_page_array: PageLockedArray,
        new_page_array: PageLockedArray,
        old_allocator_map: PageAllocatorUnLockedMap,
        new_allocator_map: PageAllocatorUnLockedMap,
    |
        (allocator_1g_pages_wf(old_page_array, old_allocator_map)
        && new_allocator_map.dom() == old_allocator_map.dom()
        && forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i)
            && ((old_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
                || (new_page_array.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }))
            ==> new_page_array.spec_index(p_i).view().view().state == old_page_array.spec_index(p_i).view().view().state)
        implies
        allocator_1g_pages_wf(new_page_array, new_allocator_map)
    by {
        allocator_1g_pages_wf_preserved_for_page_state_eq(old_page_array, new_page_array, old_allocator_map, new_allocator_map);
    };
}

}

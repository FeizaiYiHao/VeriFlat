use vstd::prelude::*;
use crate::*;

verus! {
    /// Every kernel-object page belongs to the container that holds the object: a container page belongs to the container
    /// itself, the scheduler, CPU set, PCID allocator, and page allocator pages to the container naming them, and a thread
    /// or endpoint page to the container owning that object. An unavailable page and an I/O page belong to the root
    /// container, the one without a parent. A page staged in a thread's temp cache belongs to that thread's container, or
    /// to a live container write-locked by the lock thread that holds the staging thread.
    #[verifier::opaque]
    pub open spec fn page_object_owner_wf(page_array: PageLockedArray, container_map: ContainerLockedMap, thread_map: ThreadLockedMap) -> bool {
        forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = page_array.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                let container = container_map.spec_index(page.owning_container);
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }) ==> container.view_ghost().owned_threads.view().contains(ptr)
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }) ==> container.view_ghost().owned_endpoints.view().contains(ptr)
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }) ==> container.view_rodata().view().scheduler == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }) ==> container.view_rodata().view().cpu_set == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }) ==> container.view_rodata().view().allocator_ptr_4k == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }) ==> container.view_rodata().view().allocator_ptr_2m == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }) ==> container.view_rodata().view().allocator_ptr_1g == ptr
                &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }) ==> page.owning_container == ptr
                &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }) ==> container.view_rodata().view().pcid_allocator == ptr
                &&& page.state is Unavailable || page.is_io_page ==> container.view_rodata().view().parent is None
                &&& page.state is Owned4k || page.state is Owned2m || page.state is Owned1g ==> {
                    let thread_ptr = if page.state is Owned4k { page.state->Owned4k_thread_ptr } else if page.state is Owned2m { page.state->Owned2m_thread_ptr } else { page.state->Owned1g_thread_ptr };
                    let thread = thread_map.spec_index(thread_ptr);
                    &&& thread_map.dom().contains(thread_ptr)
                    &&& page.owning_container == thread.view().owning_container || container.locking_thread() is Write && thread.locking_thread() is Write
                        && container.locking_thread()->Write_thread_id == thread.locking_thread()->Write_thread_id && !container.being_killed()
                }
            }
    }

    pub proof fn page_object_owner_wf_at(page_array: PageLockedArray, container_map: ContainerLockedMap, thread_map: ThreadLockedMap, page_index: PageIndex)
        requires
            page_object_owner_wf(page_array, container_map, thread_map),
            index_valid(NUM_PAGES, page_index),
        ensures
            ({
                let page = page_array.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                let container = container_map.spec_index(page.owning_container);
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }) ==> container.view_ghost().owned_threads.view().contains(ptr)
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }) ==> container.view_ghost().owned_endpoints.view().contains(ptr)
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }) ==> container.view_rodata().view().scheduler == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }) ==> container.view_rodata().view().cpu_set == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }) ==> container.view_rodata().view().allocator_ptr_4k == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }) ==> container.view_rodata().view().allocator_ptr_2m == ptr
                &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }) ==> container.view_rodata().view().allocator_ptr_1g == ptr
                &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }) ==> page.owning_container == ptr
                &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }) ==> container.view_rodata().view().pcid_allocator == ptr
                &&& page.state is Unavailable || page.is_io_page ==> container.view_rodata().view().parent is None
                &&& page.state is Owned4k || page.state is Owned2m || page.state is Owned1g ==> {
                    let thread_ptr = if page.state is Owned4k { page.state->Owned4k_thread_ptr } else if page.state is Owned2m { page.state->Owned2m_thread_ptr } else { page.state->Owned1g_thread_ptr };
                    let thread = thread_map.spec_index(thread_ptr);
                    &&& thread_map.dom().contains(thread_ptr)
                    &&& page.owning_container == thread.view().owning_container || container.locking_thread() is Write && thread.locking_thread() is Write
                        && container.locking_thread()->Write_thread_id == thread.locking_thread()->Write_thread_id && !container.being_killed()
                }
            }),
    { reveal(page_object_owner_wf); }
}

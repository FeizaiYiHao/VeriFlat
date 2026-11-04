use vstd::prelude::*;
use crate::*;

verus! {
/// Every kernel-object page belongs to the container that holds the object: a container page belongs to the container
/// itself, the scheduler, CPU set, PCID allocator, and page allocator pages to the container naming them, and a thread
/// or endpoint page to the container owning that object. An unavailable page and an I/O page belong to the root
/// container, the one without a parent. A page staged in a thread's temp cache belongs to that thread's container, or
/// to a container not being killed that is write-locked by the same thread that write-locks the staging thread.
#[verifier::opaque]
pub open spec fn page_object_owner_wf(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().owning_container]
        index_valid(NUM_PAGES, p_i) ==> {
            let page = pg_arr.spec_index(p_i).view().view();
            let pg_ptr = page_index2page_ptr(p_i);
            let container = ctn_mp.spec_index(page.owning_container);
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }) ==> container.view_ghost().owned_threads.view().contains(pg_ptr)
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }) ==> container.view_ghost().owned_endpoints.view().contains(pg_ptr)
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }) ==> container.view_rodata().view().scheduler == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }) ==> container.view_rodata().view().cpu_set == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }) ==> container.view_rodata().view().allocator_ptr_4k == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }) ==> container.view_rodata().view().allocator_ptr_2m == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }) ==> container.view_rodata().view().allocator_ptr_1g == pg_ptr
            &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }) ==> page.owning_container == pg_ptr
            &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }) ==> container.view_rodata().view().pcid_allocator == pg_ptr
            &&& page.state is Unavailable || page.is_io_page ==> container.view_rodata().view().parent is None
            &&& page.state is Owned4k || page.state is Owned2m || page.state is Owned1g ==> {
                let thrd_ptr = if page.state is Owned4k { page.state->Owned4k_thread_ptr }
                    else if page.state is Owned2m { page.state->Owned2m_thread_ptr }
                    else { page.state->Owned1g_thread_ptr };
                let thread = thrd_mp.spec_index(thrd_ptr);
                &&& thrd_mp.dom().contains(thrd_ptr)
                &&& {
                    ||| page.owning_container == thread.view().owning_container
                    ||| {
                        &&& container.locking_thread() is Write
                        &&& thread.locking_thread() is Write
                        &&& container.locking_thread()->Write_thread_id == thread.locking_thread()->Write_thread_id
                        &&& !container.being_killed()
                    }
                }
            }
        }
}

pub proof fn page_object_owner_wf_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        page_object_owner_wf(ctn_mp, thrd_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let pg_ptr = page_index2page_ptr(pg_idx);
            let container = ctn_mp.spec_index(page.owning_container);
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }) ==> container.view_ghost().owned_threads.view().contains(pg_ptr)
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }) ==> container.view_ghost().owned_endpoints.view().contains(pg_ptr)
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }) ==> container.view_rodata().view().scheduler == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }) ==> container.view_rodata().view().cpu_set == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }) ==> container.view_rodata().view().allocator_ptr_4k == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }) ==> container.view_rodata().view().allocator_ptr_2m == pg_ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }) ==> container.view_rodata().view().allocator_ptr_1g == pg_ptr
            &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }) ==> page.owning_container == pg_ptr
            &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }) ==> container.view_rodata().view().pcid_allocator == pg_ptr
            &&& page.state is Unavailable || page.is_io_page ==> container.view_rodata().view().parent is None
            &&& page.state is Owned4k || page.state is Owned2m || page.state is Owned1g ==> {
                let thrd_ptr = if page.state is Owned4k { page.state->Owned4k_thread_ptr }
                    else if page.state is Owned2m { page.state->Owned2m_thread_ptr }
                    else { page.state->Owned1g_thread_ptr };
                let thread = thrd_mp.spec_index(thrd_ptr);
                &&& thrd_mp.dom().contains(thrd_ptr)
                &&& {
                    ||| page.owning_container == thread.view().owning_container
                    ||| {
                        &&& container.locking_thread() is Write
                        &&& thread.locking_thread() is Write
                        &&& container.locking_thread()->Write_thread_id == thread.locking_thread()->Write_thread_id
                        &&& !container.being_killed()
                    }
                }
            }
        }),
{ reveal(page_object_owner_wf); }
}

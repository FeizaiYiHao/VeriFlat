use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn thread_pages_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
        &&& forall|pg_idx:PageIndex|
            #![trigger page_array.spec_index(pg_idx)]
            #![trigger thread_map.dom().contains(page_index2page_ptr(pg_idx))]
            index_valid(NUM_PAGES, pg_idx) ==> { page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread} ==> thread_map.dom().contains(page_index2page_ptr(pg_idx)) }
        &&& forall|t_ptr:RwLockThreadPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(t_ptr))]
            #![trigger thread_map.dom().contains(t_ptr)]
            thread_map.dom().contains(t_ptr) ==> page_ptr_valid(t_ptr) && { page_array.spec_index(page_ptr2page_index(t_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread} }
    }

    /// Thread `t_ptr` sits on a valid page marked as a thread page.
    pub proof fn thread_pages_wf_at(thread_map: ThreadLockedMap, page_array: PageLockedArray, t_ptr: RwLockThreadPtr)
        requires
            thread_pages_wf(thread_map, page_array),
            thread_map.dom().contains(t_ptr),
        ensures
            page_ptr_valid(t_ptr),
            page_array.spec_index(page_ptr2page_index(t_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread},
    { reveal(thread_pages_wf); }

    /// Page `pg_ptr` is a thread only if it is a valid page marked as a thread page.
    pub proof fn thread_pages_wf_page_at(thread_map: ThreadLockedMap, page_array: PageLockedArray, pg_ptr: PagePtr)
        requires thread_pages_wf(thread_map, page_array),
        ensures thread_map.dom().contains(pg_ptr) ==> page_ptr_valid(pg_ptr) && (page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread}),
    { reveal(thread_pages_wf); }
}

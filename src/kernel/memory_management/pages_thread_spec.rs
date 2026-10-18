use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn thread_pages_wf(thread_map: ThreadLockedMap, page_array: PageLockedArray) -> bool {
        &&& forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger thread_map.dom().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) ==> { page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread} ==> thread_map.dom().contains(page_index2page_ptr(page_index)) }
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

    /// Page `page_ptr` is a thread only if it is a valid page marked as a thread page.
    pub proof fn thread_pages_wf_page_at(thread_map: ThreadLockedMap, page_array: PageLockedArray, page_ptr: PagePtr)
        requires thread_pages_wf(thread_map, page_array),
        ensures thread_map.dom().contains(page_ptr) ==> page_ptr_valid(page_ptr) && (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread}),
    { reveal(thread_pages_wf); }
}

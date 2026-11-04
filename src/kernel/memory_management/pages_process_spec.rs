use vstd::prelude::*;
use crate::*;

verus! {
    pub open spec fn process_pages_forward_wf(page_array: PageLockedArray, process_map: ProcessLockedMap) -> bool {
        forall|pg_idx:PageIndex|
            #![trigger page_array.spec_index(pg_idx).view().view().state]
            #![trigger process_map.dom().contains(page_index2page_ptr(pg_idx))]
            index_valid(NUM_PAGES, pg_idx) ==> { page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsProcess} ==> process_map.dom().contains(page_index2page_ptr(pg_idx)) }
    }

    pub open spec fn process_pages_backward_wf(page_array: PageLockedArray, process_map: ProcessLockedMap) -> bool {
        forall|c_ptr:RwLockContainerPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state]
            #![trigger process_map.dom().contains(c_ptr)]
            process_map.dom().contains(c_ptr) ==> page_ptr_valid(c_ptr) && { page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsProcess} }
    }

    #[verifier::opaque]
    pub open spec fn process_pages_wf(page_array: PageLockedArray, process_map: ProcessLockedMap) -> bool {
        &&& process_pages_forward_wf(page_array, process_map)
        &&& process_pages_backward_wf(page_array, process_map)
    }

    pub proof fn process_pages_wf_process_entry_at(page_array: PageLockedArray, process_map: ProcessLockedMap, proc_ptr: RwLockProcessPtr)
        requires
            process_pages_wf(page_array, process_map),
            process_map.dom().contains(proc_ptr),
        ensures
            page_ptr_valid(proc_ptr),
            page_array.spec_index(page_ptr2page_index(proc_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }),
    { reveal(process_pages_wf); }
}

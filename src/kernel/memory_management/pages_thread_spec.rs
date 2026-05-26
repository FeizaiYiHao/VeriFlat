use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub proof fn thread_pages_wf_proof()
            ensures 
                forall|thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>|
                    thread_pages_wf_inner(thread_map, page_array) <==> thread_pages_wf(thread_map, page_array)
        {}

        pub closed spec fn thread_pages_wf(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
            &&&
            thread_pages_wf_inner(thread_map, page_array)
        }

        pub open spec fn thread_pages_wf_inner(thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger thread_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            ==>
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread}
                ==>
                thread_map.dom().contains(page_index2page_ptr(page_index))
            }

            &&&
            forall|t_ptr:RwLockThreadPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(t_ptr))]
            #![trigger thread_map.dom().contains(t_ptr)]
            thread_map.dom().contains(t_ptr)
            ==>
            page_ptr_valid(t_ptr)
            &&
            {
                page_array.spec_index(page_ptr2page_index(t_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsThread}
            }

        }
}
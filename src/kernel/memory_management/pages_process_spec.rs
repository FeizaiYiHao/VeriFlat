use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub proof fn process_pages_wf_proof()
            ensures 
                forall|s:Self|
                s.process_pages_wf() <==> s.process_pages_wf_inner()
        {}

        pub closed spec fn process_pages_wf(&self) -> bool {
            &&&
            self.process_pages_wf_inner()
        }

        pub open spec fn process_pages_wf_inner(&self) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger self.page_array.spec_index(page_index)]
            #![trigger self.process_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            ==>
            self.page_array.spec_index(page_index).view().wlocked()
            ||
            {
                self.page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsProcess}
                ==>
                self.process_map.dom().contains(page_index2page_ptr(page_index))
            }

            &&&
            forall|c_ptr:RwLockContainerPtr|
            #![trigger self.page_array.spec_index(page_ptr2page_index(c_ptr))]
            #![trigger self.process_map.dom().contains(c_ptr)]
            self.process_map.dom().contains(c_ptr)
            ==>
            page_ptr_valid(c_ptr)
            &&
            {
                self.page_array.spec_index(page_ptr2page_index(c_ptr)).view().wlocked()
                ||
                self.page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsProcess}
            }

        }
    }
}
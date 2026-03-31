use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub proof fn container_pages_wf_proof()
            ensures 
                forall|s:Self|
                s.container_pages_wf() <==> s.container_pages_wf_inner()
        {}

        pub closed spec fn container_pages_wf(&self) -> bool {
            &&&
            self.container_pages_wf_inner()
        }

        pub open spec fn container_pages_wf_inner(&self) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger self.page_array.spec_index(page_index)]
            #![trigger self.container_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            ==>
            {
                self.page_array.spec_index(page_index).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer}
                ==>
                self.container_map.dom().contains(page_index2page_ptr(page_index))
            }

            &&&
            forall|c_ptr:RwLockContainerPtr|
            #![trigger self.page_array.spec_index(page_ptr2page_index(c_ptr))]
            #![trigger self.container_map.dom().contains(c_ptr)]
            self.container_map.dom().contains(c_ptr)
            ==>
            page_ptr_2m_valid(c_ptr)
            &&
            {
                self.page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer}
            }

        }
    }
}
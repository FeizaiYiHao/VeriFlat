use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub open spec fn container_pages_wf_inner(&self) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger self.page_array.spec_index(page_index).view().view().state]
            page_index_wf(page_index)
            ==>
            self.page_array.spec_index(page_index).view().locked()
            ||
            {
                self.page_array.spec_index(page_index).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer{container_ptr}}
                ==>
                self.container_map.dom().contains(container_ptr)
            }

        }
    }
}
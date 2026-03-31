use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub proof fn allocator_pages_wf_proof()
            ensures 
                forall|s:Self|
                s.allocator_pages_wf() <==> 
                {
                    &&&
                    s.allocator_4k_pages_wf_inner()
                    &&&
                    s.allocator_2m_pages_wf_inner()
                    &&&
                    s.allocator_1g_pages_wf_inner()
                }
        {}

        pub closed spec fn allocator_pages_wf(&self) -> bool {
            &&&
            self.allocator_4k_pages_wf_inner()
            &&&
            self.allocator_2m_pages_wf_inner()
            &&&
            self.allocator_1g_pages_wf_inner()
        }

        pub open spec fn allocator_4k_pages_wf_inner(&self) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger self.page_array.spec_index(page_index)]
            #![trigger self.allocator_4k_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            &&
            (self.page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator})
            ==>
            self.allocator_4k_map.dom().contains(page_index2page_ptr(page_index))

            &&&
            forall|a_ptr:RwLockPageAllocatorPtr|
            #![trigger self.page_array.spec_index(page_ptr2page_index(a_ptr))]
            #![trigger self.allocator_4k_map.dom().contains(a_ptr)]
            self.allocator_4k_map.dom().contains(a_ptr)
            ==>
            page_ptr_valid(a_ptr)
            &&
            self.page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator}
        }

        pub open spec fn allocator_2m_pages_wf_inner(&self) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger self.page_array.spec_index(page_index)]
            #![trigger self.allocator_2m_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            &&
            (self.page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator})
            ==>
            self.allocator_2m_map.dom().contains(page_index2page_ptr(page_index))

            &&&
            forall|a_ptr:RwLockPageAllocatorPtr|
            #![trigger self.page_array.spec_index(page_ptr2page_index(a_ptr))]
            #![trigger self.allocator_2m_map.dom().contains(a_ptr)]
            self.allocator_2m_map.dom().contains(a_ptr)
            ==>
            page_ptr_valid(a_ptr)
            &&
            self.page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator}

        }

        pub open spec fn allocator_1g_pages_wf_inner(&self) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger self.page_array.spec_index(page_index)]
            #![trigger self.allocator_1g_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            &&
            (self.page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator})
            ==>
            self.allocator_1g_map.dom().contains(page_index2page_ptr(page_index))

            &&&
            forall|a_ptr:RwLockPageAllocatorPtr|
            #![trigger self.page_array.spec_index(page_ptr2page_index(a_ptr))]
            #![trigger self.allocator_1g_map.dom().contains(a_ptr)]
            self.allocator_1g_map.dom().contains(a_ptr)
            ==>
            page_ptr_valid(a_ptr)
            &&
            self.page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator}

        }
    }
}
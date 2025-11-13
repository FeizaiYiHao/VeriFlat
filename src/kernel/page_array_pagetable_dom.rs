use vstd::prelude::*;
use crate::define::{PageIndex, PageTableRoot, VAddr};
use crate::page_array::spec::PageArray;
use crate::pagetable_dom::spec::PageTableDom;
use crate::primitive::lock_manager::{self, LockManager};
use crate::util::page_ptr_util_u::{page_index2page_ptr, page_index_valid, spec_page_index2page_ptr};

use super::define::Kernel;
verus! {

    impl Kernel{
        pub open spec fn page_array_pagetable_dom_inv(&self) -> bool{
            &&&
            true
        }

        // pub open spec fn page_array_mapping_infer_pagetable_exist(&self, page_index: PageIndex) -> bool
        //     recommends
        //         page_index_valid(page_index),
        //         self.subsystems_inv(),
        // {
        //     forall|
        // }
        pub open spec fn page_array_pagetable_dom_inv1(&self) -> bool{
            &&&
            forall|p_i:PageIndex, mapping: (PageTableRoot, VAddr)|
                #![auto]
                page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings@.contains(mapping)
                ==>{
                    self.pagetable_dom.dom().contains(mapping.0)
                }
        }

        pub open spec fn page_array_pagetable_dom_inv2(&self) -> bool{
            &&&
            forall|p_i:PageIndex, mapping: (PageTableRoot, VAddr)|
                #![auto]
                page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings@.contains(mapping)
                ==>{
                    (self.pagetable_dom[mapping.0]@.mapping_4k().contains_key(mapping.1) && self.pagetable_dom[mapping.0]@.mapping_4k()[mapping.1].addr == page_index2page_ptr(p_i))
                }
        }


    }

    

}
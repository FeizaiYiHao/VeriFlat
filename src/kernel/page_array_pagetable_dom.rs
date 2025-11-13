use vstd::prelude::*;
use crate::define::{PageIndex, PageTableRoot, VAddr};
use crate::page_array::page_array_define_spec::*;
use crate::pagetable_dom::pagetable_dom_define_spec::*;
use crate::primitive::lock_manager::{self, LockManager};
use crate::primitive::write_locked_by_same_thread;
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

        #[verifier(external_body)]
        pub proof fn page_array_pagetable_dom_inv1_open(&self)
            ensures 
                forall|p_i:PageIndex, mapping: (PageTableRoot, VAddr)|
                    #![auto]
                    page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings_4k@.contains(mapping)
                    ==>{
                        self.page_array@[p_i as int].modified() == false
                        ==>
                        self.pagetable_dom.dom().contains(mapping.0)
                    },
        {
        }

        pub open spec fn page_array_pagetable_dom_inv1(&self) -> bool{
            &&&
            forall|p_i:PageIndex, mapping: (PageTableRoot, VAddr)|
                #![auto]
                page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings_4k@.contains(mapping)
                ==>{
                    |||
                    self.page_array@[p_i as int].writing_thread() is Some
                    |||
                    self.pagetable_dom.dom().contains(mapping.0)
                }
        }

        pub open spec fn page_array_pagetable_dom_inv2(&self) -> bool{
            &&&
            forall|p_i:PageIndex, mapping: (PageTableRoot, VAddr)|
                #![auto]
                page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings_4k@.contains(mapping)
                ==>{
                    |||
                    write_locked_by_same_thread(self.page_array@[p_i as int], self.pagetable_dom[mapping.0])
                    |||
                    (self.pagetable_dom[mapping.0]@.mapping_4k().contains_key(mapping.1) && self.pagetable_dom[mapping.0]@.mapping_4k()[mapping.1].addr == page_index2page_ptr(p_i))
                }
        }

        pub open spec fn pagetable_dom_page_array_inv1(&self) -> bool{
            &&&
            forall|pt_r:PageTableRoot, va:VAddr|
                #![auto]
                self.pagetable_dom.dom().contains(pt_r)
                ==>{
                    |||
                    write_locked_by_same_thread(self.page_array@[self.pagetable_dom[pt_r]@.mapping_4k()[va].addr as int], self.pagetable_dom[pt_r])
                    |||
                    (self.page_array@[self.pagetable_dom[pt_r]@.mapping_4k()[va].addr as int]@.mappings_4k@.contains((pt_r, va)))
                }
        }


    }

    

}
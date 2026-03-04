use vstd::prelude::*;
use crate::define::*;
use crate::page_array::*;
use crate::pagetable_map::*;
use crate::primitive::*;
use crate::util::page_ptr_util_u::*;
use crate::locks::*;

use super::kernel_define_spec::Kernel;
verus! {

    impl Kernel{
        pub open spec fn page_array_pagetable_dom_inv(&self) -> bool{
            &&&
            self.page_array_pagetable_dom_inv1()
            &&&
            self.page_array_pagetable_dom_inv2()
            &&&
            self.pagetable_dom_page_array_inv1()
            &&&
            self.pagetable_dom_page_array_inv2()
        }

        // #[verifier(external_body)]
        // pub proof fn page_array_pagetable_dom_inv1_open(&self)
        //     ensures 
        //         forall|p_i:PageIndex, mapping: (RwLockPageTableRoot, VAddr)|
        //             #![auto]
        //             page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings_4k@.contains(mapping)
        //             ==>{
        //                 |||
        //                 self.page_array@[p_i as int].wlocked()
        //                 |||
        //                 self.pagetable_dom.dom().contains(mapping.0)
        //             },
        // {
        // }

        pub open spec fn page_array_pagetable_dom_inv1(&self) -> bool{
            &&&
            forall|p_i:PageIndex, pt_r: RwLockPageTableRoot, va: VAddr|
                #![trigger self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))]
                page_index_valid(p_i) && self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))
                ==>{
                    |||
                    self.page_array[p_i]@.locking_thread() is Write
                    |||
                    self.pagetable_dom.dom().contains(pt_r)
                }
        }

        pub open spec fn page_array_pagetable_dom_inv2(&self) -> bool{
            &&&
            forall|p_i:PageIndex, pt_r: RwLockPageTableRoot, va: VAddr|
                #![auto]
                page_index_valid(p_i) && self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))
                ==>
                {
                    |||
                    write_locked_by_same_thread(self.page_array[p_i]@, self.pagetable_dom[pt_r])
                    |||
                    (self.pagetable_dom[pt_r]@.mapping_4k().contains_key(va) && self.pagetable_dom[pt_r]@.mapping_4k()[va].addr == page_index2page_ptr(p_i))
                }
        }

        pub open spec fn pagetable_dom_page_array_inv1(&self) -> bool{
            &&&
            forall|pt_r:RwLockPageTableRoot, va:VAddr|
                #![trigger self.pagetable_dom[pt_r]@.mapping_4k().contains_key(va)]
                #![trigger self.pagetable_dom[pt_r]@.mapping_4k()[va]]
                self.pagetable_dom.dom().contains(pt_r) && self.pagetable_dom[pt_r]@.mapping_4k().contains_key(va)
                ==>{
                    // |||
                    // self.pagetable_dom[pt_r].locking_thread() is Write
                    |||
                    page_ptr_valid(self.pagetable_dom[pt_r]@.mapping_4k()[va].addr)
                }
        }

        pub open spec fn pagetable_dom_page_array_inv2(&self) -> bool{
            &&&
            forall|pt_r:RwLockPageTableRoot, va:VAddr|
                #![trigger self.pagetable_dom[pt_r]@.mapping_4k().contains_key(va)]
                #![trigger self.pagetable_dom[pt_r]@.mapping_4k()[va]]
                self.pagetable_dom.dom().contains(pt_r) && self.pagetable_dom[pt_r]@.mapping_4k().contains_key(va)
                ==>{
                    |||
                    write_locked_by_same_thread(self.page_array[page_ptr2page_index(self.pagetable_dom[pt_r]@.mapping_4k()[va].addr)]@, self.pagetable_dom[pt_r])
                    |||
                    self.page_array[page_ptr2page_index(self.pagetable_dom[pt_r]@.mapping_4k()[va].addr)]@@.mappings_4k@.contains((pt_r, va))
                }
        }


    }

    

}
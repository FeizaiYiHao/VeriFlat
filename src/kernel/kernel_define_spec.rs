use vstd::prelude::*;
use crate::page_array::page_array_define_spec::*;
use crate::pagetable_dom::pagetable_dom_define_spec::*;
verus! {

    pub struct Kernel{
        pub pagetable_dom: PageTableDom,
        pub page_array: PageArray,
    }

    impl Kernel{
        pub open spec fn subsystems_inv(&self) -> bool {
            &&&
            self.page_array.inv()
            &&&
            self.pagetable_dom.inv()
        }

        pub open spec fn inv(&self) -> bool {
            &&&
            self.subsystems_inv()
            &&&
            self.page_array_pagetable_dom_inv()
        }
    }

}
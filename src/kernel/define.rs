use vstd::prelude::*;
use crate::page_array::spec::PageArray;
use crate::pagetable_dom::spec::PageTableDom;
verus! {

    pub struct Kernel{
        pub pagetable_dom: PageTableDom,
        pub page_array: PageArray,
    }

    impl Kernel{
        pub open spec fn subsystems_inv(&self) -> bool{
            &&&
            self.page_array.inv()
            &&&
            self.pagetable_dom.inv()
        }
    }

}
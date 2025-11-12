use vstd::prelude::*;
use crate::page_array::spec::PageArray;
use crate::pagetable_dom::spec::PageTableDom;
verus! {

    pub struct Kernel{
        pub pagetable_dom: PageTableDom,
        pub page_array: PageArray,
    }

    

}
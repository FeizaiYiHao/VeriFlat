use vstd::prelude::*;
use crate::define::*;
verus! {

pub open spec fn page_index_wf(page_index: PageIndex) -> bool{
    0<=page_index<NUM_PAGES
}
    
}
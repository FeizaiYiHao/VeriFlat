use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::pagetable_seq::pagetable_spec::*;
use crate::primitive::*;
verus! {

pub type PageTablePerm = PointsTo<PageTable>;
pub struct PageTableLocked{
    pub perm: PageTablePerm,
}

impl PageTableLocked{
    
}


}
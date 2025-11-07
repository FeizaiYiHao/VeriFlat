use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::define::*;
use crate::pagetable_seq::pagetable_spec::*;
use crate::primitive::*;
verus! {

pub type PageTablePerm = PointsTo<PageTable>;
pub struct PageTableLocked{
    pub perm: PageTablePerm,
}

impl PageTableLocked{
    pub open spec fn lock_id(&self) -> LockId{
        LockId{
            major: PAGE_TABLE_LOCK_MAJOR,
            minor: self.perm.value().cr3,
        }
    }
    // pub fn read_lock(&mut self, &mut LockManager) -> Read
}


}
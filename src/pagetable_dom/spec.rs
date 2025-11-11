use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::define::*;
use crate::pagetable_seq::pagetable_spec::*;
use crate::primitive::*;
verus! {

pub struct PageTableDom{
    pub map: Tracked<Map<RwLockPageTableRoot, PointsTo<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>>>
}

impl PageTableDom {
    pub open spec fn inv(&self) -> bool {
        &&&
        true
    }

    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|rw_pt_root:RwLockPageTableRoot| 
            #![auto]
            self.map@.dom().contains(rw_pt_root)
            ==>
            {
                &&&
                self.map@[rw_pt_root].addr() == rw_pt_root
                &&&
                self.map@[rw_pt_root].value().inv()
            }
    }

    pub proof fn page_table_dom_lock_id_axiom(&self)
        requires 
            self.perms_wf(),
        ensures
            forall|rw_pt_root:RwLockPageTableRoot| 
                #![auto]
                self.map@.dom().contains(rw_pt_root)
                ==>
                {
                    &&&
                    self.map@[rw_pt_root].value().lock_minor() == self.map@[rw_pt_root].value()@.cr3
                }
    {
        admit()
    }
}

}
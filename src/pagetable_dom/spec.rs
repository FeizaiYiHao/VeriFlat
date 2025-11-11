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
        self.perms_wf()
    }

    pub open spec fn dom(&self) -> Set<RwLockPageTableRoot>{
        self.map@.dom()
    }

    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|rw_pt_root:RwLockPageTableRoot| 
            #![auto]
            self.map@.dom().contains(rw_pt_root)
            ==>
            { 
                &&&
                self.map@[rw_pt_root].is_init()
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

    pub open spec fn spec_index(&self, rwlock_root: RwLockPageTableRoot) -> RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>
        recommends
            self.inv(),
            self.dom().contains(rwlock_root),
    {
        self.map@[rwlock_root].value()
    }

    pub fn wlock(&mut self, rwlock_root: RwLockPageTableRoot, Tracked(lm): Tracked<&mut LockManager>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).dom().contains(rwlock_root),
            old(lm).lock_seq().len() == 0
                || old(self)[rwlock_root].lock_id().greater(old(lm).lock_seq().last()),
            old(self)[rwlock_root].locked(old(lm).thread_id()) == false,
        ensures 
            self.inv(),
    {
        proof{ 
            self.page_table_dom_lock_id_axiom();
        }
        let tracked mut rwlock_perm = self.map.borrow_mut().tracked_remove(rwlock_root);
        let mut rwlock = PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(rwlock_root).take(Tracked(&mut rwlock_perm));
        let ret = rwlock.wlock(Tracked(lm));
        PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(rwlock_root).put(Tracked(&mut rwlock_perm), rwlock);
        proof{
            self.map.borrow_mut().tracked_insert(rwlock_root, rwlock_perm);
        }
        ret
    }
}

}
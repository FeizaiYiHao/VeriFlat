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
                self.map@[rw_pt_root].value().is_init() ==> self.map@[rw_pt_root].value().inv()
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

    pub open spec fn spec_index(&self, pagetable_root: RwLockPageTableRoot) -> RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>
        recommends
            self.dom().contains(pagetable_root),
    {
        self.map@[pagetable_root].value()
    }

    pub fn wlock(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            old(lock_manager).lock_seq().len() == 0
                || old(self)[pagetable_root].lock_id().greater(old(lock_manager).lock_seq().last()),
            old(self)[pagetable_root].locked(old(lock_manager).thread_id()) == false,
            old(lock_manager).wf(),
        ensures 
            self.inv(),
            self.dom() == old(self).dom(),
            forall|pt_r:PageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],
            
            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() == old(lock_manager).lock_seq().push(self[pagetable_root].lock_id()),
            lock_manager.wf(),

            self[pagetable_root].lock_id() == old(self)[pagetable_root].lock_id(),
            old(self)[pagetable_root].released() == false ==> self[pagetable_root]@ == old(self)[pagetable_root]@,
            self[pagetable_root].wlocked(lock_manager.thread_id()),
            self[pagetable_root].rlocked(lock_manager.thread_id()) == false,

            ret@.lock_id() == self[pagetable_root].lock_id(),
            ret@.state == LockState::WriteLock,
    {
        proof{ 
            self.page_table_dom_lock_id_axiom();
        }
        let tracked mut rwlock_perm = self.map.borrow_mut().tracked_remove(pagetable_root);
        let mut rwlock = PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).take(Tracked(&mut rwlock_perm));
        let ret = rwlock.wlock(Tracked(lock_manager));
        PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).put(Tracked(&mut rwlock_perm), rwlock);
        proof{
            self.map.borrow_mut().tracked_insert(pagetable_root, rwlock_perm);
        }
        ret
    }

        pub fn wunlock(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lock_manager): Tracked<&mut LockManager>, Tracked(lock_perm): Tracked<LockPerm>) 
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            old(self)[pagetable_root].wlocked(old(lock_manager).thread_id()) == true,
            old(self)[pagetable_root].is_init(),
            old(lock_manager).lock_seq().contains(old(self)[pagetable_root].lock_id()),
            old(lock_manager).wf(),
            lock_perm.lock_id() == old(self)[pagetable_root].lock_id(),
            lock_perm.state == LockState::WriteLock,
            lock_perm.thread_id() == old(lock_manager).thread_id(),
        ensures 
            self.inv(),
            self.dom() == old(self).dom(),
            forall|pt_r:PageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],
            
            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() == old(lock_manager).lock_seq().remove_value(self[pagetable_root].lock_id()),
            lock_manager.wf(),

            self[pagetable_root].lock_id() == old(self)[pagetable_root].lock_id(),
            self[pagetable_root]@ == old(self)[pagetable_root]@,
            self[pagetable_root].wlocked(lock_manager.thread_id()) == false,
            self[pagetable_root].rlocked(lock_manager.thread_id()) == false,
    {
        // proof{ 
        //     self.page_table_dom_lock_id_axiom();
        // }
        let tracked mut rwlock_perm = self.map.borrow_mut().tracked_remove(pagetable_root);
        let mut rwlock = PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).take(Tracked(&mut rwlock_perm));
        rwlock.wunlock(Tracked(lock_manager), Tracked(lock_perm));
        PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).put(Tracked(&mut rwlock_perm), rwlock);
        proof{
            self.map.borrow_mut().tracked_insert(pagetable_root, rwlock_perm);
        }
    }
}

}
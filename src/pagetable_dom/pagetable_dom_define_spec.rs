use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::define::*;
use crate::pagetable_seq::entry::MapEntry;
use crate::pagetable_seq::pagetable_spec::*;
use crate::primitive::*;
use crate::util::page_ptr_util_u::page_ptr_valid;
use crate::util::page_ptr_util_u::spec_index2va;
verus! {

pub struct PageTableDom{
    pub map: Tracked<Map<RwLockPageTableRoot, PointsTo<RwLock<PageTable>>>>
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
                {
                    |||
                    self.map@[rw_pt_root].value().wlocked()
                    |||
                    self.map@[rw_pt_root].value().inv()
                }
            }
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
            self[pagetable_root].wlocked_by(lock_manager.thread_id()),
            self[pagetable_root].rlocked_by(lock_manager.thread_id()) == false,

            ret@.lock_id() == self[pagetable_root].lock_id(),
            ret@.state == LockState::WriteLock,
    {
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
            old(self)[pagetable_root].wlocked_by(old(lock_manager).thread_id()) == true,
            old(self)[pagetable_root].inv(),

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
            self[pagetable_root].wlocked_by(lock_manager.thread_id()) == false,
            self[pagetable_root].rlocked_by(lock_manager.thread_id()) == false,
    {
        let tracked mut rwlock_perm = self.map.borrow_mut().tracked_remove(pagetable_root);
        let mut rwlock = PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).take(Tracked(&mut rwlock_perm));
        rwlock.wunlock(Tracked(lock_manager), Tracked(lock_perm));
        PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).put(Tracked(&mut rwlock_perm), rwlock);
        proof{
            self.map.borrow_mut().tracked_insert(pagetable_root, rwlock_perm);
        }
    }

    pub fn map_4k_page(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lock_perm): Tracked<&LockPerm>, 
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,)
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            old(self)[pagetable_root].wlocked_by(lock_perm.thread_id()) == true,
            old(self)[pagetable_root].inv(),

            lock_perm.state == LockState::WriteLock,
            lock_perm.lock_id().major == PAGE_TABLE_LOCK_MAJOR,
            lock_perm.lock_id().minor == old(self)[pagetable_root]@.cr3,

            old(self)[pagetable_root]@.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self)[pagetable_root]@.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self)[pagetable_root]@.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
                == target_l1_p,
            old(self)[pagetable_root]@.spec_resolve_mapping_4k_l1(target_l4i,target_l3i,target_l2i,target_l1i) is None 
                || old(self)[pagetable_root]@.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
        ensures
            self.inv(),
            self.dom() == old(self).dom(),
            forall|pt_r:PageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],

            self[pagetable_root].inv(),
            self[pagetable_root]@.kernel_l4_end == old(self)[pagetable_root]@.kernel_l4_end,
            self[pagetable_root]@.page_closure() =~= old(self)[pagetable_root]@.page_closure(),
            self[pagetable_root]@.mapping_4k@ == old(self)[pagetable_root]@.mapping_4k@.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),*target_entry),
            self[pagetable_root]@.mapping_2m() =~= old(self)[pagetable_root]@.mapping_2m(),
            self[pagetable_root]@.mapping_1g() =~= old(self)[pagetable_root]@.mapping_1g(),
            self[pagetable_root]@.kernel_entries =~= old(self)[pagetable_root]@.kernel_entries,
    {
        let tracked pt_perm = self.map.borrow_mut().tracked_remove(pagetable_root);
        let mut pt_lock = PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).take(Tracked(&mut pt_perm));
        let mut pt = pt_lock.take(Tracked(lock_perm));
        pt.map_4k_page(target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p,target_entry);
        pt_lock.put(Tracked(lock_perm), pt);
        PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).put(Tracked(&mut pt_perm), pt_lock);
        proof{
            self.map.borrow_mut().tracked_insert(pagetable_root, pt_perm);
        }
    }
}

}
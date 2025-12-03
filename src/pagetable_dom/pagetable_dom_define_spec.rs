use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::define::*;
use crate::pagetable_seq::*;
use crate::primitive::*;
use crate::locks::*;
verus! {

pub struct PageTableDom{
    pub map: LockedMap<PageTable, PAGE_TABLE_HAS_KILL_STATE>,
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
        self.map.perms_wf()
    }

    pub open spec fn wlocked_or_inv(&self) -> bool{
        &&&
        forall|pt_r:PageTableRoot|
            #![auto]
            self.dom().contains(pt_r)
            ==>
                self[pt_r].wlocked() || self[pt_r].inv()
    }

    pub open spec fn spec_index(&self, pagetable_root: RwLockPageTableRoot) -> RwLock<PageTable, PAGE_TABLE_HAS_KILL_STATE>
        recommends
            self.dom().contains(pagetable_root),
    {
        self.map[pagetable_root]
    }

    pub fn wlock(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            old(lock_manager).lock_seq().len() == 0
                || LockId::from_pagetable_root(pagetable_root) > old(lock_manager).lock_seq().last(),
            old(self)[pagetable_root].locked_by(old(lock_manager)) == false,
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
            lock_manager.lock_seq() == old(lock_manager).lock_seq().push(LockId::from_pagetable_root(pagetable_root)),
            lock_manager.wf(),

            wlock_ensures(old(self)[pagetable_root], self[pagetable_root], LockId::from_pagetable_root(pagetable_root), lock_manager.thread_id(), ret@),
            lock_ensures(old(lock_manager), lock_manager, LockId::from_pagetable_root(pagetable_root)),
    {
        self.map.wlock(pagetable_root, Tracked(lock_manager), Ghost(LockId::from_pagetable_root(pagetable_root)))
    }

    pub fn wunlock(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lock_manager): Tracked<&mut LockManager>, lock_perm: Tracked<LockPerm>) 
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            
            old(self)[pagetable_root].wlocked_by(old(lock_manager)),
            old(self)[pagetable_root].being_killed() == false,
            old(self)[pagetable_root].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lock_manager).thread_id(),
            lock_perm@.lock_id() == old(self)[pagetable_root].locking_thread() -> Write_lock_id,
        ensures 
            self.inv(),
            self.dom() == old(self).dom(),
            forall|pt_r:PageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],
        
            self[pagetable_root].locking_thread() is None,

            wunlock_ensures(old(self)[pagetable_root], self[pagetable_root]),
            unlock_ensures(old(lock_manager), lock_manager, lock_perm@.lock_id()),
    {
        self.map.wunlock(pagetable_root, Tracked(lock_manager), lock_perm);
    }

//     pub fn map_4k_page(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lock_perm): Tracked<&LockPerm>, 
//         target_l4i: L4Index,
//         target_l3i: L3Index,
//         target_l2i: L2Index,
//         target_l1i: L2Index,
//         target_l1_p: PageMapPtr,
//         target_entry: &MapEntry,)
//         requires
//             old(self).inv(),
//             old(self).dom().contains(pagetable_root),
//             old(self)[pagetable_root].wlocked_by(lock_perm.thread_id()) == true,
//             old(self)[pagetable_root].inv(),

//             lock_perm.state == LockState::WriteLock,
//             lock_perm.lock_id().major == PAGE_TABLE_LOCK_MAJOR,
//             lock_perm.lock_id().minor == old(self)[pagetable_root]@.cr3,

//             old(self)[pagetable_root]@.kernel_l4_end <= target_l4i < 512,
//             0 <= target_l3i < 512,
//             0 <= target_l2i < 512,
//             0 <= target_l1i < 512,
//             old(self)[pagetable_root]@.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
//             old(self)[pagetable_root]@.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
//                 == target_l1_p,
//             old(self)[pagetable_root]@.spec_resolve_mapping_4k_l1(target_l4i,target_l3i,target_l2i,target_l1i) is None 
//                 || old(self)[pagetable_root]@.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
//             page_ptr_valid(target_entry.addr),
//             target_entry.present,
//         ensures
//             self.inv(),
//             self.dom() == old(self).dom(),
//             forall|pt_r:PageTableRoot|
//                 #![auto]
//                 self.dom().contains(pt_r) && pt_r != pagetable_root
//                 ==>
//                     self[pt_r] == old(self)[pt_r],

//             self[pagetable_root].inv(),
//             self[pagetable_root]@.kernel_l4_end == old(self)[pagetable_root]@.kernel_l4_end,
//             self[pagetable_root]@.page_closure() =~= old(self)[pagetable_root]@.page_closure(),
//             self[pagetable_root]@.mapping_4k@ == old(self)[pagetable_root]@.mapping_4k@.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),*target_entry),
//             self[pagetable_root]@.mapping_2m() =~= old(self)[pagetable_root]@.mapping_2m(),
//             self[pagetable_root]@.mapping_1g() =~= old(self)[pagetable_root]@.mapping_1g(),
//             self[pagetable_root]@.kernel_entries =~= old(self)[pagetable_root]@.kernel_entries,
//     {
//         let tracked pt_perm = self.map.borrow_mut().tracked_remove(pagetable_root);
//         let mut pt_lock = PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).take(Tracked(&mut pt_perm));
//         let mut pt = pt_lock.take(Tracked(lock_perm));
//         pt.map_4k_page(target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p,target_entry);
//         pt_lock.put(Tracked(lock_perm), pt);
//         PPtr::<RwLock<PageTable, PAGE_TABLE_LOCK_MAJOR>>::from_usize(pagetable_root).put(Tracked(&mut pt_perm), pt_lock);
//         proof{
//             self.map.borrow_mut().tracked_insert(pagetable_root, pt_perm);
//         }
//     }
}

}
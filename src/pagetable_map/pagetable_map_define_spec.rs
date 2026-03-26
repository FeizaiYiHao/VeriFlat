use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::define::*;
use crate::pagetable_seq::*;
use crate::primitive::*;
use crate::locks::*;
use crate::util::*;
verus! {

pub struct LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>{
    pub map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>,
}

impl LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE> {
    pub open spec fn inv(&self) -> bool {
        &&&
        self.perms_wf()
        &&&
        self.wlocked_or_inv()
    }

    pub open spec fn dom(&self) -> Set<RwLockPageTableRoot>{
        self.map@.dom()
    }

    pub open spec fn perms_wf(&self) -> bool {
        self.map.perms_wf()
    }

    pub open spec fn wlocked_or_inv(&self) -> bool{
        &&&
        forall|pt_r:RwLockPageTableRoot|
            #![auto]
            self.dom().contains(pt_r)
            ==>
                self[pt_r].wlocked() || self[pt_r].inv()
    }

    pub open spec fn spec_index(&self, pagetable_root: RwLockPageTableRoot) -> RwLock<PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>
        recommends
            self.dom().contains(pagetable_root),
    {
        self.map[pagetable_root]
    }

    #[verifier::veriflat_pull]
    pub fn wlock(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            old(lctx).lock_seq().len() == 0
                || pagetable_root.to_lock_id() > old(lctx).lock_seq().last(),
            old(self)[pagetable_root].locked_by(old(lctx)) == false,
            old(lctx).locking_serial_num() == old(self)[pagetable_root].serial_num(),

            old(lctx).wf(),
        ensures 
            self.inv(),
            self.dom() == old(self).dom(),
            forall|pt_r:RwLockPageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],
            
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.lock_seq() == old(lctx).lock_seq().push(pagetable_root.to_lock_id()),
            lctx.wf(),

            wlock_ensures(old(self)[pagetable_root], self[pagetable_root], pagetable_root.to_lock_id(), lctx.thread_id(), ret@),
            lock_ensures(old(lctx), lctx, pagetable_root.to_lock_id()),
    {
        self.map.wlock(pagetable_root, Tracked(lctx), Ghost(pagetable_root.to_lock_id()))
    }

    #[verifier::veriflat_push]
    pub fn wunlock(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>) 
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            
            old(self)[pagetable_root].wlocked_by(old(lctx)),
            old(self)[pagetable_root].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[pagetable_root].locking_thread() -> Write_lock_id,
        ensures 
            self.inv(),
            self.dom() == old(self).dom(),
            forall|pt_r:RwLockPageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],
        
            self[pagetable_root].locking_thread() is None,

            wunlock_ensures(old(self)[pagetable_root], self[pagetable_root]),
            unlock_ensures(old(lctx), lctx, lock_perm@.lock_id()),
    {
        self.map.wunlock(pagetable_root, Tracked(lctx), lock_perm);
    }

    pub fn map_4k_page(&mut self, pagetable_root: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(lock_perm): Tracked<&LockPerm>, 
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,)
        requires
            old(self).inv(),
            old(self).dom().contains(pagetable_root),
            old(self)[pagetable_root].wlocked_by(lctx) == true,
            old(self)[pagetable_root].inv(),

            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == lctx.thread_id(),
            lock_perm.lock_id() == old(self)[pagetable_root].locking_thread() -> Write_lock_id,

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
            forall|pt_r:RwLockPageTableRoot|
                #![auto]
                self.dom().contains(pt_r) && pt_r != pagetable_root
                ==>
                    self[pt_r] == old(self)[pt_r],

            self[pagetable_root].wlocked_by(lctx) == true,
            self[pagetable_root].inv(),
            self[pagetable_root]@.kernel_l4_end == old(self)[pagetable_root]@.kernel_l4_end,
            self[pagetable_root]@.page_closure() =~= old(self)[pagetable_root]@.page_closure(),
            self[pagetable_root]@.mapping_4k@ == old(self)[pagetable_root]@.mapping_4k@.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),*target_entry),
            self[pagetable_root]@.mapping_2m() =~= old(self)[pagetable_root]@.mapping_2m(),
            self[pagetable_root]@.mapping_1g() =~= old(self)[pagetable_root]@.mapping_1g(),
            self[pagetable_root]@.kernel_entries =~= old(self)[pagetable_root]@.kernel_entries,
            self[pagetable_root]@.pcid_or_ioid() =~= old(self)[pagetable_root]@.pcid_or_ioid(),
            self[pagetable_root]@.cr3 =~= old(self)[pagetable_root]@.cr3,

    {
        let mut pagetable = self.map.take(pagetable_root, Tracked(lctx), Tracked(lock_perm));
        pagetable.map_4k_page(target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        self.map.put(pagetable_root, Tracked(lctx), Tracked(lock_perm), pagetable);
    }
}

}
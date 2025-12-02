use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use crate::concurrency::*;
verus! {

pub enum MapDomainDelta{
    None,
    Sub(Set<usize>),
    Add(Set<usize>),
}

#[verifier::reject_recursive_types(V)]
pub struct LockedMap<V:LockedUtil + LockOwnerIdUtil>{
    map: Tracked<Map<usize, PointsTo<RwLock<V>>>>,
    delta: MapDomainDelta,
}

impl<V:LockedUtil + LockOwnerIdUtil> LockedMap<V>{
    pub closed spec fn delta(&self) -> MapDomainDelta{
        self.delta
    }
    pub closed spec fn view(&self) -> Map<usize, PointsTo<RwLock<V>>>{
        self.map@
    }
    pub open spec fn dom(&self) -> Set<usize>{
        self@.dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:usize| 
            #![auto]
            self@.dom().contains(k)
            ==>
            { 
                &&&
                self@[k].is_init()
                &&&
                self@[k].addr() == k
            }
    }
    pub open spec fn spec_index(&self, key: usize) -> RwLock<V>
        recommends
            self@.dom().contains(key),
    {
        self@[key].value()
    }
    pub open spec fn unchanged_except(&self, old: &Self, key:usize) -> bool{
        &&&
        old.delta() == self.delta()
        &&&
        old.dom() == self.dom()
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && k != key
            ==>
            self[k] == old[k]
    }
    pub fn wlock(&mut self, key:usize, Tracked(lock_manager): Tracked<&mut LockManager>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)@[key].lock_major_sat(lock_id@.major),
            old(self)@[key].lock_minor() == lock_id@.minor,

            wlock_requires(old(self)[key], old(lock_manager)),
            old(lock_manager).lock_id_valid(lock_id@),
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            wlock_ensures(old(self)[key], self[key], lock_id@, lock_manager.thread_id(), ret@),
            lock_ensures(old(lock_manager), lock_manager, lock_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wlock(&PPtr::<RwLock<V>>::from_usize(key), Tracked(&mut perm), Tracked(lock_manager), lock_id);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn wunlock(&mut self, key:usize, Tracked(lock_manager): Tracked<&mut LockManager>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(old(lock_manager)),
            old(self)[key].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lock_manager).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread()->Write_lock_id,
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            self[key].locking_thread() is None,

            wunlock_ensures(old(self)[key], self[key]),
            unlock_ensures(old(lock_manager), lock_manager, lock_perm@.lock_id()),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wunlock(&PPtr::<RwLock<V>>::from_usize(key), Tracked(&mut perm), Tracked(lock_manager), lock_perm);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }
}

impl<V:LockedUtil + LockOwnerIdUtil> Step for LockedMap<V>{
    open spec fn step_spec(self, old:&Self, lock_manager: &LockManager) -> bool{
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && old[k].locked_by(lock_manager)
            ==>
            self.dom().contains(k) && self[k] =~= old[k]
        &&&
        self.delta() =~= old.delta()
    }
    proof fn step(&mut self, lock_manager: &LockManager)
    {
        admit()
    }
}

}
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use crate::concurrency::*;
verus! {

#[verifier::reject_recursive_types(K)]
pub enum MapDomainDelta<K>{
    None,
    Sub(Set<K>),
    Add(Set<K>),
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
pub struct LockedMap<K:ToUsize, T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool>{
    map: Tracked<Map<K, PointsTo<RwLock<T, HasKillState>>>>,
    delta: MapDomainDelta<K>,
}

impl<K:ToUsize, T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool> LockedMap<K, T, HasKillState>{
    pub closed spec fn delta(&self) -> MapDomainDelta<K>{
        self.delta
    }
    pub closed spec fn view(&self) -> Map<K, PointsTo<RwLock<T, HasKillState>>>{
        self.map@
    }
    pub open spec fn dom(&self) -> Set<K>{
        self@.dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:K| 
            #![trigger self@[k].is_init()]
            #![trigger self@[k].addr()]
            self@.dom().contains(k)
            ==>
            { 
                &&&
                self@[k].is_init()
                &&&
                self@[k].addr() == k.to_usize()
            }
    }
    pub open spec fn spec_index(&self, key: K) -> RwLock<T, HasKillState>
        recommends
            self@.dom().contains(key),
    {
        self@[key].value()
    }
    pub open spec fn unchanged_except(&self, old: &Self, key:K) -> bool{
        &&&
        old.delta() == self.delta()
        &&&
        old.dom() == self.dom()
        &&&
        forall|k:K|
            #![auto]
            old.dom().contains(k) && k != key
            ==>
            self[k] == old[k]
    }
    pub fn wlock(&mut self, key:K, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)@[key].lock_major_sat(lock_id@.major),
            old(self)@[key].lock_minor() == lock_id@.minor,

            wlock_requires(old(self)[key], old(lctx)),
            old(lctx).lock_id_valid(lock_id@),
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            wlock_ensures(old(self)[key], self[key], lock_id@, lctx.thread_id(), ret@),
            lock_ensures(old(lctx), lctx, lock_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wlock(&PPtr::<RwLock<T, HasKillState>>::from_usize(key.to_usize()), Tracked(&mut perm), Tracked(lctx), lock_id);
        assert(perm.addr() == key.to_usize());
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn wunlock(&mut self, key:K, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(old(lctx)),
            old(self)[key].being_killed() == false,
            old(self)[key].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            self[key].locking_thread() is None,

            wunlock_ensures(old(self)[key], self[key]),
            unlock_ensures(old(lctx), lctx, lock_perm@.lock_id()),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wunlock(&PPtr::<RwLock<T, HasKillState>>::from_usize(key.to_usize()), Tracked(&mut perm), Tracked(lctx), lock_perm);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn take(&mut self, key:K, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret:T)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(lctx),
            old(self)[key].is_init(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == lctx.thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            take_ensures(old(self)[key], self[key]),

            ret == old(self)[key]@,
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = take(&PPtr::<RwLock<T, HasKillState>>::from_usize(key.to_usize()), Tracked(&mut perm), Tracked(lctx), lock_perm);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn put(&mut self, key:K, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>, v:T)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(lctx),
            old(self)[key].is_init() == false,

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == lctx.thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            put_ensures(old(self)[key], self[key], v),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        put(&PPtr::<RwLock<T, HasKillState>>::from_usize(key.to_usize()), Tracked(&mut perm), Tracked(lctx), lock_perm, v);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
    }
}

impl<K:ToUsize, T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool> Step for LockedMap<K, T, HasKillState>{
    open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
        &&&
        forall|k:K|
            #![auto]
            old.dom().contains(k) && old[k].locked_by(lctx)
            ==>
            self.dom().contains(k) && self[k] =~= old[k]
        &&&
        forall|k:K|
            #![auto]
            self.dom().contains(k) && self[k].locked_by(lctx) == false
            ==>
            self[k].being_killed_by(lctx) == false
            &&
            self[k].serial_num() == lctx.locking_serial_num()
        &&&
        self.delta() =~= old.delta()
    }
    proof fn random_step(&mut self, lctx: &LocalContext)
    {
        admit()
    }
}

}
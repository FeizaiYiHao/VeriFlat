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
pub struct LockedMap<K, T, const HasKillState: bool>{
    map: Tracked<Map<K, PointsTo<RwLock<T, HasKillState>>>>,
    delta: MapDomainDelta<K>,
}

impl<T, const HasKillState: bool> LockedMap<usize, T, HasKillState>{
    pub closed spec fn delta(&self) -> MapDomainDelta<usize>{
        self.delta
    }
    pub closed spec fn view(&self) -> Map<usize, PointsTo<RwLock<T, HasKillState>>>{
        self.map@
    }
    // pub closed spec fn user_view(&self) -> Map<usize, >
    pub open spec fn dom(&self) -> Set<usize>{
        self@.dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:usize| 
            #![trigger self@[k].is_init()]
            #![trigger self@[k].addr()]
            self@.dom().contains(k)
            ==>
            { 
                &&&
                self@[k].is_init()
                &&&
                self@[k].addr() == k
            }
    }
    pub open spec fn spec_index(&self, key: usize) -> RwLock<T, HasKillState>
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

    pub fn take(&mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret:T)
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
        let ret = take(&PPtr::<RwLock<T, HasKillState>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn put(&mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>, v:T)
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
        put(&PPtr::<RwLock<T, HasKillState>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm, v);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
    }

    pub fn borrow<'a>(&self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret:&'a T)
        requires
            self.perms_wf(),
            self.dom().contains(key),
            
            self[key].locked_by(lctx),
            self[key].is_init(),

            lock_perm@.thread_id() == lctx.thread_id(),
            lock_perm@.state() is WriteLock ==> self[key].write_lock_perm_match(lock_perm@),
            lock_perm@.state() is ReadLock ==> self[key].read_lock_perm_match(lock_perm@), 
        ensures
            ret == self[key]@,
    {
        let tracked perm = self.map.tracked_borrow(key);
        let ret = borrow(&PPtr::<RwLock<T, HasKillState>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm);
        return ret;
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait> LockedMap<usize, T, NO_KILL_STATE>{
    pub fn wlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)@[key].lock_major_sat(lock_id@.major),
            old(self)@[key].lock_minor() == lock_id@.minor,

            wlock_requires(old(self)[key], old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            wlock_ensures(old(self)[key], self[key], lock_id@, lctx.thread_id(), ret@),
            lock_ensures(old(lctx), lctx, self[key]@, lock_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wlock(&PPtr::<RwLock<T, NO_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_id);
        assert(perm.addr() == key);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn wunlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(old(lctx)),
            old(self)[key].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,
        ensures
            self.perms_wf(),
            self.unchanged_except(old(self), key),

            self[key].locking_thread() is None,

            wunlock_ensures(old(self)[key], self[key]),
            unlock_ensures(old(lctx), lctx, self[key]@, lock_perm@.lock_id()),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wunlock(&PPtr::<RwLock<T, NO_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }
}

impl<T:LockInvTrait + LockRecursivelyLockedTrait, const HasKillState: bool> Step for LockedMap<usize, T, HasKillState>{
    open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && old[k].partial_locked_by(lctx)
            ==>
            self.dom().contains(k) && self[k] =~= old[k]
    }
    proof fn random_step(&mut self, lctx: &LocalContext)
    {
        admit()
    }
}

}
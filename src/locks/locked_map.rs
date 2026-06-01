use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use crate::concurrency::*;
verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
pub struct LockedMap<K, T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>{
    map: Tracked<Map<K, PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>>,

    map_u: Ghost<Map<K, RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>,
}

impl<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> LockedMap<usize, T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    pub closed spec fn user_view(&self) -> Map<usize, RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
        self.map_u.view()
    }

    pub closed spec fn view(&self) -> Map<usize, PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>{
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
    pub open spec fn spec_index(&self, key: usize) -> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>
        recommends
            self@.dom().contains(key),
    {
        self@[key].value()
    }

    pub open spec fn unchanged_except(&self, old: &Self, key:usize) -> bool{
        &&&
        old.dom() == self.dom()
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && k != key
            ==>
            self[k] == old[k]
    }

    pub open spec fn user_view_unchanged(&self, old: &Self,) -> bool{
        &&&
        self.user_view() == old.user_view()
    }

    pub open spec fn user_view_unchanged_except(&self, old: &Self, key:usize) -> bool{
        &&&
        self.user_view().dom() == old.user_view().dom()
        &&&
        forall|k:usize|
            #![trigger self.user_view()[k]]
            old.user_view().dom().contains(k) && k != key
            ==>
            self.user_view()[k] == old.user_view()[k]
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
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).user_view_unchanged(old(self)),

            take_ensures(old(self)[key], final(self)[key]),

            ret == old(self)[key]@,
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = take(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm);
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
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).user_view_unchanged(old(self)),

            put_ensures(old(self)[key], final(self)[key], v),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        put(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm, v);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
    }

    pub fn borrow<'a>(&self, key:usize, lock_perm: Tracked<&'a LockPerm>) -> (ret:&'a T)
        requires
            self.perms_wf(),
            self.dom().contains(key),
            
            self[key].is_init(),

            lock_perm@.state() is WriteLock ==> self[key].write_lock_perm_match(lock_perm@),
            lock_perm@.state() is ReadLock ==> self[key].read_lock_perm_match(lock_perm@), 
        ensures
            ret == self[key]@,
    {
        let tracked perm = self.map.tracked_borrow(key);
        let ret = borrow(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&mut perm), lock_perm);
        return ret;
    }

    pub fn borrow_mut<'a>(&'a mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            old(self)[key].wlocked_by(lctx),
            old(self)[key].is_init(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == lctx.thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),

            // Other entries unchanged.
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k) && k != key
                ==>
                final(self)[k] == old(self)[k],

            // Lock state of `key`'s rwlock is preserved.
            final(self)[key].is_init(),
            final(self)[key].view_rodata() == old(self)[key].view_rodata(),
            final(self)[key].view_kernel_ghost() == old(self)[key].view_kernel_ghost(),
            final(self)[key].view_user_ghost() == old(self)[key].view_user_ghost(),
            final(self)[key].locking_thread() == old(self)[key].locking_thread(),
            final(self)[key].being_killed() == old(self)[key].being_killed(),

            // The `&mut T` linkage.
            *ret == old(self)[key]@,
            final(self)[key]@ == *final(ret),
    {
        let tracked perm = self.map.borrow_mut().tracked_borrow_mut(key);
        let ret = borrow_mut(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(perm), Tracked(lctx), lock_perm);
        return ret;
    }

    pub fn borrow_rodata(&self, key:usize) -> (ret:&ROT)
        requires
            self.perms_wf(),
            self.dom().contains(key),
        ensures
            ret == self[key].view_rodata(),
    {
        let tracked perm = self.map.tracked_borrow(key);
        let ret = borrow_rodata(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&perm));
        return ret;
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, NO_KILL_STATE>{
    pub fn wlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            wlock_requires(old(self)[key], old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self)@[key].container_depth(),
                process: old(self)@[key].process_depth(),
                major: old(self)@[key].value()@.current_lock_major(),
                minor: key,
            }),
            old(lctx).obj_id_fresh(obj_id@),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).user_view_unchanged(old(self)),

            wlock_ensures(old(self)[key], final(self)[key], LockId{
                container: old(self)@[key].container_depth(),
                process: old(self)@[key].process_depth(),
                major: old(self)@[key].value()@.current_lock_major(),
                minor: key,
            }, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self)[key]@, LockId{
                container: old(self)@[key].container_depth(),
                process: old(self)@[key].process_depth(),
                major: old(self)@[key].value()@.current_lock_major(),
                minor: key,
            }, obj_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wlock(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), obj_id);
        assert(perm.addr() == key);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn wunlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(old(lctx)),
            old(self)[key].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,

            old(lctx).lock_map().dom().contains(obj_id@),
            old(lctx).lock_map()[obj_id@] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).user_view_unchanged_except(old(self), key),
            final(self).user_view().spec_index(key) == final(self)[key],

            final(self)[key].locking_thread() is None,

            wunlock_ensures(old(self)[key], final(self)[key]),
            unlock_ensures(old(lctx), final(lctx), final(self)[key]@, lock_perm@.lock_id(), obj_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wunlock(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm, obj_id);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        proof{
            self.map_u@ = self.map_u@.insert(key, self[key]);
            assume(self.user_view_unchanged_except(old(self), key));
        }
        return ret;
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    pub fn wlock_unless_killed(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: (bool, Option<Tracked<LockPerm>>))
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            // wlock_requires(old(self)[key], old(lctx)),
            old(self)[key].locked_by(old(lctx)) == false,
            old(lctx).kernel_view_locking_state() is Acquire,
            T::is_user_visible() ==> old(lctx).user_view_locking_state() is Acquire,

            old(lctx).lock_id_acyclic(LockId{
                container: old(self)@[key].container_depth(),
                process: old(self)@[key].process_depth(),
                major: old(self)@[key].value()@.current_lock_major(),
                minor: key,
            }),
            old(lctx).obj_id_fresh(obj_id@),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).user_view_unchanged(old(self)),

            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

            ret.0 == false ==> 
            {
                &&&
                old(self)[key].being_killed() == true
                &&&
                old(self)[key] == final(self)[key]
                &&&
                ret.1 is None
                &&&
                final(lctx).lock_map() =~= old(lctx).lock_map()
            },
            ret.0 == true ==>{
                &&&                
                old(self)[key].being_killed() == false
                &&&
                ret.1 is Some
                &&&
                wlock_ensures(old(self)[key], final(self)[key], LockId{
                    container: old(self)@[key].container_depth(),
                    process: old(self)@[key].process_depth(),
                    major: old(self)@[key].value()@.current_lock_major(),
                    minor: key,
                }, final(lctx).thread_id(), ret.1.unwrap()@)
                &&&
                lock_ensures(old(lctx), final(lctx), old(self)[key].view(), LockId{
                    container: old(self)@[key].container_depth(),
                    process: old(self)@[key].process_depth(),
                    major: old(self)@[key].value()@.current_lock_major(),
                    minor: key,
                }, obj_id@)
            },
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wlock_unless_killed(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), obj_id);
        assert(perm.addr() == key);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }

    pub fn wunlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self)[key].wlocked_by(old(lctx)),
            old(self)[key].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,

            old(lctx).lock_map().dom().contains(obj_id@),
            old(lctx).lock_map()[obj_id@] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).user_view_unchanged_except(old(self), key),
            final(self).user_view().spec_index(key) == final(self)[key],

            final(self)[key].locking_thread() is None,
            old(self)[key].being_killed() == final(self)[key].being_killed(),

            wunlock_ensures(old(self)[key], final(self)[key]),
            unlock_ensures(old(lctx), final(lctx), final(self)[key]@, lock_perm@.lock_id(), obj_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = has_kill_state_wunlock(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm, obj_id);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        proof{
            self.map_u@ = self.map_u@.insert(key, self[key]);
            assume(self.user_view_unchanged_except(old(self), key));
        }
        return ret;
    }
}

impl<T:LockInvTrait + LockRecursivelyLockedTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> Step for LockedMap<usize, T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
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

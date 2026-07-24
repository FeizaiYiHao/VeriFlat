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
    pub closed spec fn view(&self) -> Map<usize, PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>{
        self.map@
    }
    pub open spec fn dom(&self) -> Set<usize>{
        self@.dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:usize| 
            #![trigger self@[k].is_init()]
            #![trigger self@[k].addr()]
            #![trigger self@.dom().contains(k)]
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
            #![trigger self.spec_index(k)]
            #![trigger old.spec_index(k)]
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
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

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

    pub proof fn update_kernel_ghost(tracked &mut self, key:usize, new_kernel_ghost: KGhostT)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            update_kernel_ghost_ensures(old(self)[key], final(self)[key], new_kernel_ghost),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        update_kernel_ghost(&mut perm, new_kernel_ghost);
        self.map.borrow_mut().tracked_insert(key, perm);
    }

    pub proof fn update_user_ghost(tracked &mut self, key:usize, new_user_ghost: UGhostT)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            update_user_ghost_ensures(old(self)[key], final(self)[key], new_user_ghost),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        update_user_ghost(&mut perm, new_user_ghost);
        self.map.borrow_mut().tracked_insert(key, perm);
    }
}


impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    pub open spec fn lock_id_by_key(&self, key: usize) -> LockId
        recommends
            self.dom().contains(key)
    {
        self.view().spec_index(key).lock_id()
    }

    /// TCB: register a brand-new object into the map at a fresh key, GROWING the
    /// domain. Mints a fresh `RwLock<T>` at address `key` holding `value` /
    /// `rodata` / `kernel_ghost` / `user_ghost`, initialized (`is_init`), not
    /// being-killed, and WRITE-LOCKED by the calling thread — so the caller can
    /// immediately `borrow_mut` to finish wiring the object and later `wunlock`
    /// it. Registers the lock id in `lctx.lock_map()` under `obj_id`, returning
    /// the `LockPerm` (same shape as `wlock`).
    ///
    /// This is the ONLY operation that changes a `LockedMap`'s domain; every
    /// other method preserves `dom()`. Allocation itself is trusted (there is no
    /// verified heap allocator); the returned key is assumed to be a fresh,
    /// otherwise-unused slot address, enforced by `!old(self).dom().contains(key)`.
    /// The acyclicity precondition uses the same `LockId` (container/process/major
    /// derived from `value`, minor = `key`) that `wlock` computes, so a
    /// freshly-inserted-and-locked object obeys global lock ordering exactly like
    /// an ordinarily-acquired one.
    #[verifier::external_body]
    pub fn insert(
        &mut self,
        key: usize,
        value: T,
        rodata: ROT,
        Ghost(kernel_ghost): Ghost<KGhostT>,
        Ghost(user_ghost): Ghost<UGhostT>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key) == false,
            value.inv(),
            old(lctx).lock_id_acyclic(LockId{
                container: rodata.container_depth(),
                process: rodata.process_depth(),
                major: value.current_lock_major(),
                minor: key,
            }),
            old(lctx).obj_id_fresh(obj_id@),
        ensures
            final(self).perms_wf(),
            // ---- domain grows by exactly `key`; every prior entry unchanged ----
            final(self).dom() =~= old(self).dom().insert(key),
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k)
                ==>
                final(self)[k] == old(self)[k],
            // ---- the new entry: initialized, write-locked, holds the given payload ----
            final(self).dom().contains(key),
            final(self)[key].is_init(),
            final(self)[key]@ == value,
            final(self)[key].view_rodata() == rodata,
            final(self)[key].view_kernel_ghost() == kernel_ghost,
            final(self)[key].view_user_ghost() == user_ghost,
            final(self)[key].being_killed() == false,
            final(self)[key].locking_thread() == (RwLockState::Write {
                thread_id: final(lctx).thread_id(),
                lock_id: final(self).lock_id_by_key(key),
            }),
            final(self).lock_id_by_key(key) == (LockId{
                container: rodata.container_depth(),
                process: rodata.process_depth(),
                major: value.current_lock_major(),
                minor: key,
            }),
            // ---- the returned write perm ----
            ret@.state() is WriteLock,
            ret@.thread_id() == final(lctx).thread_id(),
            ret@.lock_id() == final(self).lock_id_by_key(key),
            // ---- lctx: the new lock id is registered under obj_id ----
            lock_ensures(old(lctx), final(lctx), value, final(self).lock_id_by_key(key), obj_id@),
    {
        unimplemented!()
    }

    /// Insert an already-initialized, already-locked entry into the map.
    /// The caller provides the `PointsTo<RwLock<T>>` (from a retype operation)
    /// and the entry is already write-locked. No lctx registration is done here
    /// (the caller handles lock registration via the retype primitive).
    #[verifier::external_body]
    pub fn insert_with_perm(
        &mut self,
        key: usize,
        Tracked(perm): Tracked<PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>,
        rodata: ROT,
        Ghost(kernel_ghost): Ghost<KGhostT>,
        Ghost(user_ghost): Ghost<UGhostT>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key) == false,
            perm.is_init(),
            perm.addr() == key,
            perm.value().is_init(),
            perm.value().view().inv(),
            perm.value().view_rodata() == rodata,
            perm.value().view_kernel_ghost() == kernel_ghost,
            perm.value().view_user_ghost() == user_ghost,
            perm.value().being_killed() == false,
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(key),
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k)
                ==>
                final(self)[k] == old(self)[k],
            final(self).dom().contains(key),
            final(self)[key].is_init(),
            final(self)[key]@ == perm.value().view(),
            final(self)[key].view_rodata() == rodata,
            final(self)[key].view_kernel_ghost() == kernel_ghost,
            final(self)[key].view_user_ghost() == user_ghost,
            final(self)[key].being_killed() == false,
            final(self)[key].locking_thread() == perm.value().locking_thread(),
            final(self).lock_id_by_key(key) == (LockId{
                container: rodata.container_depth(),
                process: rodata.process_depth(),
                major: perm.value().view().current_lock_major(),
                minor: key,
            }),
    {
        unimplemented!()
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, NO_KILL_STATE>{
    pub fn wlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            wlock_requires(old(self)[key], old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).spec_index(key).container_depth(),
                process: old(self).spec_index(key).process_depth(),
                major: old(self).spec_index(key).view().current_lock_major(),
                minor: key,
            }),
            old(lctx).obj_id_fresh(obj_id@),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            wlock_ensures(old(self)[key], final(self)[key], LockId{
                container: old(self).spec_index(key).container_depth(),
                process: old(self).spec_index(key).process_depth(),
                major: old(self).spec_index(key).view().current_lock_major(),
                minor: key,
            }, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self)[key]@, LockId{
                container: old(self).spec_index(key).container_depth(),
                process: old(self).spec_index(key).process_depth(),
                major: old(self).spec_index(key).view().current_lock_major(),
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

            unlock_requires::<T>(old(lctx)),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,

            old(lctx).lock_map().dom().contains(obj_id@),
            old(lctx).lock_map()[obj_id@] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).spec_index(key) == final(self)[key],

            final(self)[key].locking_thread() is None,

            wunlock_ensures(old(self)[key], final(self)[key]),
            unlock_ensures(old(lctx), final(lctx), final(self)[key]@, lock_perm@.lock_id(), obj_id@),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wunlock(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm, obj_id);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
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

            old(lctx).lock_id_acyclic(old(self).lock_id_by_key(key)),
            old(lctx).obj_id_fresh(obj_id@),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            // A (possibly failed) lock attempt never changes the calling
            // thread's identity (see free `wlock_unless_killed`).
            final(lctx).thread_id() == old(lctx).thread_id(),
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
                wlock_ensures(old(self)[key], final(self)[key], old(self).lock_id_by_key(key), final(lctx).thread_id(), ret.1.unwrap()@)
                &&&
                lock_ensures(old(lctx), final(lctx), old(self)[key].view(), old(self).lock_id_by_key(key), obj_id@)
            },
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        assert(perm.value() == old(self).spec_index(key));
        assert(perm.value().container_depth() == old(self).spec_index(key).container_depth());
        assert(perm.value().process_depth() == old(self).spec_index(key).process_depth());
        assert(perm.value().view().current_lock_major() == old(self).spec_index(key).view().current_lock_major());
        assert(perm.lock_minor() == key);
        proof{
            lock_id_fields_eq_imply_eq();
            lctx.lemma_lock_id_eq_imply_acyclic_eq();
        }
        // assert(LockId{
        //         container: old(self).spec_index(key).view().container_depth(),
        //         process: old(self).spec_index(key).view().process_depth(),
        //         major: old(self).spec_index(key).view().current_lock_major(),
        //         minor: key,
        //     }
        //     ==
        //     LockId{
        //         container: perm.value().container_depth(),
        //         process: perm.value().process_depth(),
        //         major: perm.value().view().current_lock_major(),
        //         minor: perm.lock_minor(),
        //     }
        // );
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

            unlock_requires::<T>(old(lctx)),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[key].locking_thread() -> Write_lock_id,

            old(lctx).lock_map().dom().contains(obj_id@),
            old(lctx).lock_map()[obj_id@] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

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

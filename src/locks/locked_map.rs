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
        self.map.view()
    }
    pub open spec fn dom(&self) -> Set<usize>{
        self.view().dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:usize| 
            #![trigger self.view().spec_index(k).is_init()]
            #![trigger self.view().spec_index(k).addr()]
            #![trigger self.view().dom().contains(k)]
            self.view().dom().contains(k)
            ==>
            { 
                &&&
                self.view().spec_index(k).is_init()
                &&&
                self.view().spec_index(k).addr() == k
            }
    }
    pub open spec fn spec_index(&self, key: usize) -> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>
        recommends
            self.view().dom().contains(key),
    {
        self.view().spec_index(key).value()
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
            self.spec_index(k) == old.spec_index(k)
    }

    pub fn take(&mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret:T)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),
            
            old(self).spec_index(key).wlocked_by(lctx),
            old(self).spec_index(key).is_init(),

            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(key).locking_thread() -> Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            take_ensures(old(self).spec_index(key), final(self).spec_index(key)),

            ret == old(self).spec_index(key).view(),
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
            
            old(self).spec_index(key).wlocked_by(lctx),
            old(self).spec_index(key).is_init() == false,

            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(key).locking_thread() -> Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            put_ensures(old(self).spec_index(key), final(self).spec_index(key), v),
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
            
            self.spec_index(key).is_init(),

            lock_perm.view().state() is WriteLock ==> self.spec_index(key).write_lock_perm_match(lock_perm.view()),
            lock_perm.view().state() is ReadLock ==> self.spec_index(key).read_lock_perm_match(lock_perm.view()),
        ensures
            ret == self.spec_index(key).view(),
    {
        let tracked perm = self.map.tracked_borrow(key);
        let ret = borrow(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>::from_usize(key), Tracked(&mut perm), lock_perm);
        return ret;
    }

    pub fn borrow_mut<'a>(&'a mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            old(self).spec_index(key).wlocked_by(lctx),
            old(self).spec_index(key).is_init(),

            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(key).locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),

            // Other entries unchanged.
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k) && k != key
                ==>
                final(self).spec_index(k) == old(self).spec_index(k),

            // Lock state of `key`'s rwlock is preserved.
            final(self).spec_index(key).is_init(),
            final(self).spec_index(key).view_rodata() == old(self).spec_index(key).view_rodata(),
            final(self).spec_index(key).view_kernel_ghost() == old(self).spec_index(key).view_kernel_ghost(),
            final(self).spec_index(key).view_user_ghost() == old(self).spec_index(key).view_user_ghost(),
            final(self).spec_index(key).locking_thread() == old(self).spec_index(key).locking_thread(),
            final(self).spec_index(key).being_killed() == old(self).spec_index(key).being_killed(),

            // The `&mut T` linkage.
            *ret == old(self).spec_index(key).view(),
            final(self).spec_index(key).view() == *final(ret),
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
            ret == self.spec_index(key).view_rodata(),
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

            update_kernel_ghost_ensures(old(self).spec_index(key), final(self).spec_index(key), new_kernel_ghost),
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

            update_user_ghost_ensures(old(self).spec_index(key), final(self).spec_index(key), new_user_ghost),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        update_user_ghost(&mut perm, new_user_ghost);
        self.map.borrow_mut().tracked_insert(key, perm);
    }
}


impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
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
    /// it. Registers the lock id in the corresponding `lctx` map under `obj_id`, returning
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
            old(lctx).obj_id_fresh(obj_id.view()),
        ensures
            final(self).perms_wf(),
            // ---- domain grows by exactly `key`; every prior entry unchanged ----
            final(self).dom() =~= old(self).dom().insert(key),
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k)
                ==>
                final(self).spec_index(k) == old(self).spec_index(k),
            // ---- the new entry: initialized, write-locked, holds the given payload ----
            final(self).dom().contains(key),
            final(self).spec_index(key).is_init(),
            final(self).spec_index(key).view() == value,
            final(self).spec_index(key).view_rodata() == rodata,
            final(self).spec_index(key).view_kernel_ghost() == kernel_ghost,
            final(self).spec_index(key).view_user_ghost() == user_ghost,
            final(self).spec_index(key).being_killed() == false,
            final(self).spec_index(key).locking_thread() == (RwLockState::Write {
                thread_id: final(lctx).thread_id(),
                lock_id: ret.view().lock_id(),
            }),
            final(self).lock_id_by_key(key) == (LockId{
                container: rodata.container_depth(),
                process: rodata.process_depth(),
                major: value.current_lock_major(),
                minor: key,
            }),
            // ---- the returned write perm ----
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            // ---- lctx: the new lock id is registered under obj_id ----
            lock_ensures(old(lctx), final(lctx), value, final(self).lock_id_by_key(key), obj_id.view()),
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
                final(self).spec_index(k) == old(self).spec_index(k),
            final(self).dom().contains(key),
            final(self).spec_index(key).is_init(),
            final(self).spec_index(key).view() == perm.value().view(),
            final(self).spec_index(key).view_rodata() == rodata,
            final(self).spec_index(key).view_kernel_ghost() == kernel_ghost,
            final(self).spec_index(key).view_user_ghost() == user_ghost,
            final(self).spec_index(key).being_killed() == false,
            final(self).spec_index(key).locking_thread() == perm.value().locking_thread(),
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

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, NO_KILL_STATE>{
    pub open spec fn lock_id_by_key(&self, key: usize) -> LockId
        recommends
            self.dom().contains(key)
    {
        self.view().spec_index(key).lock_id()
    }

    pub fn wlock(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            wlock_requires(old(self).spec_index(key), old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).spec_index(key).container_depth(),
                process: old(self).spec_index(key).process_depth(),
                major: old(self).spec_index(key).view().current_lock_major(),
                minor: key,
            }),
            old(lctx).obj_id_fresh(obj_id.view()),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            wlock_ensures(old(self).spec_index(key), final(self).spec_index(key), LockId{
                container: old(self).spec_index(key).container_depth(),
                process: old(self).spec_index(key).process_depth(),
                major: old(self).spec_index(key).view().current_lock_major(),
                minor: key,
            }, final(lctx).thread_id(), ret.view()),
            lock_ensures(old(lctx), final(lctx), final(self).spec_index(key).view(), LockId{
                container: old(self).spec_index(key).container_depth(),
                process: old(self).spec_index(key).process_depth(),
                major: old(self).spec_index(key).view().current_lock_major(),
                minor: key,
            }, obj_id.view()),
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
            
            old(self).spec_index(key).wlocked_by(old(lctx)),
            old(self).spec_index(key).inv(),

            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(key).locking_thread() -> Write_lock_id,

            old(lctx).lock_map_contains(obj_id.view()),
            old(lctx).lock_id_for_obj(obj_id.view()) == old(self).lock_id_by_key(key),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),
            final(self).spec_index(key) == final(self).spec_index(key),

            final(self).spec_index(key).locking_thread() is None,

            wunlock_ensures(old(self).spec_index(key), final(self).spec_index(key)),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).spec_index(key).view(),
                lock_perm.view().lock_id(),
                obj_id.view(),
                old(self).lock_id_by_key(key),
            ),
    {
        let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
        let ret = wunlock(&PPtr::<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>::from_usize(key), Tracked(&mut perm), Tracked(lctx), lock_perm, obj_id);
        proof{
            self.map.borrow_mut().tracked_insert(key, perm);
        }
        return ret;
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,> LockedMap<usize, T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    pub fn wlock_unless_killed(&mut self, key:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: (bool, Option<Tracked<LockPerm>>))
        requires
            old(self).perms_wf(),
            old(self).dom().contains(key),

            // wlock_requires(old(self)[key], old(lctx)),
            old(self).spec_index(key).locked_by(old(lctx)) == false,
            old(lctx).kernel_view_locking_state() is Acquire,

            old(lctx).lock_id_acyclic(old(self).lock_id_by_key(key)),
            old(lctx).obj_id_fresh(obj_id.view()),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            // A (possibly failed) lock attempt never changes the calling
            // thread's identity (see free `wlock_unless_killed`).
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

            ret.0 == false ==> 
            {
                &&&
                old(self).spec_index(key).being_killed() == true
                &&&
                old(self).spec_index(key) == final(self).spec_index(key)
                &&&
                ret.1 is None
                &&&
                final(lctx).lock_maps_equal(old(lctx))
            },
            ret.0 == true ==>{
                &&&                
                old(self).spec_index(key).being_killed() == false
                &&&
                ret.1 is Some
                &&&
                wlock_ensures(old(self).spec_index(key), final(self).spec_index(key), old(self).lock_id_by_key(key), final(lctx).thread_id(), ret.1.unwrap().view())
                &&&
                lock_ensures(old(lctx), final(lctx), old(self).spec_index(key).view(), old(self).lock_id_by_key(key), obj_id.view())
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
            
            old(self).spec_index(key).wlocked_by(old(lctx)),
            old(self).spec_index(key).inv(),

            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(key).locking_thread() -> Write_lock_id,

            old(lctx).lock_map_contains(obj_id.view()),
            old(lctx).lock_id_for_obj(obj_id.view()) == old(self).lock_id_by_key(key),
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), key),

            final(self).spec_index(key).locking_thread() is None,
            old(self).spec_index(key).being_killed() == final(self).spec_index(key).being_killed(),

            wunlock_ensures(old(self).spec_index(key), final(self).spec_index(key)),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).spec_index(key).view(),
                lock_perm.view().lock_id(),
                obj_id.view(),
                old(self).lock_id_by_key(key),
            ),
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
            old.dom().contains(k) && old.spec_index(k).partial_locked_by(lctx)
            ==>
            self.dom().contains(k) && self.spec_index(k) =~= old.spec_index(k)
    }
    proof fn random_step(&mut self, lctx: &LocalContext)
    {
        admit()
    }
}

}

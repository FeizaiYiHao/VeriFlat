use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use std::ops::Index;
use crate::concurrency::*;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArray<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, KGhostT, UGhostT, const N: usize, const HAS_KILL_STATE: bool>{
        array: Array<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, N>,
        
        user_seq: Ghost<Seq<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>,
    }
    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool, const N: usize> LockedArray<T, ROT, KGhostT, UGhostT, N, HAS_KILL_STATE> { 
        pub closed spec fn inv(&self) -> bool{
            &&&
            self.array.wf()
        }
        
        pub closed spec fn user_view(&self) -> Seq<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
            self.user_seq.view()
        }

        pub closed spec fn view(&self) -> Seq<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
            self.array@
        }
        pub open spec fn spec_index(&self, index: usize) -> LockedArrayElement<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>
            recommends
                0 <= index < N,
        {
            LockedArrayElement{
                value:self@[index as int],
                lock_minor: index,
           }
        }
        pub open spec fn unchanged_except(&self, old: &Self, index:usize) -> bool{
            &&&
            forall|i:usize|
                #![auto]
                0 <= i < N && i != index
                ==>
                self[i] == old[i]
        }
        
        pub open spec fn user_view_unchanged(&self, old: &Self) -> bool {
            &&&
            self.user_view() == old.user_view()
        }
        
        pub open spec fn user_view_unchanged_except(&self, old: &Self, index:usize) -> bool {
            &&&
            self.user_view().len() == old.user_view().len()
            &&&
            forall|i:usize|
                #![auto]
                0 <= i < N && i != index
                ==>
                self.user_view()[i as int] == old.user_view()[i as int]
        }


        #[verifier(external_body)]
        pub fn take(&mut self, index:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm:Tracked<&LockPerm>) -> (ret:T)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(lctx),
                old(self)[index]@.is_init(),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == lctx.thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,
            ensures
                final(self).inv(),
                final(self).unchanged_except(old(self), index),
                final(self).user_view_unchanged(old(self)),

                take_ensures(old(self)[index]@, final(self)[index]@),
                
                ret == old(self)[index]@@,
        {
            self.array.ar[index].take(Tracked(lctx), lock_perm)
        } 

        #[verifier(external_body)]
        pub fn put(&mut self, index:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm:Tracked<&LockPerm>, v:T) 
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(lctx),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == lctx.thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,
            ensures
                final(self).inv(),
                final(self).unchanged_except(old(self), index),
                final(self).user_view_unchanged(old(self)),

                put_ensures(old(self)[index]@, final(self)[index]@, v),
        {
            self.array.ar[index].put(Tracked(lctx), lock_perm, v);
        }

        // @Xiangdong comeback
        #[verifier::external_body]
        pub fn borrow<'a,>(&self, index:usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
            requires
                self.inv(),
                0 <= index < N,

                lp@.state() is WriteLock ==> self[index]@.write_lock_perm_match(lp@),
                lp@.state() is ReadLock ==> self[index]@.read_lock_perm_match(lp@), 
            ensures
                ret == self[index]@@,
        {
            self.array.ar.index(index).borrow(lp)
        } 
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const N: usize> LockedArray<T, ROT, KGhostT, UGhostT, N, NO_KILL_STATE>{
        #[verifier(external_body)]
        pub fn wlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret:Tracked<LockPerm>)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index].container_depth() == lock_id@.container,
                old(self)[index].process_depth() == lock_id@.process,
                old(self)[index].lock_major_sat(lock_id@.major),
                old(self)[index].lock_minor() == lock_id@.minor,

                wlock_requires(old(self)[index]@, old(lctx)),
                old(lctx).lock_id_acyclic(lock_id@),
                old(lctx).obj_id_fresh(obj_id@),
            ensures
                final(self).inv(),
                final(self).unchanged_except(old(self), index),
                final(self).user_view_unchanged(old(self)),

                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                wlock_ensures(old(self)[index]@, final(self)[index]@, lock_id@, final(lctx).thread_id(), ret@),
                lock_ensures(old(lctx), final(lctx), final(self)[index]@@, lock_id@, obj_id@),
        {
            self.array.ar[index].wlock_external(Tracked(lctx))
        }

        #[verifier(external_body)]
        pub fn wunlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm:Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(old(lctx)),
                old(self)[index]@.being_killed() == false,

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,

                old(lctx).lock_map().dom().contains(obj_id@),
                old(lctx).lock_map()[obj_id@] == lock_perm@.lock_id(),
            ensures
                final(self).inv(),
                final(self).unchanged_except(old(self), index),
                final(self).user_view_unchanged_except(old(self), index),
                final(self).user_view().spec_index(index as int) == final(self)[index]@,

                final(self)[index]@.locking_thread() is None,

                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                wunlock_ensures(old(self)[index]@, final(self)[index]@),
                unlock_ensures(old(lctx), final(lctx), final(self)[index]@@, lock_perm@.lock_id(), obj_id@),
        {
            self.array.ar[index].wunlock_external(Tracked(lctx), lock_perm);
        }

    }

}

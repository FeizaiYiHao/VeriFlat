use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use std::ops::Index;
use crate::concurrency::*;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArray<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const N: usize, const HasKillState: bool>{
        array: Array<RwLock<T, ROT, GhostT, HasKillState>, N>,
        
        user_seq: Ghost<Seq<RwLock<T, ROT, GhostT, HasKillState>>>,
    }
    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const HasKillState: bool, const N: usize> LockedArray<T, ROT, GhostT, N, HasKillState> { 
        pub closed spec fn inv(&self) -> bool{
            &&&
            self.array.wf()
        }
        
        pub closed spec fn user_view(&self) -> Seq<RwLock<T, ROT, GhostT, HasKillState>>{
            self.user_seq.view()
        }

        pub closed spec fn view(&self) -> Seq<RwLock<T, ROT, GhostT, HasKillState>>{
            self.array@
        }
        pub open spec fn spec_index(&self, index: usize) -> LockedArrayElement<T, ROT, GhostT, HasKillState>
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
                self.inv(),
                self.unchanged_except(old(self), index),
                self.user_view_unchanged(old(self)),

                take_ensures(old(self)[index]@, self[index]@),
                
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
                self.inv(),
                self.unchanged_except(old(self), index),
                self.user_view_unchanged(old(self)),

                put_ensures(old(self)[index]@, self[index]@, v),
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
            unsafe{
                self.array.ar.index(index).borrow(lp)
            }
        } 
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, GhostT, const N: usize> LockedArray<T, ROT, GhostT, N, NO_KILL_STATE>{
        #[verifier(external_body)]
        pub fn wlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret:Tracked<LockPerm>)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index].container_depth() == lock_id@.container,
                old(self)[index].process_depth() == lock_id@.process,
                old(self)[index].lock_major_sat(lock_id@.major),
                old(self)[index].lock_minor() == lock_id@.minor,

                wlock_requires(old(self)[index]@, old(lctx)),
                old(lctx).lock_id_acyclic(lock_id@),
            ensures
                self.inv(),
                self.unchanged_except(old(self), index),
                self.user_view_unchanged(old(self)),

                wlock_ensures(old(self)[index]@, self[index]@, lock_id@, lctx.thread_id(), ret@),
                lock_ensures(old(lctx), lctx, self[index]@@, lock_id@),
        {
            self.array.ar[index].wlock_external(Tracked(lctx))
        }

        #[verifier(external_body)]
        pub fn wunlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm:Tracked<LockPerm>) 
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(old(lctx)),
                old(self)[index]@.being_killed() == false,

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,
            ensures
                self.inv(),
                self.unchanged_except(old(self), index),
                self.user_view_unchanged_except(old(self), index),
                self.user_view().spec_index(index as int) == self[index]@,

                self[index]@.locking_thread() is None,

                wunlock_ensures(old(self)[index]@, self[index]@),
                unlock_ensures(old(lctx), lctx, self[index]@@, lock_perm@.lock_id()),
        {
            self.array.ar[index].wunlock_external(Tracked(lctx), lock_perm);
        }

    }

    // impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool, const N: usize> Step for LockedArray<T, HasKillState, N>{
    //     open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
    //         &&&
    //         forall|i:usize|
    //             #![auto]
    //             0 <= i < N && self[i]@.locked_by(lctx) == false
    //             ==>
    //             self[i]@.being_killed_by(lctx) == false
    //             &&
    //             self[i]@.serial_num() == lctx.locking_serial_num()
    //     }
    //     proof fn random_step(&mut self, lctx: &LocalContext)
    //     {
    //         admit()
    //     }
    // }

}
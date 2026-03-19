use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::concurrency::*;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArrayElement<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool>{
        pub value: RwLock<T, HasKillState>,
        pub lock_minor: LockMinorId, 
    }
    impl<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool> LockedArrayElement<T, HasKillState>{
        pub open spec fn view(&self) -> RwLock<T, HasKillState>{
            self.value
        }
        pub open spec fn value(&self) -> RwLock<T, HasKillState>{
            self.value
        }
    }

    impl<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool> LockMinorTrait for LockedArrayElement<T, HasKillState>{
        open spec fn lock_minor(&self) -> LockMinorId {
            self.lock_minor
        }
    }

    impl<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool> LockMajorTrait for LockedArrayElement<T, HasKillState>{
        open spec fn inv(&self) -> bool {
            self@.inv()
        }
        open spec fn lock_major_1(&self) -> LockMajorId {
            self@@.lock_major_1()
        }
    
        open spec fn lock_major_2(&self) -> LockMajorId {
            self@@.lock_major_2()
        }
    
        open spec fn lock_major_3(&self) -> LockMajorId {
            self@@.lock_major_3()
        }
    
        open spec fn lock_major_default(&self) -> LockMajorId {
            self@@.lock_major_default()
        }
    
        open spec fn lock_major_1_predicate(&self) -> bool {
            self@@.lock_major_1_predicate()
        }
    
        open spec fn lock_major_2_predicate(&self) -> bool {
            self@@.lock_major_2_predicate()
        }
    
        open spec fn lock_major_3_predicate(&self) -> bool {
            self@@.lock_major_3_predicate()
        }
    
        open spec fn lock_major_default_predicate(&self) -> bool {
            self@@.lock_major_default_predicate()
        }
    }
    
    impl<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool> LockOwnerIdTrait for LockedArrayElement<T, HasKillState>{
        open spec fn container_depth(&self) -> LockOwnerId {
            self.view().view().container_depth()
        }
    
        open spec fn process_depth(&self) -> LockOwnerId {
            self.view().view().process_depth()
        }
    }
    
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArray<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool, const N: usize>{
        array: Array<RwLock<T,HasKillState>, N>,
    }
    impl<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool, const N: usize> LockedArray<T, HasKillState, N> { 
        pub closed spec fn inv(&self) -> bool{
            &&&
            self.array.wf()
        }
        
        pub closed spec fn view(&self) -> Seq<RwLock<T, HasKillState>>{
            self.array@
        }
        pub open spec fn spec_index(&self, index: usize) -> LockedArrayElement<T, HasKillState>
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

                put_ensures(old(self)[index]@, self[index]@, v),
        {
            self.array.ar[index].put(Tracked(lctx), lock_perm, v);
        } 
    }

    impl<T:LockMajorTrait + LockOwnerIdTrait, const N: usize> LockedArray<T, false, N>{
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

                wlock_ensures(old(self)[index]@, self[index]@, lock_id@, lctx.thread_id(), ret@),
                lock_ensures(old(lctx), lctx, lock_id@),
        {
            self.array.ar[index].wlock_external(Tracked(lctx), Ghost(lock_id@.major))
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

                self[index]@.locking_thread() is None,

                wunlock_ensures(old(self)[index]@, self[index]@),
                unlock_ensures(old(lctx), lctx, lock_perm@.lock_id()),
        {
            self.array.ar[index].wunlock_external(Tracked(lctx), lock_perm);
        }

    }

    impl<T:LockMajorTrait + LockOwnerIdTrait, const HasKillState: bool, const N: usize> Step for LockedArray<T, HasKillState, N>{
        open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
            &&&
            forall|i:usize|
                #![auto]
                0 <= i < N && self[i]@.locked_by(lctx) == false
                ==>
                self[i]@.being_killed_by(lctx) == false
                &&
                self[i]@.serial_num() == lctx.locking_serial_num()
        }
        proof fn random_step(&mut self, lctx: &LocalContext)
        {
            admit()
        }
    }

}
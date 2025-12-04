use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArrayElement<T:LockedUtil + LockOwnerIdUtil, const HasKillState: bool>{
        pub value: RwLock<T, HasKillState>,
        pub lock_minor: LockMinorId, 
    }
    impl<T:LockedUtil + LockOwnerIdUtil, const HasKillState: bool> LockedArrayElement<T, HasKillState>{
        pub open spec fn lock_minor(&self) -> LockMinorId{
            self.lock_minor
        }
        pub open spec fn view(&self) -> RwLock<T, HasKillState>{
            self.value
        }
        pub open spec fn value(&self) -> RwLock<T, HasKillState>{
            self.value
        }
    }

    impl<T:LockedUtil + LockOwnerIdUtil, const HasKillState: bool> LockedUtil for LockedArrayElement<T, HasKillState>{
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

    #[verifier::reject_recursive_types(T)]
    pub struct LockedArray<T:LockedUtil + LockOwnerIdUtil, const HasKillState: bool, const N: usize>{
        array: Array<RwLock<T,HasKillState>, N>,
    }
    impl<T:LockedUtil + LockOwnerIdUtil, const HasKillState: bool, const N: usize> LockedArray<T, HasKillState, N> { 
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
        pub fn wlock(&mut self, index:usize, Tracked(lock_manager): Tracked<&mut LockManager>, lock_id: Ghost<LockId>) -> (ret:Tracked<LockPerm>)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index].lock_major_sat(lock_id@.major),
                old(self)[index].lock_minor() == lock_id@.minor,

                wlock_requires(old(self)[index]@, old(lock_manager)),
                old(lock_manager).lock_id_valid(lock_id@),
            ensures
                self.inv(),
                self.unchanged_except(old(self), index),

                wlock_ensures(old(self)[index]@, self[index]@, lock_id@, lock_manager.thread_id(), ret@),
                lock_ensures(old(lock_manager), lock_manager, lock_id@),
        {
            self.array.ar[index].wlock(Tracked(lock_manager), Ghost(lock_id@.major))
        }

        #[verifier(external_body)]
        pub fn wunlock(&mut self, index:usize, Tracked(lock_manager): Tracked<&mut LockManager>, lock_perm:Tracked<LockPerm>) 
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(old(lock_manager)),
                old(self)[index]@.being_killed() == false,
                old(self)[index].inv(),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lock_manager).thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,
            ensures
                self.inv(),
                self.unchanged_except(old(self), index),

                self[index]@.locking_thread() is None,

                wunlock_ensures(old(self)[index]@, self[index]@),
                unlock_ensures(old(lock_manager), lock_manager, lock_perm@.lock_id()),
        {
            self.array.ar[index].wunlock(Tracked(lock_manager), lock_perm);
        }

        #[verifier(external_body)]
        pub fn take(&mut self, index:usize, Tracked(lock_manager): Tracked<&LockManager>, lock_perm:Tracked<&LockPerm>) -> (ret:T)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(lock_manager),
                old(self)[index]@.is_init(),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == lock_manager.thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,
            ensures
                self.inv(),
                self.unchanged_except(old(self), index),

                take_ensures(old(self)[index]@, self[index]@),
                
                ret == old(self)[index]@@,
        {
            self.array.ar[index].take(Tracked(lock_manager), lock_perm)
        } 

        #[verifier(external_body)]
        pub fn put(&mut self, index:usize, Tracked(lock_manager): Tracked<&LockManager>, lock_perm:Tracked<&LockPerm>, v:T) 
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(lock_manager),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == lock_manager.thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,
            ensures
                self.inv(),
                self.unchanged_except(old(self), index),

                put_ensures(old(self)[index]@, self[index]@, v),
        {
            self.array.ar[index].put(Tracked(lock_manager), lock_perm, v);
        } 
    }

}
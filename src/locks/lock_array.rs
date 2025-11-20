use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;

use super::*;
use crate::primitive::*;

verus! {

    impl<T: LockInv, const N: usize, const LockMajor: LockMajorId> Array<RwLock<T, LockMajor>, N> { 
        
        #[verifier(external_body)]
        pub fn wlock(&mut self, index:usize, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret:Tracked<LockPerm>)
            requires
                old(self).wf(),
                0 <= index < N,

                old(self)[index].locked(old(lock_manager).thread_id()) == false,
                old(lock_manager).lock_seq().len() == 0 ||
                    old(self)[index].lock_id().greater(old(lock_manager).lock_seq().last()),
            ensures
                self.wf(),
                forall|i:usize|
                    #![auto]
                    0 <= i < N && i != index
                    ==>
                    self[i] === old(self)[i],

                self[index].rlocked_by(lock_manager.thread_id()) == false,
                self[index].wlocked_by(lock_manager.thread_id()),
                self[index].lock_id() == old(self)[index].lock_id(),
                old(self)[index].released() == false ==> self[index].view() == old(self)[index].view(),
                self[index]@.inv(),
                old(self)[index].is_init(),
                self[index].is_init() == old(self)[index].is_init(),

                lock_manager.thread_id() == old(lock_manager).thread_id(),
                lock_manager.lock_seq() == old(lock_manager).lock_seq().push(self[index].lock_id()),
                old(lock_manager).wf() ==> lock_manager.wf(),
                ret@.thread_id() == lock_manager.thread_id(),

                ret@.state == LockState::WriteLock,
                ret@.lock_id() == self[index].lock_id(),

                self[index].modified() == false,
        {
            self.ar[index].wlock(Tracked(lock_manager))
        }

        #[verifier(external_body)]
        pub fn wunlock(&mut self, index:usize, Tracked(lock_manager): Tracked<&mut LockManager>, lp:Tracked<LockPerm>) 
            requires
                old(self).wf(),
                0 <= index < N,

                old(self)[index].locked(old(lock_manager).thread_id()),
                old(self)[index].inv(),

                lp@.thread_id() == old(lock_manager).thread_id(),
                lp@.state == LockState::WriteLock,
                lp@.lock_id() == old(self)[index].lock_id(),

                old(lock_manager).lock_seq().contains(old(self)[index].lock_id())
            ensures
                self.wf(),
                forall|i:usize|
                    #![auto]
                    0 <= i < N && i != index
                    ==>
                    self[i] === old(self)[i],

                self[index].rlocked_by(lock_manager.thread_id()) == false,
                self[index].wlocked_by(lock_manager.thread_id()) == false,
                self[index].lock_id() == old(self)[index].lock_id(),
                self[index].inv(),
                self[index].view() == old(self)[index].view(),
                self[index].is_init() == old(self)[index].is_init(),

                lock_manager.thread_id() == old(lock_manager).thread_id(),
                lock_manager.lock_seq() === old(lock_manager).lock_seq().remove_value(self[index].lock_id()),
                old(lock_manager).wf() ==> lock_manager.wf(),
        {
            self.ar[index].wunlock(Tracked(lock_manager), lp);
        }

        #[verifier(external_body)]
        pub fn take(&mut self, index:usize, lp:Tracked<&LockPerm>) -> (ret:T)
            requires
                old(self).wf(),
                0 <= index < N,

                lp@.state == LockState::WriteLock,
                lp@.lock_id() == old(self)[index].lock_id(),
                old(self)[index].is_init(),
            ensures
                self.wf(),
                forall|i:usize|
                    #![auto]
                    0 <= i < N && i != index
                    ==>
                    self[i] === old(self)[i],

                self[index].reading_thread() == old(self)[index].reading_thread(),
                self[index].writing_thread() == old(self)[index].writing_thread(),
                self[index].lock_id() == old(self)[index].lock_id(),
                self[index].is_init() == false,
                ret == old(self)[index].view(),
        {
            self.ar[index].take(lp)
        } 

        #[verifier(external_body)]
        pub fn put(&mut self, index:usize, lp:Tracked<&LockPerm>, v:T) 
            requires
                old(self).wf(),
                0 <= index < N,

                lp@.state == LockState::WriteLock,
                lp@.lock_id() == old(self)[index].lock_id(),
                old(self)[index].is_init() == false,
            ensures
                self.wf(),
                forall|i:usize|
                    #![auto]
                    0 <= i < N && i != index
                    ==>
                    self[i] === old(self)[i],

                self[index].reading_thread() == old(self)[index].reading_thread(),
                self[index].writing_thread() == old(self)[index].writing_thread(),
                self[index].lock_id() == old(self)[index].lock_id(),
                self[index].view() == v,

                self[index].modified() == true,

                self[index].is_init(),
        {
            self.ar[index].put(lp, v);
        } 
    }

}
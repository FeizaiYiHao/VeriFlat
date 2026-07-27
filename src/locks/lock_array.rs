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
        pub closed spec fn array_wf(&self) -> bool{
            &&&
            self.array.wf()
        }

        pub open spec fn inv(&self) -> bool{
            &&&
            self.array_wf()
            &&&
            self.view().len() == N
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
                #![trigger self[i]]
                0 <= i < N && i != index
                ==>
                self[i] === old[i]
        }

        /// Bridge between `spec_index(i).value` and `view()[i]`.

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
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

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
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

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

        #[verifier::external_body]
        pub fn borrow_mut<'a>(&'a mut self, index:usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self)[index]@.wlocked_by(lctx),
                old(self)[index]@.is_init(),

                lp@.state() is WriteLock,
                lp@.thread_id() == lctx.thread_id(),
                lp@.lock_id() == old(self)[index]@.locking_thread()->Write_lock_id,
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

                // Lock state of the touched entry is preserved.
                final(self)[index]@.is_init(),
                final(self)[index]@.view_rodata() == old(self)[index]@.view_rodata(),
                final(self)[index]@.view_kernel_ghost() == old(self)[index]@.view_kernel_ghost(),
                final(self)[index]@.view_user_ghost() == old(self)[index]@.view_user_ghost(),
                final(self)[index]@.locking_thread() == old(self)[index]@.locking_thread(),
                final(self)[index]@.being_killed() == old(self)[index]@.being_killed(),

                // The `&mut T` linkage.
                *ret == old(self)[index]@@,
                final(self)[index]@@ == *final(ret),
        {
            self.array.ar[index].borrow_mut(Tracked(lctx), lp)
        } 
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const N: usize> LockedArray<T, ROT, KGhostT, UGhostT, N, NO_KILL_STATE>{
        pub open spec fn lock_id_by_index(&self, index:usize) -> LockId
            recommends
                0 <= index < N,
        {
            self.spec_index(index).lock_id()
        }
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const N: usize> LockedArray<T, ROT, KGhostT, UGhostT, N, NO_KILL_STATE>{
        #[verifier(external_body)]
        pub fn wlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret:Tracked<LockPerm>)
            requires
                old(self).inv(),
                0 <= index < N,

                wlock_requires(old(self)[index]@, old(lctx)),
                old(lctx).lock_id_acyclic(old(self).lock_id_by_index(index)),
                old(lctx).obj_id_fresh(obj_id@),
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                wlock_ensures(old(self)[index]@, final(self)[index]@, old(self).lock_id_by_index(index), final(lctx).thread_id(), ret@),
                lock_ensures(old(lctx), final(lctx), final(self)[index]@@, old(self).lock_id_by_index(index), obj_id@),
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

                unlock_requires::<T>(old(lctx)),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self)[index]@.locking_thread() -> Write_lock_id,

                old(lctx).lock_map_contains(obj_id@),
                old(lctx).lock_id_for_obj(obj_id@) == old(self).lock_id_by_index(index),
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

                final(self)[index]@.locking_thread() is None,

                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // it contradicts `unlock_ensures` (which transitions Acquire →
                // Release), making the postcondition `false` in an Acquire
                // section. `unlock_ensures` is the source of truth for the phase
                // transition (matches `LockedMap::wunlock`). user_view is
                // separately preserved by unlock_ensures.
                wunlock_ensures(old(self)[index]@, final(self)[index]@),
                unlock_ensures(old(lctx), final(lctx), final(self)[index]@@, lock_perm@.lock_id(), obj_id@),
        {
            self.array.ar[index].wunlock_external(Tracked(lctx), lock_perm);
        }

    }

}

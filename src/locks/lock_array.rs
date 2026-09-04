use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use std::ops::Index;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArray<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const N: usize, const HAS_KILL_STATE: bool>{
        array: Array<RwLock<T, ROT, GhostT, HAS_KILL_STATE>, N>,
        
        user_seq: Ghost<Seq<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>,
    }
    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT,
        const HAS_KILL_STATE: bool, const N: usize>
        LockedArray<T, ROT, GhostT, N, HAS_KILL_STATE> {
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

        pub closed spec fn view(&self) -> Seq<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>{
            self.array.view()
        }
        pub open spec fn spec_index(&self, index: usize) -> LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>
            recommends
                0 <= index < N,
        {
            LockedArrayElement{
                value:self.view().spec_index(index as int),
                lock_minor: index,
           }
        }

        pub open spec fn entries_unchanged_except(&self, old: &Self, index: usize) -> bool {
            forall|i:usize|
                #![trigger self.spec_index(i)]
                #![trigger old.spec_index(i)]
                index_valid(N, i) && i != index
                ==>
                self.spec_index(i) == old.spec_index(i)
        }

        pub open spec fn unchanged_except(&self, old: &Self, index: usize) -> bool {
            forall|i: usize|
                #![trigger self.spec_index(i)]
                #![trigger old.spec_index(i)]
                index_valid(N, i) ==> {
                    &&& (i != index ==> self.spec_index(i) == old.spec_index(i))
                    &&& self.spec_index(i).view().view()
                            == old.spec_index(i).view().view()
                }
        }

        #[verifier::opaque]
        pub open spec fn typed_lock_map_aligned(
            &self,
            held_locks: Map<usize, TypedHeldLock>,
            thread_id: LockThreadId,
        ) -> bool {
            &&& (forall|index: usize|
                #![trigger held_locks.dom().contains(index)]
                #![trigger self.spec_index(index).view().locked_by_thread(thread_id)]
                held_locks.dom().contains(index) == {
                    &&& index_valid(N, index)
                    &&& self.spec_index(index).view().locked_by_thread(thread_id)
                }
                && (held_locks.dom().contains(index) ==>
                    held_locks.index(index).lock_id == self.spec_index(index).lock_id()))
            &&& (forall|index: usize|
                #![trigger typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Read)]
                #![trigger self.spec_index(index).view().rlocked_by_thread(thread_id)]
                typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Read) == {
                    &&& index_valid(N, index)
                    &&& self.spec_index(index).view().rlocked_by_thread(thread_id)
                })
            &&& (forall|index: usize|
                #![trigger typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write)]
                #![trigger self.spec_index(index).view().wlocked_by_thread(thread_id)]
                typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write) == {
                    &&& index_valid(N, index)
                    &&& self.spec_index(index).view().wlocked_by_thread(thread_id)
                })
        }

        /// Bridge between `spec_index(i).value` and `view()[i]`.
        pub proof fn lemma_view_index(&self, index: usize)
            requires
                0 <= index < N,
            ensures
                self.view().spec_index(index as int) == self.spec_index(index).value,
        {
        }

        #[verifier(external_body)]
        pub fn take(&mut self, index:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm:Tracked<&LockPerm>) -> (ret:T)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self).spec_index(index).view().wlocked_by(lctx),
                old(self).spec_index(index).view().is_init(),

                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == lctx.thread_id(),
                lock_perm.view().lock_id() == old(self).spec_index(index).view().locking_thread() -> Write_lock_id,
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).entries_unchanged_except(old(self), index),

                take_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view()),
                final(self).spec_index(index).view().wlocked_by(lctx),

                ret == old(self).spec_index(index).view().view(),
        {
            self.array.ar[index].take(Tracked(lctx), lock_perm)
        }

        #[verifier(external_body)]
        pub fn put(&mut self, index:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm:Tracked<&LockPerm>, v:T)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self).spec_index(index).view().wlocked_by(lctx),

                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == lctx.thread_id(),
                lock_perm.view().lock_id() == old(self).spec_index(index).view().locking_thread() -> Write_lock_id,
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).entries_unchanged_except(old(self), index),

                put_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view(), v),
                final(self).spec_index(index).view().wlocked_by(lctx),
        {
            self.array.ar[index].put(Tracked(lctx), lock_perm, v);
        }

        // @Xiangdong comeback
        #[verifier::external_body]
        pub fn borrow<'a,>(&self, index:usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
            requires
                self.inv(),
                0 <= index < N,

                lp.view().state() is WriteLock ==> self.spec_index(index).view().write_lock_perm_match(lp.view()),
                lp.view().state() is ReadLock ==> self.spec_index(index).view().read_lock_perm_match(lp.view()),
            ensures
                ret == self.spec_index(index).view().view(),
        {
            self.array.ar.index(index).borrow(lp)
        }

        #[verifier::external_body]
        pub fn borrow_mut<'a>(&'a mut self, index:usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self).spec_index(index).view().wlocked_by(lctx),
                old(self).spec_index(index).view().is_init(),

                lp.view().state() is WriteLock,
                lp.view().thread_id() == lctx.thread_id(),
                lp.view().lock_id() == old(self).spec_index(index).view().locking_thread()->Write_lock_id,
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).entries_unchanged_except(old(self), index),

                // Lock state of the touched entry is preserved.
                final(self).spec_index(index).view().is_init(),
                final(self).spec_index(index).view().wlocked_by(lctx),
                final(self).spec_index(index).view().view_rodata() == old(self).spec_index(index).view().view_rodata(),
                final(self).spec_index(index).view().view_ghost() == old(self).spec_index(index).view().view_ghost(),
                final(self).spec_index(index).view().locking_thread() == old(self).spec_index(index).view().locking_thread(),
                final(self).spec_index(index).view().being_killed() == old(self).spec_index(index).view().being_killed(),

                // The `&mut T` linkage.
                *ret == old(self).spec_index(index).view().view(),
                final(self).spec_index(index).view().view() == *final(ret),
        {
            self.array.ar[index].borrow_mut(Tracked(lctx), lp)
        }

        pub fn borrow_mut_typed<'a>(
            &'a mut self,
            index: usize,
            Ghost(held_locks): Ghost<Map<usize, TypedHeldLock>>,
            Tracked(lctx): Tracked<&LocalContext>,
            lp: Tracked<&'a LockPerm>,
        ) -> (ret: &'a mut T)
            requires
                old(self).inv(),
                0 <= index < N,
                old(self).typed_lock_map_aligned(held_locks, lctx.thread_id()),
                old(self).spec_index(index).view().is_init(),
                lp.view().state() is WriteLock,
                lp.view().thread_id() == lctx.thread_id(),
                old(self).spec_index(index).view().write_lock_perm_match(lp.view()),
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).entries_unchanged_except(old(self), index),
                final(self).spec_index(index).view().is_init(),
                final(self).spec_index(index).view().wlocked_by(lctx),
                final(self).spec_index(index).view().write_lock_perm_match(lp.view()),
                final(self).spec_index(index).view().view_rodata() == old(self).spec_index(index).view().view_rodata(),
                final(self).spec_index(index).view().view_ghost() == old(self).spec_index(index).view().view_ghost(),
                final(self).spec_index(index).view().locking_thread() == old(self).spec_index(index).view().locking_thread(),
                final(self).spec_index(index).view().being_killed() == old(self).spec_index(index).view().being_killed(),
                *ret == old(self).spec_index(index).view().view(),
                final(self).spec_index(index).view().view() == *final(ret),
                final(self).typed_lock_map_aligned(
                    held_locks.insert(index, TypedHeldLock {
                        lock_id: final(self).spec_index(index).lock_id(),
                        mode: held_locks.index(index).mode,
                    }),
                    lctx.thread_id(),
                ),
                held_locks.index(index).lock_id == old(self).spec_index(index).lock_id(),
                typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write),
                final(self).spec_index(index).lock_id() == old(self).spec_index(index).lock_id()
                    ==> final(self).typed_lock_map_aligned(held_locks, lctx.thread_id()),
        {
            proof {
                assert(typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write)) by { reveal(LockedArray::typed_lock_map_aligned); };
                reveal(LockedArray::typed_lock_map_aligned);
            }
            self.borrow_mut(index, Tracked(lctx), lp)
        }
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT,
        const N: usize>
        LockedArray<T, ROT, GhostT, N, NO_KILL_STATE>{
        pub open spec fn lock_id_by_index(&self, index:usize) -> LockId
            recommends
                0 <= index < N,
        {
            self.spec_index(index).lock_id()
        }
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT,
        const N: usize>
        LockedArray<T, ROT, GhostT, N, NO_KILL_STATE>{
        #[verifier(external_body)]
        pub fn wlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret:Tracked<LockPerm>)
            requires
                old(self).inv(),
                0 <= index < N,

                wlock_requires(old(self).spec_index(index).view(), old(lctx)),
                old(lctx).lock_id_acyclic(old(self).lock_id_by_index(index)),
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                wlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view(), old(self).lock_id_by_index(index), final(lctx), ret.view()),
                lock_ensures(old(lctx), final(lctx),
                    final(self).spec_index(index).view().view(),
                    old(self).lock_id_by_index(index), obj_id.view()),
        {
            self.array.ar[index].wlock_external(Tracked(lctx))
        }

        #[verifier(external_body)]
        pub fn wunlock(&mut self, index:usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm:Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
            requires
                old(self).inv(),
                0 <= index < N,

                old(self).spec_index(index).view().wlocked_by(old(lctx)),
                old(self).spec_index(index).view().being_killed() == false,

                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).spec_index(index).view().locking_thread() -> Write_lock_id,

                old(lctx).lock_id_set().contains((
                    old(self).lock_id_by_index(index), obj_id.view())),
            ensures
                final(self).inv(),
                final(self).view().len() == old(self).view().len(),
                final(self).unchanged_except(old(self), index),

                final(self).spec_index(index).view().locking_thread() is None,
                final(self).lock_id_by_index(index) == old(self).lock_id_by_index(index),

                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // it contradicts `unlock_ensures` (which transitions Acquire →
                // Release), making the postcondition `false` in an Acquire
                // section. `unlock_ensures` is the source of truth for the phase
                // transition (matches `LockedMap::wunlock`). user_view is
                // separately preserved by unlock_ensures.
                wunlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view()),
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).spec_index(index).view().view(),
                    lock_perm.view().lock_id(),
                    obj_id.view(),
                    old(self).lock_id_by_index(index),
                ),
        {
            self.array.ar[index].wunlock_external(Tracked(lctx), lock_perm);
        }

    }

}

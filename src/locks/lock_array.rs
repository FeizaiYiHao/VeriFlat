use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::{define::*};
use core::sync::atomic::*;
use core::ops::Index;

use super::*;
use crate::primitive::*;
use crate::cpu::Cpu;
use crate::page::Page;

verus! {
/// Storage of a lock array's cells: the cells' lock objects and their well-formedness.
pub trait LockStorage<T, ROT, GhostT, const N: usize, const HAS_KILL_STATE: bool> {
    spec fn view(&self) -> Seq<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>;
    spec fn wf(&self) -> bool;
}

/// Inline storage: the cells live inside the array value.
impl<T, ROT, GhostT, const N: usize, const HAS_KILL_STATE: bool> LockStorage<T, ROT, GhostT, N, HAS_KILL_STATE> for Array<LockCell<T, ROT, GhostT, HAS_KILL_STATE>, N> {
    open spec fn view(&self) -> Seq<LockCell<T, ROT, GhostT, HAS_KILL_STATE>> { self.seq.view() }
    open spec fn wf(&self) -> bool { self.seq.view().len() == N }
}

/// Address of cell `i` of a lock array of `E` cells that starts at `base`.
pub uninterp spec fn lock_cell_addr<E>(base: usize, i: int) -> usize;

/// TCB: cell `i` of a lock array of `E` cells lies `i` cells past `base`.
#[verifier::external_body]
pub fn lock_cell_addr_exec<E>(base: usize, i: usize) -> (ret: usize)
    ensures
        ret == lock_cell_addr::<E>(base, i as int),
{
    base + i * core::mem::size_of::<E>()
}

/// A lock type whose cells live in one static region outside every lock value: the region's first cell address.
pub trait TokenCellBase {
    spec fn cell_base_spec() -> usize;
    fn cell_base() -> (ret: usize)
        ensures
            ret == Self::cell_base_spec();
}

/// Token storage: the cells live outside the array value, from the lock type's `TokenCellBase` address on, and are
/// reached only through raw addresses; the array holds one points-to token per cell and no runtime bytes.
#[verifier::reject_recursive_types(T)]
pub struct TokenCells<T, ROT, GhostT, const N: usize, const HAS_KILL_STATE: bool> {
    pub perms: Tracked<Map<int, LockObjPerm<T, ROT, GhostT, HAS_KILL_STATE>>>,
}

impl<T, ROT, GhostT, const N: usize, const HAS_KILL_STATE: bool> LockStorage<T, ROT, GhostT, N, HAS_KILL_STATE> for TokenCells<T, ROT, GhostT, N, HAS_KILL_STATE>
    where LockCell<T, ROT, GhostT, HAS_KILL_STATE>: TokenCellBase {
    open spec fn view(&self) -> Seq<LockCell<T, ROT, GhostT, HAS_KILL_STATE>> { Seq::new(N as nat, |i: int| self.perms.view().index(i).value()) }
    open spec fn wf(&self) -> bool {
        // one token per cell 0..N
        &&& forall|i: int|
            #![trigger self.perms.view().dom().contains(i)]
            self.perms.view().dom().contains(i) <==> 0 <= i < N
        // each token is the initialized cell `i` past the lock type's `TokenCellBase` address
        &&& forall|i: int|
            #![trigger self.perms.view().dom().contains(i)]
            #![trigger self.perms.view().index(i)]
            self.perms.view().dom().contains(i) ==> {
                &&& self.perms.view().index(i).is_init()
                &&& self.perms.view().index(i).addr()
                    == lock_cell_addr::<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>(LockCell::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base_spec(), i)
            }
    }
}

/// A lock array over inline (`S` default) or token storage; both expose the same cell sequence.
#[verifier::reject_recursive_types(T)]
pub struct LockedArray<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const N: usize, const HAS_KILL_STATE: bool,
    S = Array<LockCell<T, ROT, GhostT, HAS_KILL_STATE>, N>> {
    pub(crate) storage: S,
    user_seq: Ghost<Seq<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>>,
}
impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const HAS_KILL_STATE: bool, const N: usize, S: LockStorage<T, ROT, GhostT, N, HAS_KILL_STATE>>
    LockedArray<T, ROT, GhostT, N, HAS_KILL_STATE, S> {
    pub closed spec fn array_wf(&self) -> bool { self.storage.wf() }

    /// The storage is well formed and exposes exactly `N` cells.
    pub open spec fn inv(&self) -> bool {
        &&& self.array_wf()
        // exported: `array_wf` and `view` are closed
        &&& self.view().len() == N
    }

    pub closed spec fn view(&self) -> Seq<LockCell<T, ROT, GhostT, HAS_KILL_STATE>> { self.storage.view() }
    pub open spec fn spec_index(&self, index: usize) -> LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>
        recommends
            0 <= index < N,
    {
        LockedArrayElement { value: self.view().spec_index(index as int), lock_minor: index }
    }

    #[verifier::inline]
    pub open spec fn entries_unchanged_except(&self, old: &Self, index: usize) -> bool {
        forall|i: usize| #![trigger self.spec_index(i)] index_valid(N, i) && i != index ==> self.spec_index(i) == old.spec_index(i)
    }

    pub open spec fn unchanged_except(&self, old: &Self, index: usize) -> bool {
        forall|i: usize|
            #![trigger self.spec_index(i)]
            #![trigger old.spec_index(i)]
            index_valid(N, i) ==> {
                &&& (i != index ==> self.spec_index(i) == old.spec_index(i))
                &&& self.spec_index(i).view().view() == old.spec_index(i).view().view()
            }
    }

    #[verifier::opaque]
    pub open spec fn typed_lock_map_aligned(&self, held_locks: Map<usize, TypedHeldLock>, thread_id: LockThreadId) -> bool {
        &&& (forall|index: usize|
            #![trigger held_locks.dom().contains(index)]
            #![trigger self.spec_index(index).view().locked_by_thread(thread_id)]
            held_locks.dom().contains(index) == {
                &&& index_valid(N, index)
                &&& self.spec_index(index).view().locked_by_thread(thread_id)
            }
            && (held_locks.dom().contains(index) ==> held_locks.index(index).lock_id == self.spec_index(index).lock_id()))
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
    pub proof fn view_index_eq_element_value(&self)
        ensures
            forall|i: int| 0 <= i < N ==> #[trigger] self.view().spec_index(i) == self.spec_index(i as usize).value,
    {
    }

    pub open spec fn lock_id_by_index(&self, index: usize) -> LockId
        recommends
            0 <= index < N,
    {
        self.spec_index(index).lock_id()
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const HAS_KILL_STATE: bool, const N: usize> LockedArray<T, ROT, GhostT, N, HAS_KILL_STATE> {
    pub fn from_array(array: Array<LockCell<T, ROT, GhostT, HAS_KILL_STATE>, N>) -> (ret: Self)
        requires
            array.wf(),
        ensures
            ret.inv(),
            ret.view() == array.view(),
    {
        Self { user_seq: Ghost(array.view()), storage: array }
    }

    // @Xiangdong comeback
    #[verifier::external_body]
    pub fn borrow<'a,>(&self, index: usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.inv(),
            0 <= index < N,
            self.spec_index(index).view().is_init(),
            lp.view().state() is WriteLock ==> self.spec_index(index).view().write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.spec_index(index).view().read_lock_perm_match(lp.view()),
        ensures
            ret == self.spec_index(index).view().view(),
    {
        self.storage.ar.index(index).borrow(lp)
    }

    pub fn borrow_typed<'a>(&self, index: usize, Ghost(held_locks): Ghost<Map<usize, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.inv(),
            index_valid(N, index),
            self.spec_index(index).view().is_init(),
            self.typed_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock ==> lock_perm.view().lock_id() == self.spec_index(index).view().locking_thread()->Write_lock_id,
            lock_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Read),
            lock_perm.view().state() is ReadLock ==> self.spec_index(index).view().locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), lock_perm.view().lock_id()),
        ensures
            ret == self.spec_index(index).view().view(),
    {
        assert({
            &&& lock_perm.view().state() is WriteLock ==> self.spec_index(index).view().write_lock_perm_match(lock_perm.view())
            &&& lock_perm.view().state() is ReadLock ==> self.spec_index(index).view().read_lock_perm_match(lock_perm.view())
        }) by { reveal(LockedArray::typed_lock_map_aligned); };
        self.borrow(index, lock_perm)
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const HAS_KILL_STATE: bool, const N: usize>
    LockedArray<T, ROT, GhostT, N, HAS_KILL_STATE, TokenCells<T, ROT, GhostT, N, HAS_KILL_STATE>> where LockCell<T, ROT, GhostT, HAS_KILL_STATE>: TokenCellBase {
    pub fn from_token_cells(cells: TokenCells<T, ROT, GhostT, N, HAS_KILL_STATE>) -> (ret: Self)
        requires
            cells.wf(),
        ensures
            ret.inv(),
            ret.view() == cells.view(),
    {
        Self { user_seq: Ghost(cells.view()), storage: cells }
    }

    pub fn set_ghost(&mut self, index: usize, Ghost(value): Ghost<GhostT>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>)
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
            update_ghost_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view(), value),
    {
        proof {
            let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
            update_ghost(perm, value);
        }
    }

    pub fn borrow<'a>(&self, index: usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.inv(),
            0 <= index < N,
            self.spec_index(index).view().is_init(),
            lp.view().state() is WriteLock ==> self.spec_index(index).view().write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.spec_index(index).view().read_lock_perm_match(lp.view()),
        ensures
            ret == self.spec_index(index).view().view(),
    {
        let addr = lock_cell_addr_exec::<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>(LockCell::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow().tracked_borrow(index as int);
        borrow(&PPtr::<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), lp)
    }

    pub fn borrow_typed<'a>(&self, index: usize, Ghost(held_locks): Ghost<Map<usize, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.inv(),
            index_valid(N, index),
            self.spec_index(index).view().is_init(),
            self.typed_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock ==> lock_perm.view().lock_id() == self.spec_index(index).view().locking_thread()->Write_lock_id,
            lock_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Read),
            lock_perm.view().state() is ReadLock ==> self.spec_index(index).view().locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), lock_perm.view().lock_id()),
        ensures
            ret == self.spec_index(index).view().view(),
    {
        assert({
            &&& lock_perm.view().state() is WriteLock ==> self.spec_index(index).view().write_lock_perm_match(lock_perm.view())
            &&& lock_perm.view().state() is ReadLock ==> self.spec_index(index).view().read_lock_perm_match(lock_perm.view())
        }) by { reveal(LockedArray::typed_lock_map_aligned); };
        self.borrow(index, lock_perm)
    }

    pub fn borrow_mut<'a>(&'a mut self, index: usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
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
            final(self).spec_index(index).view().killer_info() == old(self).spec_index(index).view().killer_info(),
            final(self).spec_index(index).view().control() == old(self).spec_index(index).view().control(),
            // The `&mut T` linkage.
            *ret == old(self).spec_index(index).view().view(),
            final(self).spec_index(index).view().view() == *final(ret),
    {
        let addr = lock_cell_addr_exec::<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>(LockCell::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        borrow_mut(&PPtr::<LockCell<T, ROT, GhostT, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lp)
    }

    pub fn borrow_mut_typed<'a>(&'a mut self, index: usize, Ghost(held_locks): Ghost<Map<usize, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
        requires
            old(self).inv(),
            0 <= index < N,
            old(self).typed_lock_map_aligned(held_locks, lctx.thread_id()),
            old(self).spec_index(index).view().is_init(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write),
            lp.view().lock_id() == old(self).spec_index(index).view().locking_thread()->Write_lock_id,
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
            final(self).spec_index(index).view().killer_info() == old(self).spec_index(index).view().killer_info(),
            final(self).spec_index(index).view().control() == old(self).spec_index(index).view().control(),
            *ret == old(self).spec_index(index).view().view(),
            final(self).spec_index(index).view().view() == *final(ret),
            final(self).typed_lock_map_aligned(held_locks.insert(index, TypedHeldLock { lock_id: final(self).spec_index(index).lock_id(), mode: held_locks.index(index).mode }), lctx.thread_id()),
            held_locks.index(index).lock_id == old(self).spec_index(index).lock_id(),
            typed_lock_map_contains_mode(held_locks, index, TypedLockMode::Write),
            final(self).spec_index(index).lock_id() == old(self).spec_index(index).lock_id()
                ==> final(self).typed_lock_map_aligned(held_locks, lctx.thread_id()),
    {
        proof { reveal(LockedArray::typed_lock_map_aligned); }
        self.borrow_mut(index, Tracked(lctx), lp)
    }
}

impl<const N: usize> LockedArray<Cpu, (), Option<CpuId>, N, HAS_KILL_STATE, TokenCells<Cpu, (), Option<CpuId>, N, HAS_KILL_STATE>> {
    /// Write-lock entry `index` unless it is marked: a marked entry returns at once with nothing changed.
    pub fn wlock_unless_killed(&mut self, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            0 <= index < N,
            !(old(self).spec_index(index).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(index).view().view_rodata().process_source() is Dynamic),
            wlock_requires(old(self).spec_index(index).view(), old(lctx)),
            !old(self).spec_index(index).view().being_killed() ==> old(lctx).lock_id_acyclic(old(self).lock_id_by_index(index)),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            (ret is None) == old(self).spec_index(index).view().being_killed(),
            ret is None ==> *final(self) == *old(self) && *final(lctx) == *old(lctx),
            ret is Some ==> wlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view(), old(self).lock_id_by_index(index), final(lctx), ret->Some_0.view()),
            ret is Some ==> lock_ensures(old(lctx), final(lctx), old(self).lock_id_by_index(index), obj_id.view()),
    {
        let addr = lock_cell_addr_exec::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>(LockCell::<Cpu, (), Option<CpuId>, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        let ret = wlock_unless_killed_array_cell(&PPtr::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), Ghost(index), obj_id);
        proof { if ret is None { assert(self.storage.perms.view() =~= old(self).storage.perms.view()); } }
        ret
    }

    pub fn wunlock(&mut self, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).inv(),
            0 <= index < N,
            !(old(self).spec_index(index).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(index).view().view_rodata().process_source() is Dynamic),
            old(self).spec_index(index).view().wlocked_by(old(lctx)),
            old(self).spec_index(index).view().inv(),
            old(self).spec_index(index).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(index).view().locking_thread() -> Write_lock_id,
            old(lctx).lock_entry_contains(old(self).lock_id_by_index(index), obj_id.view()),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            final(self).spec_index(index).view().locking_thread() is None,
            final(self).lock_id_by_index(index) == old(self).lock_id_by_index(index),
            wunlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view()),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(self).lock_id_by_index(index)),
    {
        let addr = lock_cell_addr_exec::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>(LockCell::<Cpu, (), Option<CpuId>, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        has_kill_state_wunlock_array_cell(&PPtr::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lock_perm, Ghost(index), obj_id);
    }

    /// `wlock_unless_killed` that also clears the calling cpu's interrupt flag when it takes the lock.
    pub fn wlock_unless_killed_cli(&mut self, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            0 <= index < N,
            !(old(self).spec_index(index).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(index).view().view_rodata().process_source() is Dynamic),
            wlock_requires(old(self).spec_index(index).view(), old(lctx)),
            !old(self).spec_index(index).view().being_killed() ==> old(lctx).lock_id_acyclic(old(self).lock_id_by_index(index)),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            (ret is None) == old(self).spec_index(index).view().being_killed(),
            ret is None ==> *final(self) == *old(self) && *final(lctx) == *old(lctx),
            ret is Some ==> wlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view(), old(self).lock_id_by_index(index), final(lctx), ret->Some_0.view()),
            ret is Some ==> lock_ensures(old(lctx), final(lctx), old(self).lock_id_by_index(index), obj_id.view()),
    {
        let addr = lock_cell_addr_exec::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>(LockCell::<Cpu, (), Option<CpuId>, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        let ret = wlock_unless_killed_cli_array_cell(&PPtr::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), Ghost(index), obj_id);
        proof { if ret is None { assert(self.storage.perms.view() =~= old(self).storage.perms.view()); } }
        ret
    }

    /// `wunlock` that also sets the calling cpu's interrupt flag after the release.
    pub fn wunlock_sti(&mut self, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).inv(),
            0 <= index < N,
            !(old(self).spec_index(index).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(index).view().view_rodata().process_source() is Dynamic),
            old(self).spec_index(index).view().wlocked_by(old(lctx)),
            old(self).spec_index(index).view().inv(),
            old(self).spec_index(index).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(index).view().locking_thread() -> Write_lock_id,
            old(lctx).lock_entry_contains(old(self).lock_id_by_index(index), obj_id.view()),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            final(self).spec_index(index).view().locking_thread() is None,
            final(self).lock_id_by_index(index) == old(self).lock_id_by_index(index),
            wunlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view()),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(self).lock_id_by_index(index)),
    {
        let addr = lock_cell_addr_exec::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>(LockCell::<Cpu, (), Option<CpuId>, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        wunlock_sti_array_cell(&PPtr::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lock_perm, Ghost(index), obj_id);
    }

    /// Mark entry `index`, which this thread write-holds, for its killer; the write lock stays. The mark is a
    /// kernel-view Release: every other thread's next `*_unless_killed` lock fails.
    pub fn mark_kill(&mut self, index: usize, Tracked(lctx): Tracked<&LocalContext>, Ghost(killer_info): Ghost<KillerInfo>)
        requires
            old(self).inv(),
            0 <= index < N,
            !(old(self).spec_index(index).view().view_rodata().container_source() is Dynamic),
            !(old(self).spec_index(index).view().view_rodata().process_source() is Dynamic),
            old(self).spec_index(index).view().wlocked_by(lctx),
            !old(self).spec_index(index).view().being_killed(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            final(self).spec_index(index).view().killer_info() == Some(killer_info),
            final(self).spec_index(index).view().locking_thread() == old(self).spec_index(index).view().locking_thread(),
            final(self).spec_index(index).view().is_init() == old(self).spec_index(index).view().is_init(),
            final(self).spec_index(index).view().view_rodata() == old(self).spec_index(index).view().view_rodata(),
            final(self).spec_index(index).view().view_ghost() == old(self).spec_index(index).view().view_ghost(),
    {
        let addr = lock_cell_addr_exec::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>(LockCell::<Cpu, (), Option<CpuId>, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        mark_kill(&PPtr::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), Ghost(killer_info));
    }
}

impl LockedArray<Cpu, (), Option<CpuId>, NUM_CPUS, HAS_KILL_STATE, TokenCells<Cpu, (), Option<CpuId>, NUM_CPUS, HAS_KILL_STATE>> {
    /// Clear the mark of cpu `index` while its killer still write-holds it. Only a cpu lock can be unmarked;
    /// every other object keeps its mark until it is destroyed.
    pub fn unkill(&mut self, index: usize, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, index),
            old(self).spec_index(index).view().wlocked_by(lctx),
            old(self).spec_index(index).view().being_killed(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            !final(self).spec_index(index).view().being_killed(),
            final(self).spec_index(index).view().locking_thread() == old(self).spec_index(index).view().locking_thread(),
            final(self).spec_index(index).view().is_init() == old(self).spec_index(index).view().is_init(),
            final(self).spec_index(index).view().view_rodata() == old(self).spec_index(index).view().view_rodata(),
            final(self).spec_index(index).view().view_ghost() == old(self).spec_index(index).view().view_ghost(),
    {
        let addr = lock_cell_addr_exec::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>(LockCell::<Cpu, (), Option<CpuId>, HAS_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        unkill(&PPtr::<LockCell<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx));
    }
}

impl<const N: usize> LockedArray<Page, (), (), N, NO_KILL_STATE, TokenCells<Page, (), (), N, NO_KILL_STATE>> {
    pub fn wlock(&mut self, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
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
            lock_ensures(old(lctx), final(lctx), old(self).lock_id_by_index(index), obj_id.view()),
    {
        let addr = lock_cell_addr_exec::<LockCell<Page, (), (), NO_KILL_STATE>>(LockCell::<Page, (), (), NO_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        wlock_array_cell(&PPtr::<LockCell<Page, (), (), NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), Ghost(index), obj_id)
    }

    pub fn wunlock(&mut self, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).inv(),
            0 <= index < N,
            old(self).spec_index(index).view().wlocked_by(old(lctx)),
            old(self).spec_index(index).view().inv(),
            old(self).spec_index(index).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(index).view().locking_thread() -> Write_lock_id,
            old(lctx).lock_entry_contains(old(self).lock_id_by_index(index), obj_id.view()),
        ensures
            final(self).inv(),
            final(self).view().len() == old(self).view().len(),
            final(self).unchanged_except(old(self), index),
            final(self).spec_index(index).view().locking_thread() is None,
            final(self).lock_id_by_index(index) == old(self).lock_id_by_index(index),
            wunlock_ensures(old(self).spec_index(index).view(), final(self).spec_index(index).view()),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(self).lock_id_by_index(index)),
    {
        let addr = lock_cell_addr_exec::<LockCell<Page, (), (), NO_KILL_STATE>>(LockCell::<Page, (), (), NO_KILL_STATE>::cell_base(), index);
        let tracked perm = self.storage.perms.borrow_mut().tracked_borrow_mut(index as int);
        wunlock_array_cell(&PPtr::<LockCell<Page, (), (), NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lock_perm, Ghost(index), obj_id);
    }
}
}

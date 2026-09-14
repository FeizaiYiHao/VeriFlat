use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::reject_recursive_types(T)]
pub struct LockedArray2D<T, ROT, GhostT, const ROWS: usize, const COLS: usize> {
    array: [[RwLock<T, ROT, GhostT, NO_KILL_STATE>; COLS]; ROWS],
}

impl<T, ROT, GhostT, const ROWS: usize, const COLS: usize> LockedArray2D<T, ROT, GhostT, ROWS, COLS> {
    pub fn from_array(array: [[RwLock<T, ROT, GhostT, NO_KILL_STATE>; COLS]; ROWS]) -> (ret: Self)
        ensures ret.view() == array,
    {
        Self { array }
    }

    pub closed spec fn view(&self) -> [[RwLock<T, ROT, GhostT, NO_KILL_STATE>; COLS]; ROWS] { self.array }

    pub open spec fn spec_index(&self, row: usize, col: usize) -> RwLock<T, ROT, GhostT, NO_KILL_STATE>
        recommends index_valid(ROWS, row), index_valid(COLS, col),
    {
        self.view()[row as int][col as int]
    }

    pub fn set_ghost(&mut self, row: usize, col: usize, Ghost(value): Ghost<GhostT>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>)
        requires
            index_valid(ROWS, row),
            index_valid(COLS, col),
            old(self).spec_index(row, col).wlocked_by(lctx),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).spec_index(row, col).locking_thread()->Write_lock_id,
        ensures
            update_ghost_ensures(old(self).spec_index(row, col), final(self).spec_index(row, col), value),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        self.array[row][col].set_ghost(Ghost(value), Tracked(lctx), lp);
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait, ROT, GhostT, const ROWS: usize, const COLS: usize> LockedArray2D<T, ROT, GhostT, ROWS, COLS> {
    pub open spec fn lock_id_by_index(&self, row: usize, col: usize) -> LockId
        recommends index_valid(ROWS, row), index_valid(COLS, col),
    {
        let value = self.spec_index(row, col).view();
        LockId { container: value.container_depth(), process: value.process_depth(), major: value.current_lock_major(), minor: value.lock_minor() }
    }

    #[verifier::opaque]
    pub open spec fn typed_lock_map_aligned(&self, held: Map<(usize, usize), TypedHeldLock>, thread_id: LockThreadId) -> bool {
        &&& (forall|row: usize, col: usize|
            #![trigger held.dom().contains((row, col))]
            #![trigger self.spec_index(row, col).locked_by_thread(thread_id)]
            held.dom().contains((row, col)) == (index_valid(ROWS, row) && index_valid(COLS, col) && self.spec_index(row, col).locked_by_thread(thread_id))
            && (held.dom().contains((row, col)) ==> held.index((row, col)).lock_id == self.lock_id_by_index(row, col)))
        &&& (forall|row: usize, col: usize|
            #![trigger typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Write)]
            #![trigger self.spec_index(row, col).wlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Write) == (index_valid(ROWS, row) && index_valid(COLS, col) && self.spec_index(row, col).wlocked_by_thread(thread_id)))
        &&& (forall|row: usize, col: usize|
            #![trigger typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Read)]
            #![trigger self.spec_index(row, col).rlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Read) == (index_valid(ROWS, row) && index_valid(COLS, col) && self.spec_index(row, col).rlocked_by_thread(thread_id)))
    }

    pub fn wlock(&mut self, row: usize, col: usize, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(obj): Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            index_valid(ROWS, row),
            index_valid(COLS, col),
            wlock_requires(old(self).spec_index(row, col), old(lctx)),
            old(lctx).lock_id_acyclic(old(self).lock_id_by_index(row, col)),
            old(self).spec_index(row, col).view().lock_major_sat(old(self).lock_id_by_index(row, col).major),
        ensures
            wlock_ensures(old(self).spec_index(row, col), final(self).spec_index(row, col), old(self).lock_id_by_index(row, col), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(self).lock_id_by_index(row, col), obj),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        let id = Ghost(self.lock_id_by_index(row, col));
        self.array[row][col].wlock(Tracked(lctx), id, Ghost(obj))
    }

    pub fn wunlock(&mut self, row: usize, col: usize, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, Ghost(obj): Ghost<KernelObjId>)
        requires
            index_valid(ROWS, row),
            index_valid(COLS, col),
            old(self).spec_index(row, col).wlocked_by(old(lctx)),
            old(self).spec_index(row, col).inv(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).spec_index(row, col).locking_thread()->Write_lock_id,
            old(lctx).lock_id_set().contains((old(self).lock_id_by_index(row, col), obj)),
        ensures
            wunlock_ensures(old(self).spec_index(row, col), final(self).spec_index(row, col)),
            unlock_ensures(old(lctx), final(lctx), obj, old(self).lock_id_by_index(row, col)),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        self.array[row][col].wunlock(Tracked(lctx), lp, Ghost(obj));
    }

    pub fn borrow_typed<'a>(&self, row: usize, col: usize, Ghost(held): Ghost<Map<(usize, usize), TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            index_valid(ROWS, row),
            index_valid(COLS, col),
            self.typed_lock_map_aligned(held, lctx.thread_id()),
            self.spec_index(row, col).is_init(),
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().lock_id() == self.spec_index(row, col).locking_thread()->Write_lock_id,
        ensures *ret == self.spec_index(row, col).view(),
    {
        assert(self.spec_index(row, col).write_lock_perm_match(lp.view())) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        self.array[row][col].borrow(lp)
    }

    pub fn borrow_mut_typed<'a>(&'a mut self, row: usize, col: usize, Ghost(held): Ghost<Map<(usize, usize), TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
        requires
            index_valid(ROWS, row),
            index_valid(COLS, col),
            old(self).typed_lock_map_aligned(held, lctx.thread_id()),
            old(self).spec_index(row, col).is_init(),
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().lock_id() == old(self).spec_index(row, col).locking_thread()->Write_lock_id,
        ensures
            *ret == old(self).spec_index(row, col).view(),
            final(self).spec_index(row, col).view() == *final(ret),
            final(self).spec_index(row, col).locking_thread() == old(self).spec_index(row, col).locking_thread(),
            final(self).spec_index(row, col).view_rodata() == old(self).spec_index(row, col).view_rodata(),
            final(self).spec_index(row, col).view_ghost() == old(self).spec_index(row, col).view_ghost(),
            final(self).spec_index(row, col).is_init(),
            final(self).spec_index(row, col).being_killed() == old(self).spec_index(row, col).being_killed(),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        assert(self.spec_index(row, col).wlocked_by(lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        self.array[row][col].borrow_mut(Tracked(lctx), lp)
    }
}
}

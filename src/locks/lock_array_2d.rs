use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
/// A two-dimensional lock array over token storage: the cells live in memory outside the array value, reached only
/// through raw addresses. Cell `(row, col)` lies at `lock_cell_addr(base, row * COLS + col)` for the lock type's
/// `TokenCellBase` address `base`, and the array holds one points-to token per cell and no runtime bytes.
#[verifier::reject_recursive_types(T)]
pub struct LockedArray2D<T, ROT, GhostT, const ROWS: usize, const COLS: usize> {
    perms: Tracked<Map<(usize, usize), PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>>,
}

impl<T, ROT, GhostT, const ROWS: usize, const COLS: usize> LockedArray2D<T, ROT, GhostT, ROWS, COLS> where RwLock<T, ROT, GhostT, NO_KILL_STATE>: TokenCellBase {
    /// `perms` holds exactly one token per in-range cell, each covering an initialized lock at its cell address.
    pub open spec fn token_cells_wf(perms: Map<(usize, usize), PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>) -> bool {
        &&& ROWS * COLS <= usize::MAX
        &&& forall|row: usize, col: usize| #![trigger perms.dom().contains((row, col))] perms.dom().contains((row, col)) <==> index_valid(ROWS, row) && index_valid(COLS, col)
        &&& forall|row: usize, col: usize|
            #![trigger perms.dom().contains((row, col))]
            #![trigger perms[(row, col)]]
            perms.dom().contains((row, col)) ==> {
                &&& perms[(row, col)].is_init()
                &&& perms[(row, col)].addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>(RwLock::<T, ROT, GhostT, NO_KILL_STATE>::cell_base_spec(), row * COLS + col)
            }
    }

    pub closed spec fn inv(&self) -> bool { Self::token_cells_wf(self.perms@) }

    pub closed spec fn spec_index(&self, row: usize, col: usize) -> RwLock<T, ROT, GhostT, NO_KILL_STATE>
        recommends
            index_valid(ROWS, row),
            index_valid(COLS, col),
    {
        self.perms@[(row, col)].value()
    }

    /// Builds the array over cells that boot initialized in place.
    pub fn from_token_cells(perms: Tracked<Map<(usize, usize), PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>>) -> (ret: Self)
        requires
            Self::token_cells_wf(perms@),
        ensures
            ret.inv(),
    {
        Self { perms }
    }

    fn cell_addr(&self, row: usize, col: usize) -> (ret: usize)
        requires
            self.inv(),
            index_valid(ROWS, row),
            index_valid(COLS, col),
        ensures
            ret == self.perms@[(row, col)].addr(),
    {
        assert(row * COLS + col < ROWS * COLS) by (nonlinear_arith) requires row < ROWS, col < COLS;
        lock_cell_addr_exec::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>(RwLock::<T, ROT, GhostT, NO_KILL_STATE>::cell_base(), row * COLS + col)
    }

    pub fn set_ghost(&mut self, row: usize, col: usize, Ghost(value): Ghost<GhostT>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>)
        requires
            old(self).inv(),
            index_valid(ROWS, row),
            index_valid(COLS, col),
            old(self).spec_index(row, col).wlocked_by(lctx),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).spec_index(row, col).locking_thread()->Write_lock_id,
        ensures
            final(self).inv(),
            update_ghost_ensures(old(self).spec_index(row, col), final(self).spec_index(row, col), value),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        proof {
            let tracked perm = self.perms.borrow_mut().tracked_borrow_mut((row, col));
            update_ghost(perm, value);
        }
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait, ROT, GhostT, const ROWS: usize, const COLS: usize> LockedArray2D<T, ROT, GhostT, ROWS, COLS>
    where RwLock<T, ROT, GhostT, NO_KILL_STATE>: TokenCellBase {
    pub open spec fn lock_id_by_index(&self, row: usize, col: usize) -> LockId
        recommends
            index_valid(ROWS, row),
            index_valid(COLS, col),
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
            old(self).inv(),
            index_valid(ROWS, row),
            index_valid(COLS, col),
            wlock_requires(old(self).spec_index(row, col), old(lctx)),
            old(lctx).lock_id_acyclic(old(self).lock_id_by_index(row, col)),
        ensures
            final(self).inv(),
            wlock_ensures(old(self).spec_index(row, col), final(self).spec_index(row, col), old(self).lock_id_by_index(row, col), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(self).lock_id_by_index(row, col), obj),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        let addr = self.cell_addr(row, col);
        let tracked perm = self.perms.borrow_mut().tracked_borrow_mut((row, col));
        wlock_object_minor(&PPtr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), Ghost(obj))
    }

    pub fn wunlock(&mut self, row: usize, col: usize, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, Ghost(obj): Ghost<KernelObjId>)
        requires
            old(self).inv(),
            index_valid(ROWS, row),
            index_valid(COLS, col),
            old(self).spec_index(row, col).wlocked_by(old(lctx)),
            old(self).spec_index(row, col).inv(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).spec_index(row, col).locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).lock_id_by_index(row, col), obj),
        ensures
            final(self).inv(),
            wunlock_ensures(old(self).spec_index(row, col), final(self).spec_index(row, col)),
            unlock_ensures(old(lctx), final(lctx), obj, old(self).lock_id_by_index(row, col)),
            forall|r: usize, c: usize| #![trigger final(self).spec_index(r, c)] #![trigger old(self).spec_index(r, c)] index_valid(ROWS, r) && index_valid(COLS, c) && (r != row || c != col) ==> final(self).spec_index(r, c) == old(self).spec_index(r, c),
    {
        let addr = self.cell_addr(row, col);
        let tracked perm = self.perms.borrow_mut().tracked_borrow_mut((row, col));
        wunlock_object_minor(&PPtr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lp, Ghost(obj));
    }

    pub fn borrow_typed<'a>(&self, row: usize, col: usize, Ghost(held): Ghost<Map<(usize, usize), TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.inv(),
            index_valid(ROWS, row),
            index_valid(COLS, col),
            self.typed_lock_map_aligned(held, lctx.thread_id()),
            self.spec_index(row, col).is_init(),
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().lock_id() == self.spec_index(row, col).locking_thread()->Write_lock_id,
        ensures
            *ret == self.spec_index(row, col).view(),
    {
        assert(self.spec_index(row, col).write_lock_perm_match(lp.view())) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        let addr = self.cell_addr(row, col);
        let tracked perm = self.perms.borrow().tracked_borrow((row, col));
        borrow(&PPtr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>::from_usize(addr), Tracked(perm), lp)
    }

    pub fn borrow_mut_typed<'a>(&'a mut self, row: usize, col: usize, Ghost(held): Ghost<Map<(usize, usize), TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
        requires
            old(self).inv(),
            index_valid(ROWS, row),
            index_valid(COLS, col),
            old(self).typed_lock_map_aligned(held, lctx.thread_id()),
            old(self).spec_index(row, col).is_init(),
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held, (row, col), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().lock_id() == old(self).spec_index(row, col).locking_thread()->Write_lock_id,
        ensures
            final(self).inv(),
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
        let addr = self.cell_addr(row, col);
        let tracked perm = self.perms.borrow_mut().tracked_borrow_mut((row, col));
        borrow_mut(&PPtr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lp)
    }
}
}

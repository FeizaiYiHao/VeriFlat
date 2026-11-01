use vstd::prelude::*;
use crate::define::*;

verus! {
/// Runtime outcome of a dynamic write acquisition: the lock was taken under the requested owner, the lock carries a
/// kill mark, or a live holder records an owner below the requested one.
pub enum DynamicWLockOutcome {
    Acquired,
    Killed,
    DepthConflict(LockOwnerId),
}

/// Runtime word of a lock taken only by writers. These traits are exec only: the ghost lock state lives in `LockCell`, and
/// the TCB primitives of `locked_points_to.rs` state what each operation does to it.
pub trait SpinLockInner: Sized {
    fn new_unlocked() -> Self;
    /// Image of a lock already write-held by its retyper under the recorded dynamic owner `owner` (`None` if unowned).
    fn new_wlocked_for_retype(owner: LockOwnerId) -> Self;
    fn wlock(&self);
    fn wunlock(&self);
}

/// Runtime word of a lock with a kill mark and a recorded dynamic owner.
pub trait KillableLockInner: SpinLockInner {
    /// Takes the lock unless it is marked; `false` leaves the lock unchanged.
    fn wlock_unless_killed(&self) -> bool;
    /// `wlock_unless_killed` that clears the calling cpu's interrupt flag before the acquisition becomes visible.
    fn wlock_unless_killed_cli(&self) -> bool;
    /// Takes and marks the lock in one step; `false` only if it is already marked.
    fn try_wlock_and_mark_kill(&self) -> bool;
    /// Marks the lock the caller write-holds.
    fn mark_kill(&self);
    /// Clears the mark of the lock the caller write-holds.
    fn unkill(&self);
    /// `wunlock` that sets the calling cpu's interrupt flag once the lock is released.
    fn wunlock_sti(&self);
    /// Reports a mark first, then a live holder whose recorded owner is below `requested`; takes a free lock under
    /// `requested` and waits for any other holder.
    fn dynamic_wlock(&self, requested: LockOwnerId) -> DynamicWLockOutcome;
    /// Releases a dynamic write acquisition and clears its recorded owner.
    fn dynamic_wunlock(&self);
}

/// Runtime word of a lock shared by readers; each reader is named by the cpu it runs on.
pub trait RwLockInner: SpinLockInner {
    fn rlock(&self, cpu_id: CpuId);
    fn runlock(&self, cpu_id: CpuId);
    /// Turns the caller's write lock into the only read lock, held by `cpu_id`.
    fn downgrade(&self, cpu_id: CpuId);
}
}

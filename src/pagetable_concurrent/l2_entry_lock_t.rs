use vstd::prelude::*;
use vstd::simple_pptr::*;
use core::sync::atomic::*;
use crate::*;

verus! {
// TCB: the word and L1-slot primitives of entry `i` of an L2 page reached through its points-to token. The word
// primitives reach the entry's word through a raw-pointer place at `pptr`, so no `&mut` covers the page's other lock
// words that other CPUs CAS concurrently; the L1 slot is ghost and moves only in the token's value.

/// TCB: spin until this thread owns the lock bit of entry `i` of the L2 page at `pptr`; the bit is free when this
/// thread takes it.
#[verifier::external_body]
pub fn l2_entry_lock(pptr: &PPtr<L2PageMap>, Tracked(perm): Tracked<&mut PointsTo<L2PageMap>>, i: L2Index, Tracked(lctx): Tracked<&mut LocalContext>,
    Ghost(lock_id): Ghost<LockId>, Ghost(obj_id): Ghost<KernelObjId>) -> (lp: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        pei_valid(i),
        !(old(perm).value().entry_lock(i).locking_thread() is Write && old(perm).value().entry_lock(i).locking_thread()->Write_thread_id == old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        window_wlock_ensures(old(perm).value().entry_lock(i), final(perm).value().entry_lock(i), lock_id, final(lctx), lp.view()),
        lock_ensures(old(lctx), final(lctx), lock_id, obj_id),
{
    let p = pptr.addr() as *mut L2PageMap;
    loop {
        let v = unsafe { (*p).ar[i].word.load(Ordering::Relaxed) };
        if v & L2_ENTRY_LOCK_MASK == 0 && unsafe { (*p).ar[i].word.compare_exchange_weak(v, v | L2_ENTRY_LOCK_MASK, Ordering::Acquire, Ordering::Relaxed) }.is_ok() { break; }
        core::hint::spin_loop();
    }
    Tracked::assume_new()
}

/// TCB: release the lock bit of entry `i` of the L2 page at `pptr`; the entry otherwise stays as published.
#[verifier::external_body]
pub fn l2_entry_unlock(pptr: &PPtr<L2PageMap>, Tracked(perm): Tracked<&mut PointsTo<L2PageMap>>, i: L2Index, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(lp): Tracked<LockPerm>, Ghost(lock_id): Ghost<LockId>, Ghost(obj_id): Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        pei_valid(i),
        old(perm).value().entry_lock(i).locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lp.lock_id() }),
        lp.state() is WriteLock,
        lp.thread_id() == old(lctx).thread_id(),
        old(lctx).lock_entry_contains(lock_id, obj_id),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        window_wunlock_ensures(old(perm).value().entry_lock(i), final(perm).value().entry_lock(i)),
        unlock_ensures(old(lctx), final(lctx), obj_id, lock_id),
{
    let p = pptr.addr() as *mut L2PageMap;
    unsafe { (*p).ar[i].word.fetch_and(!L2_ENTRY_LOCK_MASK, Ordering::Release); }
}

/// TCB: release-store `w` into the word of entry `i` of the L2 page at `pptr`. The stored lock bit must match the
/// recorded locking thread, so a store never takes or drops the window lock.
#[verifier::external_body]
pub(super) fn l2_entry_store_release(pptr: &PPtr<L2PageMap>, Tracked(perm): Tracked<&mut PointsTo<L2PageMap>>, i: L2Index, w: usize)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        pei_valid(i),
        (w & L2_ENTRY_LOCK_MASK != 0) == (old(perm).value().entry_lock(i).locking_thread() is Write),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        final(perm).value().entry_lock(i).view() == usize2page_entry(w),
        final(perm).value().entry_lock(i).locking_thread() == old(perm).value().entry_lock(i).locking_thread(),
        final(perm).value().entry_lock(i).l1() == old(perm).value().entry_lock(i).l1(),
{
    let p = pptr.addr() as *mut L2PageMap;
    unsafe { (*p).ar[i].word.store(w, Ordering::Release); }
}

/// TCB: ghost-only. Move the L1 page token out of the slot of entry `i` of the L2 page behind `perm` while this thread
/// holds the entry's lock; no memory is touched.
#[verifier::external_body]
pub proof fn l2_entry_take_l1(tracked perm: &mut PointsTo<L2PageMap>, i: L2Index, tracked lp: &LockPerm) -> (tracked ret: PointsTo<PageMap>)
    requires
        old(perm).is_init(),
        pei_valid(i),
        old(perm).value().entry_lock(i).locking_thread() == (RwLockState::Write { thread_id: lp.thread_id(), lock_id: lp.lock_id() }),
        old(perm).value().entry_lock(i).l1() is Some,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        final(perm).value().entry_lock(i).view() == old(perm).value().entry_lock(i).view(),
        final(perm).value().entry_lock(i).locking_thread() == old(perm).value().entry_lock(i).locking_thread(),
        final(perm).value().entry_lock(i).l1() is None,
        ret == old(perm).value().entry_lock(i).l1()->Some_0,
{
    unimplemented!()
}

/// TCB: ghost-only. Move the L1 page token `l1` into the slot of entry `i` of the L2 page behind `perm` while this
/// thread holds the entry's lock; no memory is touched.
#[verifier::external_body]
pub proof fn l2_entry_put_l1(tracked perm: &mut PointsTo<L2PageMap>, i: L2Index, tracked lp: &LockPerm, tracked l1: PointsTo<PageMap>)
    requires
        old(perm).is_init(),
        pei_valid(i),
        old(perm).value().entry_lock(i).locking_thread() == (RwLockState::Write { thread_id: lp.thread_id(), lock_id: lp.lock_id() }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        final(perm).value().entry_lock(i).view() == old(perm).value().entry_lock(i).view(),
        final(perm).value().entry_lock(i).locking_thread() == old(perm).value().entry_lock(i).locking_thread(),
        final(perm).value().entry_lock(i).l1() == Some(l1),
{
    unimplemented!()
}
} // verus!

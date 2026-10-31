use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
// TCB: the flag lock primitives of a `CpuOfflineFlags` table reached through its points-to token. Each reaches its flag
// lock or payload through a raw-pointer place at `pptr`, so no `&mut` covers the other flags' lock words; a payload
// borrow is formed only while its write lock is held.

/// TCB: `LockedArray::wlock` of flag `cpu_id` of the offline-flag table at `pptr`.
#[verifier::external_body]
pub fn wlock_flag(pptr: &PPtr<CpuOfflineFlags>, Tracked(perm): Tracked<&mut PointsTo<CpuOfflineFlags>>, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>)
    -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().flags.inv(),
        0 <= cpu_id < NUM_CPUS,
        wlock_requires(old(perm).value().flags.spec_index(cpu_id).view(), old(lctx)),
        old(lctx).lock_id_acyclic(old(perm).value().flags.lock_id_by_index(cpu_id)),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().flags.inv(),
        final(perm).value().flags.view().len() == old(perm).value().flags.view().len(),
        final(perm).value().flags.unchanged_except(&old(perm).value().flags, cpu_id),
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().container_depth == old(perm).value().container_depth,
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        wlock_ensures(old(perm).value().flags.spec_index(cpu_id).view(), final(perm).value().flags.spec_index(cpu_id).view(), old(perm).value().flags.lock_id_by_index(cpu_id), final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), old(perm).value().flags.lock_id_by_index(cpu_id), obj_id.view()),
{
    let p = pptr.addr() as *mut CpuOfflineFlags;
    unsafe { (*p).flags.storage.ar[cpu_id].lock.wlock(); }
    Tracked::assume_new()
}

/// TCB: `LockedArray::wunlock` of flag `cpu_id` of the offline-flag table at `pptr`.
#[verifier::external_body]
pub fn wunlock_flag(pptr: &PPtr<CpuOfflineFlags>, Tracked(perm): Tracked<&mut PointsTo<CpuOfflineFlags>>, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().flags.inv(),
        0 <= cpu_id < NUM_CPUS,
        old(perm).value().flags.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(perm).value().flags.spec_index(cpu_id).view().being_killed() == false,
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(old(perm).value().flags.lock_id_by_index(cpu_id), obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().flags.inv(),
        final(perm).value().flags.view().len() == old(perm).value().flags.view().len(),
        final(perm).value().flags.unchanged_except(&old(perm).value().flags, cpu_id),
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().container_depth == old(perm).value().container_depth,
        final(perm).value().flags.spec_index(cpu_id).view().locking_thread() is None,
        final(perm).value().flags.lock_id_by_index(cpu_id) == old(perm).value().flags.lock_id_by_index(cpu_id),
        wunlock_ensures(old(perm).value().flags.spec_index(cpu_id).view(), final(perm).value().flags.spec_index(cpu_id).view()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(perm).value().flags.lock_id_by_index(cpu_id)),
{
    let p = pptr.addr() as *mut CpuOfflineFlags;
    unsafe { (*p).flags.storage.ar[cpu_id].lock.wunlock(); }
}

/// TCB: `LockedArray::borrow_mut` of the payload of flag `cpu_id` of the offline-flag table at `pptr` under its write lock.
#[verifier::external_body]
pub fn borrow_mut_flag<'a>(pptr: &PPtr<CpuOfflineFlags>, Tracked(perm): Tracked<&'a mut PointsTo<CpuOfflineFlags>>, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>,
    lp: Tracked<&'a LockPerm>) -> (ret: &'a mut OfflineFlag)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().flags.inv(),
        0 <= cpu_id < NUM_CPUS,
        old(perm).value().flags.spec_index(cpu_id).view().wlocked_by(lctx),
        old(perm).value().flags.spec_index(cpu_id).view().is_init(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == lctx.thread_id(),
        lp.view().lock_id() == old(perm).value().flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().flags.inv(),
        final(perm).value().flags.view().len() == old(perm).value().flags.view().len(),
        final(perm).value().flags.entries_unchanged_except(&old(perm).value().flags, cpu_id),
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().container_depth == old(perm).value().container_depth,
        final(perm).value().flags.spec_index(cpu_id).view().is_init(),
        final(perm).value().flags.spec_index(cpu_id).view().wlocked_by(lctx),
        final(perm).value().flags.spec_index(cpu_id).view().view_rodata() == old(perm).value().flags.spec_index(cpu_id).view().view_rodata(),
        final(perm).value().flags.spec_index(cpu_id).view().view_ghost() == old(perm).value().flags.spec_index(cpu_id).view().view_ghost(),
        final(perm).value().flags.spec_index(cpu_id).view().locking_thread() == old(perm).value().flags.spec_index(cpu_id).view().locking_thread(),
        final(perm).value().flags.spec_index(cpu_id).view().being_killed() == old(perm).value().flags.spec_index(cpu_id).view().being_killed(),
        final(perm).value().flags.spec_index(cpu_id).view().killer_info() == old(perm).value().flags.spec_index(cpu_id).view().killer_info(),
        final(perm).value().flags.spec_index(cpu_id).view().control() == old(perm).value().flags.spec_index(cpu_id).view().control(),
        *ret == old(perm).value().flags.spec_index(cpu_id).view().view(),
        final(perm).value().flags.spec_index(cpu_id).view().view() == *final(ret),
{
    let p = pptr.addr() as *mut CpuOfflineFlags;
    unsafe { &mut (*p).flags.storage.ar[cpu_id].value }
}
}

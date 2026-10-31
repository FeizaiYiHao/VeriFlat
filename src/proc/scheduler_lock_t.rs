use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
// TCB: the shard lock primitives of a `Scheduler` reached through its points-to token. Each reaches its shard lock or
// payload through a raw-pointer place at `pptr`, so no `&mut` covers the other shards' lock words; a payload borrow
// is formed only while its write lock is held.

/// TCB: `LockedArray::wlock` of shard `cpu_id` of the scheduler at `pptr`.
#[verifier::external_body]
pub fn wlock_shard(pptr: &PPtr<Scheduler>, Tracked(perm): Tracked<&mut PointsTo<Scheduler>>, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>)
    -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().shards.inv(),
        0 <= cpu_id < NUM_CPUS,
        wlock_requires(old(perm).value().shards.spec_index(cpu_id).view(), old(lctx)),
        old(lctx).lock_id_acyclic(old(perm).value().shards.lock_id_by_index(cpu_id)),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().shards.inv(),
        final(perm).value().shards.view().len() == old(perm).value().shards.view().len(),
        final(perm).value().shards.unchanged_except(&old(perm).value().shards, cpu_id),
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        wlock_ensures(old(perm).value().shards.spec_index(cpu_id).view(), final(perm).value().shards.spec_index(cpu_id).view(), old(perm).value().shards.lock_id_by_index(cpu_id), final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), old(perm).value().shards.lock_id_by_index(cpu_id), obj_id.view()),
{
    let p = pptr.addr() as *mut Scheduler;
    unsafe { (*p).shards.storage.ar[cpu_id].lock.wlock(); }
    Tracked::assume_new()
}

/// TCB: `LockedArray::wunlock` of shard `cpu_id` of the scheduler at `pptr`.
#[verifier::external_body]
pub fn wunlock_shard(pptr: &PPtr<Scheduler>, Tracked(perm): Tracked<&mut PointsTo<Scheduler>>, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().shards.inv(),
        0 <= cpu_id < NUM_CPUS,
        old(perm).value().shards.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(perm).value().shards.spec_index(cpu_id).view().being_killed() == false,
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(old(perm).value().shards.lock_id_by_index(cpu_id), obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().shards.inv(),
        final(perm).value().shards.view().len() == old(perm).value().shards.view().len(),
        final(perm).value().shards.unchanged_except(&old(perm).value().shards, cpu_id),
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().shards.spec_index(cpu_id).view().locking_thread() is None,
        final(perm).value().shards.lock_id_by_index(cpu_id) == old(perm).value().shards.lock_id_by_index(cpu_id),
        wunlock_ensures(old(perm).value().shards.spec_index(cpu_id).view(), final(perm).value().shards.spec_index(cpu_id).view()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(perm).value().shards.lock_id_by_index(cpu_id)),
{
    let p = pptr.addr() as *mut Scheduler;
    unsafe { (*p).shards.storage.ar[cpu_id].lock.wunlock(); }
}

/// TCB: `LockedArray::borrow_mut` of the payload of shard `cpu_id` of the scheduler at `pptr` under its write lock.
#[verifier::external_body]
pub fn borrow_mut_shard<'a>(pptr: &PPtr<Scheduler>, Tracked(perm): Tracked<&'a mut PointsTo<Scheduler>>, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>,
    lp: Tracked<&'a LockPerm>) -> (ret: &'a mut SchedulerShard)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().shards.inv(),
        0 <= cpu_id < NUM_CPUS,
        old(perm).value().shards.spec_index(cpu_id).view().wlocked_by(lctx),
        old(perm).value().shards.spec_index(cpu_id).view().is_init(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == lctx.thread_id(),
        lp.view().lock_id() == old(perm).value().shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().shards.inv(),
        final(perm).value().shards.view().len() == old(perm).value().shards.view().len(),
        final(perm).value().shards.entries_unchanged_except(&old(perm).value().shards, cpu_id),
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().shards.spec_index(cpu_id).view().is_init(),
        final(perm).value().shards.spec_index(cpu_id).view().wlocked_by(lctx),
        final(perm).value().shards.spec_index(cpu_id).view().view_rodata() == old(perm).value().shards.spec_index(cpu_id).view().view_rodata(),
        final(perm).value().shards.spec_index(cpu_id).view().view_ghost() == old(perm).value().shards.spec_index(cpu_id).view().view_ghost(),
        final(perm).value().shards.spec_index(cpu_id).view().locking_thread() == old(perm).value().shards.spec_index(cpu_id).view().locking_thread(),
        final(perm).value().shards.spec_index(cpu_id).view().being_killed() == old(perm).value().shards.spec_index(cpu_id).view().being_killed(),
        final(perm).value().shards.spec_index(cpu_id).view().killer_info() == old(perm).value().shards.spec_index(cpu_id).view().killer_info(),
        final(perm).value().shards.spec_index(cpu_id).view().control() == old(perm).value().shards.spec_index(cpu_id).view().control(),
        *ret == old(perm).value().shards.spec_index(cpu_id).view().view(),
        final(perm).value().shards.spec_index(cpu_id).view().view() == *final(ret),
{
    let p = pptr.addr() as *mut Scheduler;
    unsafe { &mut (*p).shards.storage.ar[cpu_id].value }
}
}

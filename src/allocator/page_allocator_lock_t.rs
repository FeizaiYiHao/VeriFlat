use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
// TCB: the lock primitives of a `PageAllocator` reached through its points-to token. Each reaches its lock or payload
// through a raw-pointer place at `pptr`, so no `&mut` covers the allocator's other lock words; a payload borrow is
// formed only while its write lock is held.

/// TCB: `SpinLockInner::wlock` of the quota of the allocator at `pptr`.
#[verifier::external_body]
pub fn wlock_quota<const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, Tracked(lctx): Tracked<&mut LocalContext>,
    lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().quota.view().container_depth() == lock_id.view().container,
        old(perm).value().quota.view().process_depth() == lock_id.view().process,
        old(perm).value().quota.view().lock_major_sat(lock_id.view().major),
        old(perm).value().quota.view().lock_minor() == lock_id.view().minor,
        wlock_requires(old(perm).value().quota, old(lctx)),
        old(lctx).lock_id_acyclic(lock_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wlock_ensures(old(perm).value().quota, final(perm).value().quota, lock_id.view(), final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view()),
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { (*p).quota.lock.wlock(); }
    Tracked::assume_new()
}

/// TCB: `SpinLockInner::wunlock` of the quota of the allocator at `pptr`.
#[verifier::external_body]
pub fn wunlock_quota<const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, Tracked(lctx): Tracked<&mut LocalContext>,
    lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().quota.wlocked_by(old(lctx)),
        old(perm).value().quota.inv(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == old(lctx).thread_id(),
        lp.view().lock_id() == old(perm).value().quota.locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(LockId {
            container: old(perm).value().quota.view().container_depth(), process: old(perm).value().quota.view().process_depth(),
            major: old(perm).value().quota.view().current_lock_major(), minor: old(perm).value().quota.view().lock_minor() }, obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wunlock_ensures(old(perm).value().quota, final(perm).value().quota),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
            container: old(perm).value().quota.view().container_depth(), process: old(perm).value().quota.view().process_depth(),
            major: old(perm).value().quota.view().current_lock_major(), minor: old(perm).value().quota.view().lock_minor() }),
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { (*p).quota.lock.wunlock(); }
}

/// TCB: mutably borrow the quota payload of the allocator at `pptr` under its write lock.
#[verifier::external_body]
pub fn borrow_mut_quota<'a, const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&'a mut PointsTo<PageAllocator<SIZE>>>, Tracked(lctx): Tracked<&LocalContext>,
    lp: Tracked<&'a LockPerm>) -> (ret: &'a mut AllocatorQuota<SIZE>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().quota.wlocked_by(lctx),
        old(perm).value().quota.is_init(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == lctx.thread_id(),
        lp.view().lock_id() == old(perm).value().quota.locking_thread()->Write_lock_id,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().quota.is_init(),
        final(perm).value().quota.wlocked_by(lctx),
        final(perm).value().quota.view_rodata() == old(perm).value().quota.view_rodata(),
        final(perm).value().quota.view_ghost() == old(perm).value().quota.view_ghost(),
        final(perm).value().quota.locking_thread() == old(perm).value().quota.locking_thread(),
        final(perm).value().quota.control() == old(perm).value().quota.control(),
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
        *ret == old(perm).value().quota.view(),
        final(perm).value().quota.view() == *final(ret),
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { &mut (*p).quota.value }
}

/// TCB: `LockedArray::wlock` of the cache of cpu `cpu_id` in the allocator at `pptr`.
#[verifier::external_body]
pub fn wlock_cache<const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().cpu_caches.inv(),
        0 <= cpu_id < NUM_CPUS,
        wlock_requires(old(perm).value().cpu_caches.spec_index(cpu_id).view(), old(lctx)),
        old(lctx).lock_id_acyclic(old(perm).value().cpu_caches.lock_id_by_index(cpu_id)),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().cpu_caches.inv(),
        final(perm).value().cpu_caches.view().len() == old(perm).value().cpu_caches.view().len(),
        final(perm).value().cpu_caches.unchanged_except(&old(perm).value().cpu_caches, cpu_id),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        wlock_ensures(old(perm).value().cpu_caches.spec_index(cpu_id).view(), final(perm).value().cpu_caches.spec_index(cpu_id).view(), old(perm).value().cpu_caches.lock_id_by_index(cpu_id), final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), old(perm).value().cpu_caches.lock_id_by_index(cpu_id), obj_id.view()),
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { (*p).cpu_caches.storage.ar[cpu_id].lock.wlock(); }
    Tracked::assume_new()
}

/// TCB: `LockedArray::wunlock` of the cache of cpu `cpu_id` in the allocator at `pptr`.
#[verifier::external_body]
pub fn wunlock_cache<const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().cpu_caches.inv(),
        0 <= cpu_id < NUM_CPUS,
        old(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed() == false,
        lp.view().state() is WriteLock,
        lp.view().thread_id() == old(lctx).thread_id(),
        lp.view().lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(old(perm).value().cpu_caches.lock_id_by_index(cpu_id), obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().cpu_caches.inv(),
        final(perm).value().cpu_caches.view().len() == old(perm).value().cpu_caches.view().len(),
        final(perm).value().cpu_caches.unchanged_except(&old(perm).value().cpu_caches, cpu_id),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread() is None,
        final(perm).value().cpu_caches.lock_id_by_index(cpu_id) == old(perm).value().cpu_caches.lock_id_by_index(cpu_id),
        wunlock_ensures(old(perm).value().cpu_caches.spec_index(cpu_id).view(), final(perm).value().cpu_caches.spec_index(cpu_id).view()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(perm).value().cpu_caches.lock_id_by_index(cpu_id)),
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { (*p).cpu_caches.storage.ar[cpu_id].lock.wunlock(); }
}

/// TCB: mutably borrow the cache payload of cpu `cpu_id` in the allocator at `pptr` under its write lock.
#[verifier::external_body]
pub fn borrow_mut_cache<'a, const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&'a mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
    Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut AllocatorCache<SIZE>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().cpu_caches.inv(),
        0 <= cpu_id < NUM_CPUS,
        old(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
        old(perm).value().cpu_caches.spec_index(cpu_id).view().is_init(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == lctx.thread_id(),
        lp.view().lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().cpu_caches.inv(),
        final(perm).value().cpu_caches.view().len() == old(perm).value().cpu_caches.view().len(),
        final(perm).value().cpu_caches.entries_unchanged_except(&old(perm).value().cpu_caches, cpu_id),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().is_init(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().view_rodata() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view_rodata(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().view_ghost() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view_ghost(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed() == old(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().killer_info() == old(perm).value().cpu_caches.spec_index(cpu_id).view().killer_info(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().control() == old(perm).value().cpu_caches.spec_index(cpu_id).view().control(),
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
        *ret == old(perm).value().cpu_caches.spec_index(cpu_id).view().view(),
        final(perm).value().cpu_caches.spec_index(cpu_id).view().view() == *final(ret),
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { &mut (*p).cpu_caches.storage.ar[cpu_id].value }
}

/// TCB: `SpinLockInner::wlock` of the global pool of the allocator at `pptr`.
#[verifier::external_body]
pub fn wlock_global_pool<const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, Tracked(lctx): Tracked<&mut LocalContext>,
    lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().global_pool.view().container_depth() == lock_id.view().container,
        old(perm).value().global_pool.view().process_depth() == lock_id.view().process,
        old(perm).value().global_pool.view().lock_major_sat(lock_id.view().major),
        old(perm).value().global_pool.view().lock_minor() == lock_id.view().minor,
        wlock_requires(old(perm).value().global_pool, old(lctx)),
        old(lctx).lock_id_acyclic(lock_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wlock_ensures(old(perm).value().global_pool, final(perm).value().global_pool, lock_id.view(), final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view()),
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { (*p).global_pool.lock.wlock(); }
    Tracked::assume_new()
}

/// TCB: `SpinLockInner::wunlock` of the global pool of the allocator at `pptr`.
#[verifier::external_body]
pub fn wunlock_global_pool<const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, Tracked(lctx): Tracked<&mut LocalContext>,
    lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().global_pool.wlocked_by(old(lctx)),
        old(perm).value().global_pool.inv(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == old(lctx).thread_id(),
        lp.view().lock_id() == old(perm).value().global_pool.locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(LockId {
            container: old(perm).value().global_pool.view().container_depth(), process: old(perm).value().global_pool.view().process_depth(),
            major: old(perm).value().global_pool.view().current_lock_major(), minor: old(perm).value().global_pool.view().lock_minor() }, obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wunlock_ensures(old(perm).value().global_pool, final(perm).value().global_pool),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
            container: old(perm).value().global_pool.view().container_depth(), process: old(perm).value().global_pool.view().process_depth(),
            major: old(perm).value().global_pool.view().current_lock_major(), minor: old(perm).value().global_pool.view().lock_minor() }),
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { (*p).global_pool.lock.wunlock(); }
}

/// TCB: mutably borrow the global pool payload of the allocator at `pptr` under its write lock.
#[verifier::external_body]
pub fn borrow_mut_global_pool<'a, const SIZE: usize>(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&'a mut PointsTo<PageAllocator<SIZE>>>,
    Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut GlobalPool<SIZE>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().global_pool.wlocked_by(lctx),
        old(perm).value().global_pool.is_init(),
        lp.view().state() is WriteLock,
        lp.view().thread_id() == lctx.thread_id(),
        lp.view().lock_id() == old(perm).value().global_pool.locking_thread()->Write_lock_id,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().global_pool.is_init(),
        final(perm).value().global_pool.wlocked_by(lctx),
        final(perm).value().global_pool.view_rodata() == old(perm).value().global_pool.view_rodata(),
        final(perm).value().global_pool.view_ghost() == old(perm).value().global_pool.view_ghost(),
        final(perm).value().global_pool.locking_thread() == old(perm).value().global_pool.locking_thread(),
        final(perm).value().global_pool.control() == old(perm).value().global_pool.control(),
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
        final(perm).value().total_free_pages == old(perm).value().total_free_pages,
        *ret == old(perm).value().global_pool.view(),
        final(perm).value().global_pool.view() == *final(ret),
{
    let p = pptr.addr() as *mut PageAllocator<SIZE>;
    unsafe { &mut (*p).global_pool.value }
}

/// TCB: ghost-only, mirrors locked_points_to::update_ghost. Replaces the zero-sized free-page count of the allocator
/// behind `perm`; no memory is touched.
#[verifier::external_body]
pub proof fn set_total_free_pages_ghost<const SIZE: usize>(tracked perm: &mut PointsTo<PageAllocator<SIZE>>, total_free_pages: usize)
    requires
        old(perm).is_init(),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().total_free_pages.view() == total_free_pages,
        final(perm).value().cpu_caches == old(perm).value().cpu_caches,
        final(perm).value().global_pool == old(perm).value().global_pool,
        final(perm).value().quota == old(perm).value().quota,
        final(perm).value().owning_container == old(perm).value().owning_container,
{
    unimplemented!()
}
}

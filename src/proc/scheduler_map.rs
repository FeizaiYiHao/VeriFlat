use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
/// Approved TCB boundary: consume one owned 4K page permission and initialize that physical page
/// as a container `Scheduler` (`ASSERT_SCHEDULER_FITS_4K`). Keep the raw retype private; callers
/// use `retype_page_to_scheduler_and_insert`.
#[verifier::external_body]
fn retype_4k_page_perm_to_scheduler(page_ptr: PagePtr, scheduler: Scheduler, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: Tracked<PointsTo<Scheduler>>)
    requires
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        scheduler.inv(),
    ensures
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
        ret.view().value() == scheduler,
{
    unsafe { (page_ptr as *mut Scheduler).write(scheduler); }
    Tracked::assume_new()
}

impl UnLockedMap<usize, Scheduler> {
    pub fn retype_page_to_scheduler_and_insert(&mut self, page_ptr: PagePtr, scheduler: Scheduler, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).perms_wf(),
            !old(self).dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            scheduler.inv(),
            lctx.kernel_view_locking_state() is Acquire,
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(page_ptr),
            final(self).dom().contains(page_ptr),
            final(self).spec_index(page_ptr) == scheduler,
            forall|ptr: RwLockSchedulerPtr|
                #![trigger final(self).spec_index(ptr)]
                #![trigger old(self).spec_index(ptr)]
                #![trigger old(self).dom().contains(ptr)]
                #![trigger final(self).dom().contains(ptr)]
                old(self).dom().contains(ptr) ==> {
                    &&& final(self).dom().contains(ptr)
                    &&& final(self).spec_index(ptr) == old(self).spec_index(ptr)
                },
    {
        let Tracked(scheduler_perm) = retype_4k_page_perm_to_scheduler(page_ptr, scheduler, Tracked(page_perm));
        self.insert_with_perm(page_ptr, Tracked(scheduler_perm));
    }

    #[verifier::opaque]
    pub open spec fn typed_shard_lock_map_aligned(&self, held_locks: Map<(RwLockSchedulerPtr, CpuId), TypedHeldLock>, thread_id: LockThreadId) -> bool {
        &&& (forall|ptr: RwLockSchedulerPtr, cpu_id: CpuId|
            #![trigger held_locks.dom().contains((ptr, cpu_id))]
            #![trigger self.spec_index(ptr).shards.spec_index(cpu_id).view().locked_by_thread(thread_id)]
            held_locks.dom().contains((ptr, cpu_id)) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).shards.spec_index(cpu_id).view().locked_by_thread(thread_id)
            }
            && (held_locks.dom().contains((ptr, cpu_id)) ==> held_locks.index((ptr, cpu_id)).lock_id == self.spec_index(ptr).shards.lock_id_by_index(cpu_id)))
        &&& (forall|ptr: RwLockSchedulerPtr, cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Read)]
            #![trigger self.spec_index(ptr).shards.spec_index(cpu_id).view().rlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Read) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).shards.spec_index(cpu_id).view().rlocked_by_thread(thread_id)
            })
        &&& (forall|ptr: RwLockSchedulerPtr, cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Write)]
            #![trigger self.spec_index(ptr).shards.spec_index(cpu_id).view().wlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Write) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).shards.spec_index(cpu_id).view().wlocked_by_thread(thread_id)
            })
    }

    pub fn wlock_shard(&mut self, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(scheduler_ptr),
            old(self).spec_index(scheduler_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            wlock_requires(old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(), old(lctx)),
            old(lctx).lock_id_acyclic(old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), scheduler_ptr),
            final(self).spec_index(scheduler_ptr).inv(),
            final(self).spec_index(scheduler_ptr).owning_container == old(self).spec_index(scheduler_ptr).owning_container,
            final(self).spec_index(scheduler_ptr).shards.unchanged_except(&old(self).spec_index(scheduler_ptr).shards, cpu_id),
            final(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id) == old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id),
            wlock_ensures(old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(), final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(), old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id)),
    {
        let scheduler = self.borrow_mut(scheduler_ptr);
        scheduler.shards.wlock(cpu_id, Tracked(lctx), Ghost(KernelObjId::SchedulerShard(scheduler_ptr, cpu_id)))
    }

    pub fn wunlock_shard(&mut self, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(scheduler_ptr),
            old(self).spec_index(scheduler_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), scheduler_ptr),
            final(self).spec_index(scheduler_ptr).inv(),
            final(self).spec_index(scheduler_ptr).owning_container == old(self).spec_index(scheduler_ptr).owning_container,
            final(self).spec_index(scheduler_ptr).shards.unchanged_except(&old(self).spec_index(scheduler_ptr).shards, cpu_id),
            final(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id) == old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id),
            wunlock_ensures(old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(), final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id), old(self).spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id)),
    {
        let scheduler = self.borrow_mut(scheduler_ptr);
        scheduler.shards.wunlock(cpu_id, Tracked(lctx), lock_perm, Ghost(KernelObjId::SchedulerShard(scheduler_ptr, cpu_id)));
    }

    pub fn borrow_shard_typed<'a>(&'a self, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Ghost(held_locks): Ghost<Map<(RwLockSchedulerPtr, CpuId), TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a SchedulerShard)
        requires
            self.perms_wf(),
            self.dom().contains(scheduler_ptr),
            self.spec_index(scheduler_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            self.typed_shard_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().state() is WriteLock,
            typed_lock_map_contains_mode(held_locks, (scheduler_ptr, cpu_id), TypedLockMode::Write),
            lock_perm.view().lock_id() == self.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            *ret == self.spec_index(scheduler_ptr).shard(cpu_id),
    {
        assert(self.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view())) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
        self.borrow(scheduler_ptr).shards.borrow(cpu_id, lock_perm)
    }

    pub fn borrow_mut_shard_typed<'a>(&'a mut self, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Ghost(held_locks): Ghost<Map<(RwLockSchedulerPtr, CpuId), TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a mut SchedulerShard)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(scheduler_ptr),
            old(self).spec_index(scheduler_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).typed_shard_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held_locks, (scheduler_ptr, cpu_id), TypedLockMode::Write),
            lock_perm.view().lock_id() == old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), scheduler_ptr),
            final(self).spec_index(scheduler_ptr).owning_container == old(self).spec_index(scheduler_ptr).owning_container,
            final(self).spec_index(scheduler_ptr).shards.inv(),
            final(self).spec_index(scheduler_ptr).shards.entries_unchanged_except(&old(self).spec_index(scheduler_ptr).shards, cpu_id),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().is_init(),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view()),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view_rodata() == old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view_ghost() == old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view_ghost(),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == old(self).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed(),
            *ret == old(self).spec_index(scheduler_ptr).shard(cpu_id),
            final(self).spec_index(scheduler_ptr).shard(cpu_id) == *final(ret),
            final(self).typed_shard_lock_map_aligned(held_locks, lctx.thread_id()),
    {
        proof { reveal(UnLockedMap::typed_shard_lock_map_aligned); }
        let scheduler = self.borrow_mut(scheduler_ptr);
        scheduler.shards.borrow_mut(cpu_id, Tracked(lctx), lock_perm)
    }
}
}

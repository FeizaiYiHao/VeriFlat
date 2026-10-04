use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::simple_pptr::*;
use crate::*;

verus! {
/// Approved TCB boundary: initialize the second 4K of an installed container's 2M page as that
/// container's `CpuOfflineFlags` table. The container `RwLock` fits in the first 4K
/// (`ASSERT_CONTAINER_LOCK_FITS_4K`); `retype_container_page_tail_and_insert` keeps each table
/// pointer unique through `insert_with_perm`.
#[verifier::external_body]
fn retype_container_page_tail_to_offline_flags(container_map: &ContainerLockedMap, container_ptr: RwLockContainerPtr, flags: CpuOfflineFlags) -> (ret: Tracked<PointsTo<CpuOfflineFlags>>)
    requires
        container_map.dom().contains(container_ptr),
        page_ptr_2m_valid(container_ptr),
        flags.inv(),
    ensures
        ret.view().is_init(),
        ret.view().addr() == cpu_offline_flags_ptr(container_ptr),
        ret.view().value() == flags,
{
    unsafe { ((container_ptr + PAGE_SZ_4K) as *mut CpuOfflineFlags).write(flags); }
    Tracked::assume_new()
}

impl UnLockedMap<usize, CpuOfflineFlags> {
    pub fn retype_container_page_tail_and_insert(&mut self, container_map: &ContainerLockedMap, container_ptr: RwLockContainerPtr, flags: CpuOfflineFlags)
        requires
            old(self).perms_wf(),
            container_map.dom().contains(container_ptr),
            page_ptr_2m_valid(container_ptr),
            !old(self).dom().contains(cpu_offline_flags_ptr(container_ptr)),
            flags.inv(),
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(cpu_offline_flags_ptr(container_ptr)),
            final(self).dom().contains(cpu_offline_flags_ptr(container_ptr)),
            final(self).spec_index(cpu_offline_flags_ptr(container_ptr)) == flags,
            forall|ptr: RwLockCpuOfflineFlagsPtr|
                #![trigger final(self).spec_index(ptr)]
                #![trigger old(self).spec_index(ptr)]
                #![trigger old(self).dom().contains(ptr)]
                #![trigger final(self).dom().contains(ptr)]
                old(self).dom().contains(ptr) ==> {
                    &&& final(self).dom().contains(ptr)
                    &&& final(self).spec_index(ptr) == old(self).spec_index(ptr)
                },
    {
        let Tracked(flags_perm) = retype_container_page_tail_to_offline_flags(container_map, container_ptr, flags);
        self.insert_with_perm(container_ptr + 4096, Tracked(flags_perm));
    }

    #[verifier::opaque]
    pub open spec fn typed_flag_lock_map_aligned(&self, held_locks: Map<(RwLockCpuOfflineFlagsPtr, CpuId), TypedHeldLock>, thread_id: LockThreadId) -> bool {
        &&& (forall|ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId|
            #![trigger held_locks.dom().contains((ptr, cpu_id))]
            #![trigger self.spec_index(ptr).flags.spec_index(cpu_id).view().locked_by_thread(thread_id)]
            held_locks.dom().contains((ptr, cpu_id)) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).flags.spec_index(cpu_id).view().locked_by_thread(thread_id)
            }
            && (held_locks.dom().contains((ptr, cpu_id)) ==> held_locks.index((ptr, cpu_id)).lock_id == self.spec_index(ptr).flags.lock_id_by_index(cpu_id)))
        &&& (forall|ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Read)]
            #![trigger self.spec_index(ptr).flags.spec_index(cpu_id).view().rlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Read) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).flags.spec_index(cpu_id).view().rlocked_by_thread(thread_id)
            })
        &&& (forall|ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Write)]
            #![trigger self.spec_index(ptr).flags.spec_index(cpu_id).view().wlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Write) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).flags.spec_index(cpu_id).view().wlocked_by_thread(thread_id)
            })
    }

    pub fn wlock_flag(&mut self, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(flags_ptr),
            old(self).spec_index(flags_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            wlock_requires(old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view(), old(lctx)),
            old(lctx).lock_id_acyclic(old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), flags_ptr),
            final(self).spec_index(flags_ptr).inv(),
            final(self).spec_index(flags_ptr).owning_container == old(self).spec_index(flags_ptr).owning_container,
            final(self).spec_index(flags_ptr).flags.unchanged_except(&old(self).spec_index(flags_ptr).flags, cpu_id),
            final(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id) == old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id),
            wlock_ensures(
                old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view(), final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view(),
                old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), final(lctx), ret.view(),
            ),
            lock_ensures(old(lctx), final(lctx), old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id)),
    {
        let table = self.borrow_mut(flags_ptr);
        table.flags.wlock(cpu_id, Tracked(lctx), Ghost(KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id)))
    }

    pub fn wunlock_flag(&mut self, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(flags_ptr),
            old(self).spec_index(flags_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), flags_ptr),
            final(self).spec_index(flags_ptr).inv(),
            final(self).spec_index(flags_ptr).owning_container == old(self).spec_index(flags_ptr).owning_container,
            final(self).spec_index(flags_ptr).flags.unchanged_except(&old(self).spec_index(flags_ptr).flags, cpu_id),
            final(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id) == old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id),
            wunlock_ensures(old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view(), final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id), old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id)),
    {
        let table = self.borrow_mut(flags_ptr);
        table.flags.wunlock(cpu_id, Tracked(lctx), lock_perm, Ghost(KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id)));
    }

    pub fn read_flag(&self, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId, lock_perm: Tracked<&LockPerm>) -> (ret: bool)
        requires
            self.perms_wf(),
            self.dom().contains(flags_ptr),
            self.spec_index(flags_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            lock_perm.view().state() is WriteLock,
            self.spec_index(flags_ptr).flags.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view()),
        ensures
            ret == self.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().requested,
    {
        let table = self.borrow(flags_ptr);
        table.flags.borrow(cpu_id, lock_perm).requested
    }

    pub fn set_flag(&mut self, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId, value: bool, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(flags_ptr),
            old(self).spec_index(flags_ptr).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(lctx),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), flags_ptr),
            final(self).spec_index(flags_ptr).inv(),
            final(self).spec_index(flags_ptr).owning_container == old(self).spec_index(flags_ptr).owning_container,
            final(self).spec_index(flags_ptr).flags.entries_unchanged_except(&old(self).spec_index(flags_ptr).flags, cpu_id),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().requested == value,
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().index() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().index(),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().is_init(),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view_rodata() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view_ghost() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().view_ghost(),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().being_killed() == old(self).spec_index(flags_ptr).flags.spec_index(cpu_id).view().being_killed(),
            final(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id) == old(self).spec_index(flags_ptr).flags.lock_id_by_index(cpu_id),
            cpu_offline_requests_of(final(self).spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).spec_index(flags_ptr)).update(cpu_id as int, value),
    {
        let table = self.borrow_mut(flags_ptr);
        let flag = table.flags.borrow_mut(cpu_id, Tracked(lctx), lock_perm);
        flag.set(value);
        proof {
            reveal(cpu_offline_requests_of);
            assert_seqs_equal!(cpu_offline_requests_of(self.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).spec_index(flags_ptr)).update(cpu_id as int, value));
        }
    }
}
}

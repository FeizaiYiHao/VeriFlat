use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

/// TCB: retire a write-locked endpoint object and reclaim its 4k page as raw memory.
///
/// This is the inverse of the `retype_page_perm_to_rwlock` MINT. The object has
/// already left `ep_mp`, the caller exclusively write-holds its lock in the
/// release phase, and its waiter queue is empty, so it owns no thread node and
/// no thread can reach or wait on the lock. The held lock disappears from `lctx`
/// with the object.
#[verifier::external_body]
pub fn retype_endpoint_rwlock_to_4k_page_perm(
    endpoint_ptr: RwLockEndpointPtr, Tracked(endpoint_perm): Tracked<PointsTo<RwLock<Endpoint, (), (), ENDPOINT_HAS_KILL_STATE>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        endpoint_perm.is_init(),
        endpoint_perm.addr() == endpoint_ptr,
        endpoint_perm.value().is_init(),
        endpoint_perm.value().view().queue.len() == 0,
        endpoint_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
        ret.view().is_init(),
        ret.view().addr() == endpoint_ptr,
{
    Tracked::assume_new()
}

impl KernelK {
    /// Remove a write-locked endpoint with an empty queue from `ep_mp` and reclaim its page memory.
    pub fn remove_endpoint_and_reclaim_4k_page_perm(
        &mut self, endpoint_ptr: RwLockEndpointPtr, Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).ep_mp.perms_wf(),
            old(self).ep_mp.dom().contains(endpoint_ptr),
            old(self).ep_mp.spec_index(endpoint_ptr).is_init(),
            old(self).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0,
            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == old(lctx).thread_id(),
            lock_perm.lock_id() == old(self).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
            *final(self) == (KernelK { ep_mp: final(self).ep_mp, ..*old(self) }),
            final(self).ep_mp.perms_wf(),
            final(self).ep_mp.dom() =~= old(self).ep_mp.dom().remove(endpoint_ptr),
            forall|e: RwLockEndpointPtr| #![trigger final(self).ep_mp.spec_index(e)]
                final(self).ep_mp.dom().contains(e) ==> final(self).ep_mp.spec_index(e) == old(self).ep_mp.spec_index(e),
            forall|e: RwLockEndpointPtr| #![trigger final(self).ep_mp.lock_id_by_key(e)]
                final(self).ep_mp.dom().contains(e) ==> final(self).ep_mp.lock_id_by_key(e) == old(self).ep_mp.lock_id_by_key(e),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.view().is_init(),
            ret.view().addr() == endpoint_ptr,
    {
        proof { self.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), endpoint_ptr); }
        let Tracked(endpoint_perm) = self.ep_mp.remove_with_perm(endpoint_ptr);
        let ret = retype_endpoint_rwlock_to_4k_page_perm(endpoint_ptr, Tracked(endpoint_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof { assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        ret
    }
}
}

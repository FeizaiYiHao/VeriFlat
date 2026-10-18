use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

/// TCB: retire a write-locked, killed process object that has no child and no thread, and reclaim its 4k page as raw
/// memory.
///
/// This is the inverse of `retype_page_to_process_and_insert`. The object has already left `process_map`, the caller
/// exclusively write-holds its lock in the release phase, its parent's child list returned its in-page parent node, and
/// its own lists are empty, so it owns no other memory and no other thread can reach or wait on the lock. The held lock
/// disappears from `lctx` with the object.
#[verifier::external_body]
pub fn retype_process_rwlock_to_4k_page_perm(
    process_ptr: RwLockProcessPtr, Tracked(process_perm): Tracked<PointsTo<ProcessRwLock>>, Tracked(parent_node_perm): Tracked<PointsTo<Node<RwLockProcessPtr>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        process_perm.is_init(),
        process_perm.addr() == process_ptr,
        process_perm.value().is_init(),
        process_perm.value().being_killed(),
        process_perm.value().view().children.view().len() == 0,
        process_perm.value().view().owned_threads.view().len() == 0,
        parent_node_perm.is_init(),
        parent_node_perm.addr() == process_perm.value().view().parent_linkedlist_node.addr(),
        process_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(process_ptr)),
        ret.view().is_init(),
        ret.view().addr() == process_ptr,
{
    Tracked::assume_new()
}

impl KernelK {
    pub fn retype_page_to_process_and_insert(&mut self, page_ptr: PagePtr, process_value: Process, rodata: ReadOnlyNode<ProcessRO>, process_ghost: ProcessGhost, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).prc_mp.perms_wf(),
            !old(self).prc_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            process_value.inv(),
            process_value.children.view().no_duplicates(),
            !process_value.children.view().contains(page_ptr),
            process_ghost.uppertree_seq.view().no_duplicates(),
            process_ghost.uppertree_seq.view().len() == rodata.view().depth,
            old(self).prc_mp.typed_lock_map_aligned(old(lctx).process_lock_map(), old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).pt_mp == old(self).pt_mp,
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).pcid_needflush == old(self).pcid_needflush,
            final(self).cpu_published == old(self).cpu_published,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).cpu_set_mp == old(self).cpu_set_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_offline_mp == old(self).cpu_offline_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).prc_mp.perms_wf(),
            process_perms_wf(old(self).prc_mp) ==> process_perms_wf(final(self).prc_mp),
            final(self).prc_mp.dom() =~= old(self).prc_mp.dom().insert(page_ptr),
            forall|ptr: RwLockProcessPtr|
                #![trigger final(self).prc_mp.spec_index(ptr)]
                #![trigger old(self).prc_mp.spec_index(ptr)]
                #![trigger old(self).prc_mp.dom().contains(ptr)]
                #![trigger final(self).prc_mp.dom().contains(ptr)]
                old(self).prc_mp.dom().contains(ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(ptr)
                    &&& final(self).prc_mp.spec_index(ptr) == old(self).prc_mp.spec_index(ptr)
                },
            forall|ptr: RwLockProcessPtr|
                #![trigger old(self).prc_mp.lock_id_by_key(ptr)]
                #![trigger final(self).prc_mp.lock_id_by_key(ptr)]
                old(self).prc_mp.dom().contains(ptr) ==> final(self).prc_mp.lock_id_by_key(ptr) == old(self).prc_mp.lock_id_by_key(ptr),
            final(self).prc_mp.spec_index(page_ptr).is_init(),
            final(self).prc_mp.spec_index(page_ptr).view() == process_value,
            final(self).prc_mp.spec_index(page_ptr).view_rodata() == rodata,
            final(self).prc_mp.spec_index(page_ptr).view_ghost() == process_ghost,
            !final(self).prc_mp.spec_index(page_ptr).being_killed(),
            typed_lock_map_contains_mode(final(lctx).process_lock_map(), page_ptr, TypedLockMode::Write),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).prc_mp.lock_id_by_key(page_ptr),
            final(self).prc_mp.lock_id_by_key(page_ptr) == (LockId { container: rodata.container_depth(), process: rodata.process_depth(), major: process_value.current_lock_major(), minor: page_ptr }),
            final(self).prc_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Process(page_ptr), TypedHeldLock { lock_id: final(self).prc_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
            final(self).prc_mp.typed_lock_map_aligned(final(lctx).process_lock_map(), final(lctx).thread_id()),
    {
        let (Tracked(process_rwlock_perm), Tracked(process_perm)) = retype_page_perm_to_rwlock::<Process, ReadOnlyNode<ProcessRO>, ProcessGhost, PROCESS_HAS_KILL_STATE>(
            page_ptr, process_value, rodata, Ghost(process_ghost), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Process(page_ptr)));
        self.prc_mp.insert_with_perm(page_ptr, Tracked(process_rwlock_perm));
        proof { assert(process_perms_wf(old(self).prc_mp) ==> process_perms_wf(self.prc_mp)) by { reveal(process_perms_wf); }; assert(self.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        Tracked(process_perm)
    }

    /// Remove the write-held, killed process `process_ptr`, which has no child and no thread, from `prc_mp` and reclaim
    /// its page memory together with the parent node its parent's child list returned.
    pub fn remove_process_and_reclaim_4k_page_perm(
        &mut self, process_ptr: RwLockProcessPtr, Tracked(parent_node_perm): Tracked<PointsTo<Node<RwLockProcessPtr>>>,
        Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).prc_mp.perms_wf(),
            old(self).prc_mp.dom().contains(process_ptr),
            old(self).prc_mp.spec_index(process_ptr).is_init(),
            old(self).prc_mp.spec_index(process_ptr).being_killed(),
            old(self).prc_mp.spec_index(process_ptr).view().children.view().len() == 0,
            old(self).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 0,
            parent_node_perm.is_init(),
            parent_node_perm.addr() == old(self).prc_mp.spec_index(process_ptr).view().parent_linkedlist_node.addr(),
            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == old(lctx).thread_id(),
            lock_perm.lock_id() == old(self).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(process_ptr)),
            *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
            final(self).prc_mp.perms_wf(),
            process_perms_wf(old(self).prc_mp) ==> process_perms_wf(final(self).prc_mp),
            final(self).prc_mp.dom() =~= old(self).prc_mp.dom().remove(process_ptr),
            forall|p: RwLockProcessPtr| #![trigger final(self).prc_mp.spec_index(p)] final(self).prc_mp.dom().contains(p) ==> final(self).prc_mp.spec_index(p) == old(self).prc_mp.spec_index(p),
            forall|p: RwLockProcessPtr| #![trigger final(self).prc_mp.lock_id_by_key(p)] final(self).prc_mp.dom().contains(p) ==> final(self).prc_mp.lock_id_by_key(p) == old(self).prc_mp.lock_id_by_key(p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.view().is_init(),
            ret.view().addr() == process_ptr,
    {
        proof { self.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); }
        let Tracked(process_perm) = self.prc_mp.remove_with_perm(process_ptr);
        let ret = retype_process_rwlock_to_4k_page_perm(process_ptr, Tracked(process_perm), Tracked(parent_node_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof {
            assert(process_perms_wf(old(self).prc_mp) ==> process_perms_wf(self.prc_mp)) by { reveal(process_perms_wf); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        ret
    }
}
} // verus!

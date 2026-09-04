use vstd::prelude::*;
verus! {

use crate::*;

impl KernelK {
    pub fn retype_page_to_process_and_insert(
        &mut self,
        page_ptr: PagePtr,
        process_value: Process,
        rodata: ReadOnlyNode<ProcessRO>,
        process_ghost: ProcessGhost,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).prc_mp.perms_wf(),
            !old(self).prc_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            process_value.inv(),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).pt_mp == old(self).pt_mp,
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).prc_mp.perms_wf(),
            final(self).prc_mp.dom() =~= old(self).prc_mp.dom().insert(page_ptr),
            forall|ptr: RwLockProcessPtr| #![auto]
                old(self).prc_mp.dom().contains(ptr) ==> final(self).prc_mp.spec_index(ptr) == old(self).prc_mp.spec_index(ptr),
            forall|ptr: RwLockProcessPtr|
                #![trigger old(self).prc_mp.lock_id_by_key(ptr)]
                #![trigger final(self).prc_mp.lock_id_by_key(ptr)]
                old(self).prc_mp.dom().contains(ptr) ==> final(self).prc_mp.lock_id_by_key(ptr) == old(self).prc_mp.lock_id_by_key(ptr),
            final(self).prc_mp.spec_index(page_ptr).is_init(),
            final(self).prc_mp.spec_index(page_ptr).view() == process_value,
            final(self).prc_mp.spec_index(page_ptr).view_rodata() == rodata,
            final(self).prc_mp.spec_index(page_ptr).view_ghost() == process_ghost,
            !final(self).prc_mp.spec_index(page_ptr).being_killed(),
            final(self).prc_mp.spec_index(page_ptr).wlocked_by(final(lctx)),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).prc_mp.lock_id_by_key(page_ptr),
            final(self).prc_mp.lock_id_by_key(page_ptr) == (LockId {
                container: rodata.container_depth(),
                process: rodata.process_depth(),
                major: process_value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).prc_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).prc_mp.lock_id_by_key(page_ptr), KernelObjId::Process(page_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Process(page_ptr), TypedHeldLock {
                lock_id: final(self).prc_mp.lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
    {
        proof { assert(!old(lctx).process_lock_map().dom().contains(page_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        let (Tracked(process_rwlock_perm), Tracked(process_perm)) = retype_page_perm_to_rwlock::<Process, ReadOnlyNode<ProcessRO>, ProcessGhost, PROCESS_HAS_KILL_STATE>(
            page_ptr, process_value, rodata, Ghost(process_ghost), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Process(page_ptr)),
        );
        self.prc_mp.insert_with_perm(page_ptr, Tracked(process_rwlock_perm));
        proof { assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        Tracked(process_perm)
    }
}
} // verus!

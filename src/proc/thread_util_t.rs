use vstd::prelude::*;
verus! {

use crate::*;
use vstd::simple_pptr::*;

    /// TCB: reinterpret a raw 4k page's memory as a fresh, WRITE-LOCKED
    /// `RwLock<Thread>` and mint the corresponding `LockPerm`.
    ///
    /// This is a MINT, not an acquire: the page is exclusively ours (staged,
    /// slot write-locked), so no other thread can contend on the new thread
    /// lock and no wait cycle is possible. The retype reinterprets the page's
    /// physical memory as a `ThreadRwLock`, initializes it with `thread_value`,
    /// sets the lock state to Write, and registers `Thread(page_ptr)` in `lctx`.
    ///
    /// The `thread_map` domain growth is done separately by
    /// `LockedMap::insert_with_perm`; the page-state flip and process unstage
    /// stay in verified code.
    #[verifier::external_body]
    pub fn retype_page_perm_to_thread(
        page_ptr: PagePtr,
        thread_value: Thread,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: (Tracked<PointsTo<ThreadRwLock>>, Tracked<LockPerm>))
        requires
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            thread_value.inv(),
        ensures
            // ---- the ThreadRwLock: initialized, write-locked, holds thread_value ----
            ret.0.view().addr() == page_ptr,
            ret.0.view().is_init(),
            ret.0.view().value().is_init(),
            ret.0.view().value().view() == thread_value,
            ret.0.view().value().being_killed() == false,
            ret.0.view().value().locking_thread() == (RwLockState::Write {
                thread_id: final(lctx).thread_id(),
                lock_id: ret.1.view().lock_id(),
            }),
            // ---- the LockPerm ----
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().ordering_lock_id() == (LockId{
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: thread_value.current_lock_major(),
                minor: page_ptr,
            }),
            // ---- lctx: the thread lock id registered under obj_id ----
            lock_ensures(old(lctx), final(lctx), thread_value, LockId{
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: thread_value.current_lock_major(),
                minor: page_ptr,
            }, obj_id.view()),
    {
        unimplemented!()
    }

impl KernelK {
    pub fn retype_page_to_thread_and_insert(
        &mut self,
        page_ptr: PagePtr,
        thread_value: Thread,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).thr_mp.perms_wf(),
            !old(self).thr_mp.dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            thread_value.inv(),
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
            final(self).prc_mp == old(self).prc_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).thr_mp.perms_wf(),
            final(self).thr_mp.dom() =~= old(self).thr_mp.dom().insert(page_ptr),
            final(self).thr_mp.dom().contains(page_ptr),
            forall|ptr: RwLockThreadPtr| #![auto]
                old(self).thr_mp.dom().contains(ptr) ==> final(self).thr_mp.spec_index(ptr) == old(self).thr_mp.spec_index(ptr),
            forall|ptr: RwLockThreadPtr|
                #![trigger old(self).thr_mp.lock_id_by_key(ptr)]
                #![trigger final(self).thr_mp.lock_id_by_key(ptr)]
                old(self).thr_mp.dom().contains(ptr) ==> final(self).thr_mp.lock_id_by_key(ptr) == old(self).thr_mp.lock_id_by_key(ptr),
            final(self).thr_mp.spec_index(page_ptr).is_init(),
            final(self).thr_mp.spec_index(page_ptr).view() == thread_value,
            final(self).thr_mp.spec_index(page_ptr).being_killed() == false,
            final(self).thr_mp.spec_index(page_ptr).wlocked_by(final(lctx)),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).thr_mp.lock_id_by_key(page_ptr),
            final(self).thr_mp.lock_id_by_key(page_ptr) == (LockId {
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: thread_value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).thr_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).thr_mp.lock_id_by_key(page_ptr), KernelObjId::Thread(page_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(page_ptr), TypedHeldLock {
                lock_id: final(self).thr_mp.lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
    {
        proof {
            assert(!old(lctx).thread_lock_map().dom().contains(page_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        let (Tracked(thread_rwlock_perm), Tracked(thread_perm)) = retype_page_perm_to_thread(
            page_ptr, thread_value, Tracked(page_perm), Tracked(&mut *lctx),
            Ghost(KernelObjId::Thread(page_ptr)),
        );
        self.thr_mp.insert_with_perm(page_ptr, Tracked(thread_rwlock_perm), (), Ghost(()), Ghost(()));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        Tracked(thread_perm)
    }
}
}

use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

    /// TCB: reinterpret a raw 4k page's memory as a fresh, WRITE-LOCKED
    /// `RwLock<T>` and mint the corresponding `LockPerm`.
    ///
    /// This is a MINT, not an acquire: the page is exclusively ours (staged,
    /// slot write-locked), so no other thread can contend on the new object
    /// lock and no wait cycle is possible. The retype preserves the current
    /// kernel-view locking phase while registering the fresh object in `lctx`.
    ///
    /// The `thread_map` domain growth is done separately by
    /// `LockedMap::insert_with_perm`; the page-state flip and process unstage
    /// stay in verified code.
    #[verifier::external_body]
    pub fn retype_page_perm_to_rwlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool>(
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: (Tracked<PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked<LockPerm>))
        requires
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret.0.view().addr() == page_ptr,
            ret.0.view().is_init(),
            ret.0.view().value().is_init(),
            ret.0.view().value().view() == value,
            ret.0.view().value().view_rodata() == rodata,
            ret.0.view().value().view_ghost() == ghost,
            ret.0.view().value().being_killed() == false,
            ret.0.view().value().locking_thread() == (RwLockState::Write {
                thread_id: final(lctx).thread_id(),
                lock_id: ret.1.view().lock_id(),
            }),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().ordering_lock_id() == (LockId{
                container: if rodata.container_depth() != LockOwnerId::NotApp { rodata.container_depth() } else { value.container_depth() },
                process: if rodata.process_depth() != LockOwnerId::NotApp { rodata.process_depth() } else { value.process_depth() },
                major: value.current_lock_major(),
                minor: page_ptr,
            }),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock {
                lock_id: ret.1.view().ordering_lock_id(),
                mode: TypedLockMode::Write,
            }),
    {
        unimplemented!()
    }

    /// Approved TCB boundary for retyping one owned 2M page; callers use `retype_2m_and_insert`.
    #[verifier::external_body]
    fn retype_page_perm_2m_to_rwlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool>(
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm2m>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: (Tracked<PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked<LockPerm>))
        requires
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret.0.view().addr() == page_ptr,
            ret.0.view().is_init(),
            ret.0.view().value().is_init(),
            ret.0.view().value().view() == value,
            ret.0.view().value().view_rodata() == rodata,
            ret.0.view().value().view_ghost() == ghost,
            ret.0.view().value().being_killed() == false,
            ret.0.view().value().locking_thread() == (RwLockState::Write {
                thread_id: final(lctx).thread_id(),
                lock_id: ret.1.view().lock_id(),
            }),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().ordering_lock_id() == (LockId{
                container: if rodata.container_depth() != LockOwnerId::NotApp { rodata.container_depth() } else { value.container_depth() },
                process: if rodata.process_depth() != LockOwnerId::NotApp { rodata.process_depth() } else { value.process_depth() },
                major: value.current_lock_major(),
                minor: page_ptr,
            }),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock {
                lock_id: ret.1.view().ordering_lock_id(),
                mode: TypedLockMode::Write,
            }),
    {
        unimplemented!()
    }

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool>
    LockedMap<usize, T, ROT, GhostT, HAS_KILL_STATE> {
    pub fn retype_4k_and_insert(
        &mut self,
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            !old(self).dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            old(lctx).typed_lock_entry(obj_id.view()) is None,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(page_ptr),
            final(self).dom().contains(page_ptr),
            forall|ptr: usize|
                #![trigger old(self).dom().contains(ptr)]
                old(self).dom().contains(ptr) ==> {
                    &&& final(self).dom().contains(ptr)
                    &&& final(self).spec_index(ptr) == old(self).spec_index(ptr)
                },
            final(self).spec_index(page_ptr).view() == value,
            final(self).spec_index(page_ptr).view_rodata() == rodata,
            final(self).spec_index(page_ptr).view_ghost() == ghost,
            final(self).spec_index(page_ptr).is_init(),
            final(self).spec_index(page_ptr).inv(),
            !final(self).spec_index(page_ptr).being_killed(),
            final(self).lock_id_by_key(page_ptr) == (LockId {
                container: if rodata.container_depth() != LockOwnerId::NotApp {
                    rodata.container_depth()
                } else {
                    value.container_depth()
                },
                process: if rodata.process_depth() != LockOwnerId::NotApp {
                    rodata.process_depth()
                } else {
                    value.process_depth()
                },
                major: value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).spec_index(page_ptr).wlocked_by(final(lctx)),
            final(self).spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).lock_id_by_key(page_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock {
                lock_id: final(self).lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
    {
        let (Tracked(rwlock_perm), Tracked(lock_perm)) = retype_page_perm_to_rwlock::<T, ROT, GhostT, HAS_KILL_STATE>(
            page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut *lctx), obj_id,
        );
        self.insert_with_perm(page_ptr, Tracked(rwlock_perm));
        Tracked(lock_perm)
    }

    pub fn retype_2m_and_insert(
        &mut self,
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm2m>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            !old(self).dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            old(lctx).typed_lock_entry(obj_id.view()) is None,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(page_ptr),
            final(self).dom().contains(page_ptr),
            forall|ptr: usize|
                #![trigger old(self).dom().contains(ptr)]
                old(self).dom().contains(ptr) ==> {
                    &&& final(self).dom().contains(ptr)
                    &&& final(self).spec_index(ptr) == old(self).spec_index(ptr)
                },
            final(self).spec_index(page_ptr).view() == value,
            final(self).spec_index(page_ptr).view_rodata() == rodata,
            final(self).spec_index(page_ptr).view_ghost() == ghost,
            final(self).spec_index(page_ptr).is_init(),
            final(self).spec_index(page_ptr).inv(),
            !final(self).spec_index(page_ptr).being_killed(),
            final(self).lock_id_by_key(page_ptr) == (LockId {
                container: if rodata.container_depth() != LockOwnerId::NotApp {
                    rodata.container_depth()
                } else {
                    value.container_depth()
                },
                process: if rodata.process_depth() != LockOwnerId::NotApp {
                    rodata.process_depth()
                } else {
                    value.process_depth()
                },
                major: value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).spec_index(page_ptr).wlocked_by(final(lctx)),
            final(self).spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).lock_id_by_key(page_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock {
                lock_id: final(self).lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
    {
        let (Tracked(rwlock_perm), Tracked(lock_perm)) = retype_page_perm_2m_to_rwlock::<T, ROT, GhostT, HAS_KILL_STATE>(
            page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut *lctx), obj_id,
        );
        self.insert_with_perm(page_ptr, Tracked(rwlock_perm));
        Tracked(lock_perm)
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>
    LockedMap<usize, T, ROT, GhostT, NO_KILL_STATE> {
    #[verifier::spinoff_prover]
    pub fn retype_4k_as_unlocked_singleton(
        &mut self,
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm4k>,
        cpu_id: CpuId,
        lock_thread_id: LockThreadId,
        Ghost(obj_id): Ghost<KernelObjId>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().is_empty(),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= set![page_ptr],
            final(self).spec_index(page_ptr).view() == value,
            final(self).spec_index(page_ptr).view_rodata() == rodata,
            final(self).spec_index(page_ptr).view_ghost() == ghost,
            final(self).spec_index(page_ptr).is_init(),
            final(self).spec_index(page_ptr).inv(),
            !final(self).spec_index(page_ptr).being_killed(),
            final(self).spec_index(page_ptr).locking_thread() is None,
    {
        let tracked mut lctx =
            LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_4k_and_insert(
            page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id),
        );
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }

    #[verifier::spinoff_prover]
    pub fn retype_2m_as_unlocked_singleton(
        &mut self,
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm2m>,
        cpu_id: CpuId,
        lock_thread_id: LockThreadId,
        Ghost(obj_id): Ghost<KernelObjId>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().is_empty(),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= set![page_ptr],
            final(self).spec_index(page_ptr).view() == value,
            final(self).spec_index(page_ptr).view_rodata() == rodata,
            final(self).spec_index(page_ptr).view_ghost() == ghost,
            final(self).spec_index(page_ptr).is_init(),
            final(self).spec_index(page_ptr).inv(),
            !final(self).spec_index(page_ptr).being_killed(),
            final(self).spec_index(page_ptr).locking_thread() is None,
    {
        let tracked mut lctx =
            LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_2m_and_insert(
            page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id),
        );
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>
    LockedMap<usize, T, ROT, GhostT, HAS_KILL_STATE> {
    #[verifier::spinoff_prover]
    pub fn retype_4k_as_unlocked_singleton(
        &mut self,
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm4k>,
        cpu_id: CpuId,
        lock_thread_id: LockThreadId,
        Ghost(obj_id): Ghost<KernelObjId>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().is_empty(),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= set![page_ptr],
            final(self).spec_index(page_ptr).view() == value,
            final(self).spec_index(page_ptr).view_rodata() == rodata,
            final(self).spec_index(page_ptr).view_ghost() == ghost,
            final(self).spec_index(page_ptr).is_init(),
            final(self).spec_index(page_ptr).inv(),
            !final(self).spec_index(page_ptr).being_killed(),
            final(self).spec_index(page_ptr).locking_thread() is None,
    {
        let tracked mut lctx =
            LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_4k_and_insert(
            page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id),
        );
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }

    #[verifier::spinoff_prover]
    pub fn retype_2m_as_unlocked_singleton(
        &mut self,
        page_ptr: PagePtr,
        value: T,
        rodata: ROT,
        Ghost(ghost): Ghost<GhostT>,
        Tracked(page_perm): Tracked<PagePerm2m>,
        cpu_id: CpuId,
        lock_thread_id: LockThreadId,
        Ghost(obj_id): Ghost<KernelObjId>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().is_empty(),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= set![page_ptr],
            final(self).spec_index(page_ptr).view() == value,
            final(self).spec_index(page_ptr).view_rodata() == rodata,
            final(self).spec_index(page_ptr).view_ghost() == ghost,
            final(self).spec_index(page_ptr).is_init(),
            final(self).spec_index(page_ptr).inv(),
            !final(self).spec_index(page_ptr).being_killed(),
            final(self).spec_index(page_ptr).locking_thread() is None,
    {
        let tracked mut lctx =
            LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_2m_and_insert(
            page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id),
        );
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }
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
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            *final(self) == (KernelK {
                thr_mp: final(self).thr_mp,
                ..*old(self)
            }),
            final(self).thr_mp.perms_wf(),
            final(self).thr_mp.dom() =~= old(self).thr_mp.dom().insert(page_ptr),
            final(self).thr_mp.dom().contains(page_ptr),
            forall|ptr: RwLockThreadPtr|
                #![trigger old(self).thr_mp.dom().contains(ptr)]
                old(self).thr_mp.dom().contains(ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(ptr)
                    &&& final(self).thr_mp.spec_index(ptr)
                        == old(self).thr_mp.spec_index(ptr)
                },
            final(self).thr_mp.spec_index(page_ptr).is_init(),
            final(self).thr_mp.spec_index(page_ptr).view() == thread_value,
            final(self).thr_mp.spec_index(page_ptr).being_killed() == false,
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), page_ptr, TypedLockMode::Write),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).thr_mp.lock_id_by_key(page_ptr),
            final(self).thr_mp.lock_id_by_key(page_ptr) == (LockId {
                container: thread_value.container_depth(),
                process: thread_value.process_depth(),
                major: thread_value.current_lock_major(),
                minor: page_ptr,
            }),
            final(self).thr_mp.spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(page_ptr), TypedHeldLock {
                lock_id: final(self).thr_mp.lock_id_by_key(page_ptr),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(self), final(lctx)),
    {
        proof {
            assert(
                !old(lctx).thread_lock_map().dom().contains(page_ptr)
            ) by {
                reveal(LockedMap::typed_lock_map_aligned);
            };
        }
        let Tracked(thread_perm) = self.thr_mp.retype_4k_and_insert(
            page_ptr, thread_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)),
        );
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        Tracked(thread_perm)
    }
}
}

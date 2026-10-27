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
    page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>,
) -> (ret: (Tracked<PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked<LockPerm>))
    requires
        !(rodata.container_source() is Dynamic),
        !(rodata.process_source() is Dynamic),
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        value.inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret.0.view().addr() == page_ptr,
        ret.0.view().is_init(),
        ret.0.view().value().is_init(),
        ret.0.view().value().view() == value,
        ret.0.view().value().view_rodata() == rodata,
        ret.0.view().value().view_ghost() == ghost,
        ret.0.view().value().control() == LockControl::Clear,
        ret.0.view().value().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.view().lock_id() }),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().ordering_lock_id() == (LockId {
            container: match rodata.container_source() { OwnerSource::Payload => value.container_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => LockOwnerId::None },
            process: match rodata.process_source() { OwnerSource::Payload => value.process_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => LockOwnerId::None },
            major: value.current_lock_major(), minor: seq![page_ptr],
        }),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: ret.1.view().ordering_lock_id(), mode: TypedLockMode::Write }),
{
    unsafe { (page_ptr as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>).write(RwLock::new_wlocked_for_retype(value, rodata, LockControl::Clear)); }
    (Tracked::assume_new(), Tracked::assume_new())
}

/// TCB: retire a write-locked thread object and reclaim its 4k page as raw memory.
///
/// This is the inverse of the `retype_page_perm_to_rwlock` MINT. The object has
/// already left `thread_map`, the caller exclusively write-holds its lock in the
/// release phase, its process list returned the in-page process node, and its
/// other in-page nodes are not linked anywhere, so no other thread can reach or
/// wait on the lock. The held lock disappears from `lctx` with the object.
#[verifier::external_body]
pub fn retype_thread_rwlock_to_4k_page_perm(
    thread_ptr: RwLockThreadPtr, Tracked(thread_perm): Tracked<PointsTo<ThreadRwLock>>, Tracked(proc_node_perm): Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        thread_perm.is_init(),
        thread_perm.addr() == thread_ptr,
        thread_perm.value().is_init(),
        thread_perm.value().view().scheduler_linkedlist_node.is_init(),
        thread_perm.value().view().endpoint_linkedlist_node.is_init(),
        proc_node_perm.is_init(),
        proc_node_perm.addr() == thread_perm.value().view().proc_linkedlist_node.addr(),
        thread_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr)),
        ret.view().is_init(),
        ret.view().addr() == thread_ptr,
{
    Tracked::assume_new()
}

/// Approved TCB boundary for retyping one owned 2M page; callers use `retype_2m_and_insert`. A dynamic lock is created
/// write-held under the concrete `LockOwnerId::Some` owner recorded in `control`; every other lock is created with a
/// clear control word.
#[verifier::external_body]
fn retype_page_perm_2m_to_rwlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool>(
    page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm2m>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>,
    control: LockControl,
) -> (ret: (Tracked<PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked<LockPerm>))
    requires
        !(rodata.container_source() is Dynamic),
        (rodata.process_source() is Dynamic) == (control is DynamicProcess),
        !(control is Killed),
        control is DynamicProcess ==> control->DynamicProcess_0 is Some,
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        value.inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret.0.view().addr() == page_ptr,
        ret.0.view().is_init(),
        ret.0.view().value().is_init(),
        ret.0.view().value().view() == value,
        ret.0.view().value().view_rodata() == rodata,
        ret.0.view().value().view_ghost() == ghost,
        ret.0.view().value().control() == control,
        ret.0.view().value().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.view().lock_id() }),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().ordering_lock_id() == (LockId {
            container: match rodata.container_source() { OwnerSource::Payload => value.container_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => LockOwnerId::None },
            process: match rodata.process_source() { OwnerSource::Payload => value.process_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => control->DynamicProcess_0 },
            major: value.current_lock_major(), minor: seq![page_ptr],
        }),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: ret.1.view().ordering_lock_id(), mode: TypedLockMode::Write }),
{
    unsafe { (page_ptr as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>).write(RwLock::new_wlocked_for_retype(value, rodata, control)); }
    (Tracked::assume_new(), Tracked::assume_new())
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool>
    LockedMap<usize, T, ROT, GhostT, HAS_KILL_STATE> {
    pub fn retype_4k_and_insert(&mut self, page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            !(rodata.container_source() is Dynamic),
            !(rodata.process_source() is Dynamic),
            old(self).perms_wf(),
            !old(self).dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            old(lctx).typed_lock_entry(obj_id.view()) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
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
            final(self).spec_index(page_ptr).control() == LockControl::Clear,
            final(self).lock_id_by_key(page_ptr) == (LockId {
                container: match rodata.container_source() { OwnerSource::Payload => value.container_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => LockOwnerId::None },
                process: match rodata.process_source() { OwnerSource::Payload => value.process_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => LockOwnerId::None },
                major: value.current_lock_major(), minor: seq![page_ptr],
            }),
            final(self).spec_index(page_ptr).wlocked_by(final(lctx)),
            final(self).spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).lock_id_by_key(page_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: final(self).lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
    {
        let (Tracked(rwlock_perm), Tracked(lock_perm)) = retype_page_perm_to_rwlock::<T, ROT, GhostT, HAS_KILL_STATE>(page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut *lctx), obj_id);
        self.insert_with_perm(page_ptr, Tracked(rwlock_perm));
        Tracked(lock_perm)
    }

    pub fn retype_2m_and_insert(&mut self, page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm2m>,
        Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>, control: LockControl) -> (ret: Tracked<LockPerm>)
        requires
            !(rodata.container_source() is Dynamic),
            (rodata.process_source() is Dynamic) == (control is DynamicProcess),
            !(control is Killed),
            control is DynamicProcess ==> control->DynamicProcess_0 is Some,
            old(self).perms_wf(),
            !old(self).dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            value.inv(),
            old(lctx).typed_lock_entry(obj_id.view()) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
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
            final(self).spec_index(page_ptr).control() == control,
            final(self).lock_id_by_key(page_ptr) == (LockId {
                container: match rodata.container_source() { OwnerSource::Payload => value.container_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => LockOwnerId::None },
                process: match rodata.process_source() { OwnerSource::Payload => value.process_depth(), OwnerSource::Fixed(owner) => owner, OwnerSource::Dynamic => control->DynamicProcess_0 },
                major: value.current_lock_major(), minor: seq![page_ptr],
            }),
            final(self).spec_index(page_ptr).wlocked_by(final(lctx)),
            final(self).spec_index(page_ptr).write_lock_perm_match(&ret.view()),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).lock_id_by_key(page_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: final(self).lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
    {
        let (Tracked(rwlock_perm), Tracked(lock_perm)) = retype_page_perm_2m_to_rwlock::<T, ROT, GhostT, HAS_KILL_STATE>(page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut *lctx), obj_id, control);
        self.insert_with_perm(page_ptr, Tracked(rwlock_perm));
        Tracked(lock_perm)
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>
    LockedMap<usize, T, ROT, GhostT, NO_KILL_STATE> {
    #[verifier::spinoff_prover]
    pub fn retype_4k_as_unlocked_singleton(&mut self, page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm4k>, cpu_id: CpuId, lock_thread_id: LockThreadId, Ghost(obj_id): Ghost<KernelObjId>)
        requires
            !(rodata.container_source() is Dynamic),
            !(rodata.process_source() is Dynamic),
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
        let tracked mut lctx = LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_4k_and_insert(page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id));
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }

    #[verifier::spinoff_prover]
    pub fn retype_2m_as_unlocked_singleton(&mut self, page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm2m>, cpu_id: CpuId, lock_thread_id: LockThreadId, Ghost(obj_id): Ghost<KernelObjId>)
        requires
            !(rodata.container_source() is Dynamic),
            !(rodata.process_source() is Dynamic),
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
        let tracked mut lctx = LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_2m_and_insert(page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id), LockControl::Clear);
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>
    LockedMap<usize, T, ROT, GhostT, HAS_KILL_STATE> {
    #[verifier::spinoff_prover]
    pub fn retype_4k_as_unlocked_singleton(&mut self, page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm4k>, cpu_id: CpuId, lock_thread_id: LockThreadId, Ghost(obj_id): Ghost<KernelObjId>)
        requires
            !(rodata.container_source() is Dynamic),
            !(rodata.process_source() is Dynamic),
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
        let tracked mut lctx = LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_4k_and_insert(page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id));
        self.wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }

    /// Boot-only: retype a dynamic lock held under the concrete owner `requested`, then release it.
    #[verifier::spinoff_prover]
    pub fn retype_2m_as_unlocked_singleton(&mut self, page_ptr: PagePtr, value: T, rodata: ROT, Ghost(ghost): Ghost<GhostT>, Tracked(page_perm): Tracked<PagePerm2m>,
        cpu_id: CpuId, lock_thread_id: LockThreadId, Ghost(obj_id): Ghost<KernelObjId>, requested: LockOwnerId)
        requires
            !(rodata.container_source() is Dynamic),
            rodata.process_source() is Dynamic,
            requested is Some,
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
        let tracked mut lctx = LocalContext::new_bootstrap(cpu_id, lock_thread_id);
        let Tracked(lock_perm) = self.retype_2m_and_insert(page_ptr, value, rodata, Ghost(ghost), Tracked(page_perm), Tracked(&mut lctx), Ghost(obj_id), LockControl::DynamicProcess(requested));
        self.dynamic_wunlock(page_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(obj_id));
    }
}

/// Boot-only: retype the root thread page in place, then schedule it on CPU 0 so
/// both intrusive nodes take their final in-page addresses before any list uses them.
pub fn retype_boot_root_thread(thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, thread_value: Thread, initial_regs: &Registers,
    Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>, usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        old(thread_map).perms_wf(),
        old(thread_map).dom().is_empty(),
        page_perm.is_init(),
        page_perm.addr() == thread_ptr,
        thread_value.inv(),
        thread_value.state is RUNNING,
        thread_value.scheduler_linkedlist_node.is_init(),
        thread_value.proc_linkedlist_node.is_init(),
        0 < NUM_CPUS,
    ensures
        final(thread_map).perms_wf(),
        final(thread_map).dom() =~= set![thread_ptr],
        final(thread_map).spec_index(thread_ptr).view() == (Thread {
            state: ThreadState::SCHEDULED { cpu_id: 0 }, last_cpu: 0, trap_frame: final(thread_map).spec_index(thread_ptr).view().trap_frame,
            scheduler_linkedlist_node: final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node,
            proc_linkedlist_node: final(thread_map).spec_index(thread_ptr).view().proc_linkedlist_node,
            ..thread_value
        }),
        final(thread_map).spec_index(thread_ptr).view().trap_frame.is_some(),
        *final(thread_map).spec_index(thread_ptr).view().trap_frame.get_some_0() == *initial_regs,
        !final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node.is_init(),
        !final(thread_map).spec_index(thread_ptr).view().proc_linkedlist_node.is_init(),
        final(thread_map).spec_index(thread_ptr).is_init(),
        final(thread_map).spec_index(thread_ptr).inv(),
        !final(thread_map).spec_index(thread_ptr).being_killed(),
        !final(thread_map).spec_index(thread_ptr).view_ghost().exited,
        final(thread_map).spec_index(thread_ptr).locking_thread() is None,
        ret.0 == final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thread_ptr,
        ret.2 == final(thread_map).spec_index(thread_ptr).view().proc_linkedlist_node.addr(),
        ret.3.view().is_init(),
        ret.3.view().addr() == ret.2,
        ret.3.view().value().view() == thread_ptr,
{
    let tracked mut lctx = LocalContext::new_bootstrap(0, thread_ptr);
    let Tracked(lock_perm) = thread_map.retype_4k_and_insert(thread_ptr, thread_value, (), Ghost(ThreadGhost { chain_end: None, exited: false }), Tracked(page_perm), Tracked(&mut lctx), Ghost(KernelObjId::Thread(thread_ptr)));
    let ghost fresh_lock_id = thread_map.lock_id_by_key(thread_ptr);
    proof { lctx.enter_kernel_view_release(); assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&lctx), Tracked(&lock_perm));
    let (sched_node_addr, sched_node_perm, process_node_addr, process_node_perm) = thread.fresh_to_scheduled(thread_ptr, 0, initial_regs);
    proof { lctx.update_lock_id(KernelObjId::Thread(thread_ptr), fresh_lock_id, thread_map.lock_id_by_key(thread_ptr)); }
    thread_map.wunlock(thread_ptr, Tracked(&mut lctx), Tracked(lock_perm), Ghost(KernelObjId::Thread(thread_ptr)));
    (sched_node_addr, sched_node_perm, process_node_addr, process_node_perm)
}

impl KernelK {
    /// Remove a write-locked thread from `thr_mp` and reclaim its page memory together with the
    /// process node its process list returned.
    pub fn remove_thread_and_reclaim_4k_page_perm(
        &mut self, thread_ptr: RwLockThreadPtr, Tracked(proc_node_perm): Tracked<PointsTo<Node<RwLockThreadPtr>>>,
        Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).thr_mp.perms_wf(),
            old(self).thr_mp.dom().contains(thread_ptr),
            old(self).thr_mp.spec_index(thread_ptr).is_init(),
            old(self).thr_mp.spec_index(thread_ptr).view().scheduler_linkedlist_node.is_init(),
            old(self).thr_mp.spec_index(thread_ptr).view().endpoint_linkedlist_node.is_init(),
            proc_node_perm.is_init(),
            proc_node_perm.addr() == old(self).thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr(),
            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == old(lctx).thread_id(),
            lock_perm.lock_id() == old(self).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr)),
            *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
            final(self).thr_mp.perms_wf(),
            final(self).thr_mp.dom() =~= old(self).thr_mp.dom().remove(thread_ptr),
            forall|t: RwLockThreadPtr| #![trigger final(self).thr_mp.spec_index(t)]
                final(self).thr_mp.dom().contains(t) ==> final(self).thr_mp.spec_index(t) == old(self).thr_mp.spec_index(t),
            forall|t: RwLockThreadPtr| #![trigger final(self).thr_mp.lock_id_by_key(t)]
                final(self).thr_mp.dom().contains(t) ==> final(self).thr_mp.lock_id_by_key(t) == old(self).thr_mp.lock_id_by_key(t),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.view().is_init(),
            ret.view().addr() == thread_ptr,
    {
        proof { self.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
        let Tracked(thread_perm) = self.thr_mp.remove_with_perm(thread_ptr);
        let ret = retype_thread_rwlock_to_4k_page_perm(thread_ptr, Tracked(thread_perm), Tracked(proc_node_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof { assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
        ret
    }
}
}

use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use core::mem::MaybeUninit;
verus! {
impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> LockMinorTrait for PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>> {
    open spec fn lock_minor(&self) -> LockMinorId { seq![self.addr()] }
}

impl<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool> LockInvTrait for PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>> {
    open spec fn inv(&self) -> bool {
        &&& self.is_init()
        &&& self.value().view().inv()
    }
}
impl<T: LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool> LockMajorTrait for PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>> {
    open spec fn lock_major_1(&self) -> LockMajorId { self.value().view().lock_major_1() }
    open spec fn lock_major_2(&self) -> LockMajorId { self.value().view().lock_major_2() }
    open spec fn lock_major_3(&self) -> LockMajorId { self.value().view().lock_major_3() }
    open spec fn lock_major_default(&self) -> LockMajorId { self.value().view().lock_major_default() }
    open spec fn lock_major_1_predicate(&self) -> bool { self.value().view().lock_major_1_predicate() }
    open spec fn lock_major_2_predicate(&self) -> bool { self.value().view().lock_major_2_predicate() }
    open spec fn lock_major_3_predicate(&self) -> bool { self.value().view().lock_major_3_predicate() }
    open spec fn lock_major_default_predicate(&self) -> bool { self.value().view().lock_major_default_predicate() }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const KILL_STATE: bool> LockIdTrait for PointsTo<RwLock<T, ROT, GhostT, KILL_STATE>> {
    open spec fn lock_id(&self) -> LockId {
        LockId {
            container: self.value().container_depth(), process: self.value().process_depth(),
            major: if self.value().being_killed() { KILLED_LOCK_MAJOR } else { self.value().view().current_lock_major() }, minor: self.lock_minor(),
        }
    }
}

// TODO
#[verifier::external_body]
pub fn wlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(LockId { container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wlock_ensures(old(perm).value(), final(perm).value(), LockId {
            container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }, final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), LockId {
            container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }, obj_id.view()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().wlock_external(Tracked(lctx))
    }
}

// TODO
#[verifier::external_body]
pub fn wunlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(old(perm).lock_id(), obj_id.view()),
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        final(perm).value().locking_thread() is None,
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(perm).lock_id()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().wunlock_external(Tracked(lctx), lock_perm);
    }
}

#[verifier::external_body]
pub fn rlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(LockId { container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        rlock_ensures(old(perm).value(), final(perm).value(), LockId {
            container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }, final(lctx), ret.view()),
        rlock_lctx_ensures(old(lctx), final(lctx), LockId {
            container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }, obj_id.view()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().rlock_external(Tracked(lctx))
    }
}

#[verifier::external_body]
pub fn runlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().rlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is ReadLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        old(perm).value().read_lock_perm_match(&lock_perm.view()),
        old(lctx).lock_entry_contains(old(perm).lock_id(), obj_id.view()),
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        runlock_ensures(old(perm).value(), final(perm).value(), old(lctx).thread_id()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(perm).lock_id()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().runlock_external(Tracked(lctx), lock_perm);
    }
}

#[verifier::external_body]
pub fn downgrade<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>,
    Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(old(perm).lock_id(), obj_id.view()),
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        downgrade_ensures(old(perm).value(), final(perm).value(), final(lctx), lock_perm.view(), ret.view()),
        downgrade_lctx_ensures(old(lctx), final(lctx), old(perm).lock_id(), obj_id.view()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().downgrade_external(Tracked(lctx), lock_perm)
    }
}

#[verifier::external_body]
pub fn wlock_unless_killed<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Option<Tracked<LockPerm>>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        wlock_requires(old(perm).value(), old(lctx)),
        !old(perm).value().being_killed() ==> old(lctx).lock_id_acyclic(old(perm).lock_id()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret is None ==> {
            &&& old(perm).value().being_killed() == true
            &&& old(perm).value() == final(perm).value()
            &&& *final(lctx) == *old(lctx)
        },
        ret is Some ==> {
            &&& old(perm).value().being_killed() == false
            &&& wlock_ensures(old(perm).value(), final(perm).value(), LockId {
                container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }, final(lctx), ret.unwrap().view())
            &&& lock_ensures(old(lctx), final(lctx), LockId {
                container: old(perm).value().container_depth(), process: old(perm).value().process_depth(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() }, obj_id.view())
        },
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        let lock_id = Ghost(LockId { container: perm.value().container_depth(), process: perm.value().process_depth(), major: perm.value().view().current_lock_major(), minor: perm.lock_minor() });
        (*uptr).assume_init_mut().wlock_unless_killed(Tracked(lctx), lock_id, obj_id)
    }
}

/// Write-lock the unmarked object at `pptr` and mark it for its killer in one step; fails only if it is already marked.
#[verifier::external_body]
pub fn try_wlock_and_mark_kill<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>,
    obj_id: Ghost<KernelObjId>, killer_info: KillerInfo) -> (ret: (bool, Option<Tracked<LockPerm>>))
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        wlock_requires(old(perm).value(), old(lctx)),
        !old(perm).value().being_killed() ==> old(lctx).lock_id_acyclic(old(perm).lock_id()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        ret.0 == false ==> {
            &&& old(perm).value().being_killed() == true
            &&& old(perm).value() == final(perm).value()
            &&& ret.1 is None
            &&& *final(lctx) == *old(lctx)
        },
        ret.0 == true ==> {
            &&& old(perm).value().being_killed() == false
            &&& old(perm).value().locked() == false
            &&& final(perm).value().being_killed() == true
            &&& final(perm).value().killer_info_inner() == Some(killer_info)
            &&& ret.1 is Some
            &&& final(perm).value().locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.unwrap().view().lock_id() }
            &&& final(perm).value().inv()
            &&& final(perm).value().view() == old(perm).value().view()
            &&& final(perm).value().view_rodata() == old(perm).value().view_rodata()
            &&& final(perm).value().view_ghost() == old(perm).value().view_ghost()
            &&& ret.1.unwrap().view().state() is WriteLock
            &&& ret.1.unwrap().view().thread_id() == final(lctx).thread_id()
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: old(perm).lock_id(), mode: TypedLockMode::Write })
        },
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        let lock_id = Ghost(LockId { container: perm.value().container_depth(), process: perm.value().process_depth(), major: perm.value().view().current_lock_major(), minor: perm.lock_minor() });
        (*uptr).assume_init_mut().try_wlock_and_mark_kill(Tracked(lctx), lock_id, obj_id, killer_info)
    }
}

/// Mark the object at `pptr`, which this thread write-holds, for its killer; the write lock stays.
#[verifier::external_body]
pub fn mark_kill<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>,
    Tracked(lctx): Tracked<&LocalContext>, killer_info: KillerInfo)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        old(perm).value().wlocked_by(lctx),
        !old(perm).value().being_killed(),
        lctx.kernel_view_locking_state() is Release,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().being_killed(),
        final(perm).value().killer_info_inner() == Some(killer_info),
        final(perm).value().locking_thread() == old(perm).value().locking_thread(),
        final(perm).value().is_init() == old(perm).value().is_init(),
        final(perm).value().view() == old(perm).value().view(),
        final(perm).value().view_rodata() == old(perm).value().view_rodata(),
        final(perm).value().view_ghost() == old(perm).value().view_ghost(),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().mark_kill(Tracked(lctx), killer_info);
    }
}

/// Dynamic write acquisition of the object at `pptr` for the concrete owner `requested` under the candidate `lock_id`.
#[verifier::external_body]
pub fn dynamic_wlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>,
    requested: LockOwnerId) -> (ret: DynamicWLockResult)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().view_rodata().process_source() is Dynamic,
        wlock_requires(old(perm).value(), old(lctx)),
        !old(perm).value().being_killed() ==> {
            &&& lock_id.view() == (LockId { container: old(perm).value().container_depth(), process: requested, major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() })
            &&& old(lctx).lock_id_acyclic(lock_id.view())
        },
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        dynamic_wlock_ensures(old(perm).value(), final(perm).value(), old(lctx), final(lctx), lock_id.view(), obj_id.view(), requested, ret),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().dynamic_wlock(Tracked(lctx), lock_id, obj_id, requested)
    }
}

/// Release this thread's live dynamic write acquisition of the object at `pptr`, registered under `lock_id`.
#[verifier::external_body]
pub fn dynamic_wunlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, lock_id: Ghost<LockId>,
    obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().view_rodata().process_source() is Dynamic,
        !old(perm).value().being_killed(),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(lock_id.view(), obj_id.view()),
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        dynamic_wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), lock_id.view()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().dynamic_wunlock(Tracked(lctx), lock_perm, lock_id, obj_id);
    }
}

/// `try_wlock_and_mark_kill` of a dynamic object under the candidate `lock_id` of the killer owner `High`.
#[verifier::external_body]
pub fn try_wlock_dynamic_and_mark_kill<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(
    pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>,
    Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>, requested: Ghost<LockOwnerId>, killer_info: KillerInfo)
    -> (ret: (bool, Option<Tracked<LockPerm>>))
    requires
        requested.view() == LockOwnerId::High,
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().view_rodata().process_source() is Dynamic,
        wlock_requires(old(perm).value(), old(lctx)),
        !old(perm).value().being_killed() ==> {
            &&& lock_id.view() == (LockId { container: old(perm).value().container_depth(), process: requested.view(), major: old(perm).value().view().current_lock_major(), minor: old(perm).lock_minor() })
            &&& old(lctx).lock_id_acyclic(lock_id.view())
        },
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        ret.0 == false ==> {
            &&& old(perm).value().being_killed() == true
            &&& old(perm).value() == final(perm).value()
            &&& ret.1 is None
            &&& *final(lctx) == *old(lctx)
        },
        ret.0 == true ==> {
            &&& old(perm).value().being_killed() == false
            &&& old(perm).value().locked() == false
            &&& final(perm).value().being_killed() == true
            &&& final(perm).value().killer_info_inner() == Some(killer_info)
            &&& ret.1 is Some
            &&& final(perm).value().locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.unwrap().view().lock_id() }
            &&& final(perm).value().inv()
            &&& final(perm).value().view() == old(perm).value().view()
            &&& final(perm).value().view_rodata() == old(perm).value().view_rodata()
            &&& final(perm).value().view_ghost() == old(perm).value().view_ghost()
            &&& ret.1.unwrap().view().state() is WriteLock
            &&& ret.1.unwrap().view().thread_id() == final(lctx).thread_id()
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: lock_id.view(), mode: TypedLockMode::Write })
        },
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().try_wlock_dynamic_and_mark_kill(Tracked(lctx), lock_id, obj_id, requested, killer_info)
    }
}

#[verifier::external_body]
pub fn has_kill_state_wunlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(old(perm).lock_id(), obj_id.view()),
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        final(perm).value().locking_thread() is None,
        old(perm).value().being_killed() == final(perm).value().being_killed(),
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), old(perm).lock_id()),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().wunlock(Tracked(lctx), lock_perm, Ghost(perm.lock_id()), obj_id);
    }
}

#[verifier::external_body]
pub fn take<T, ROT, GhostT, const HAS_KILL_STATE: bool>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret: T)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == lctx.thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        take_ensures(old(perm).value(), final(perm).value()),
        final(perm).value().wlocked_by(lctx),
        ret == old(perm).value().view()
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().take(Tracked(lctx),lock_perm)
    }
}

#[verifier::external_body]
pub fn put<T, ROT, GhostT, const HAS_KILL_STATE: bool>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>, v: T)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init() == false,
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == lctx.thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),
        put_ensures(old(perm).value(), final(perm).value(), v),
        final(perm).value().wlocked_by(lctx),
{
    unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().put(Tracked(lctx), lock_perm,v)
    }
}
#[verifier::external_body]
pub fn borrow<'a, T, ROT, GhostT, const HAS_KILL_STATE: bool>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<& PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, lock_perm: Tracked<&'a LockPerm>) -> (ret: &'a T)
    requires
        pptr.addr() == perm.addr(),
        perm.is_init(),
        perm.value().is_init(),
        lock_perm.view().state() is WriteLock ==> perm.value().write_lock_perm_match(lock_perm.view()),
        lock_perm.view().state() is ReadLock ==> perm.value().read_lock_perm_match(lock_perm.view()),
    ensures
        ret == perm.value().view(),
{
    unsafe {
        let uptr = &*(pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>);
        uptr.borrow(lock_perm)
    }
}

#[verifier::external_body]
pub fn borrow_rodata<'a, T, ROT, GhostT, const HAS_KILL_STATE: bool>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&'a PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>) -> (ret: &'a ROT)
    requires
        pptr.addr() == perm.addr(),
        perm.is_init(),
    ensures
        ret == perm.value().view_rodata(),
{
    unsafe {
        let uptr = &*(pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>);
        uptr.borrow_rodata()
    }
}

/// Mutably borrow the `T` inside the rwlock through a `&mut PointsTo<RwLock<...>>`.
/// Caller holds a write `LockPerm`. The `&mut T` linkage is wired so that, when
/// the borrow ends, the rwlock's view reflects the borrow's final state.
#[verifier::external_body]
pub fn borrow_mut<'a, T, ROT, GhostT, const HAS_KILL_STATE: bool>(
    pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&'a mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&'a LockPerm>,
) -> (ret: &'a mut T)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == lctx.thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().is_init(),
        final(perm).value().wlocked_by(lctx),
        // The rwlock's structural state is unchanged.
        final(perm).value().view_rodata() == old(perm).value().view_rodata(),
        final(perm).value().view_ghost() == old(perm).value().view_ghost(),
        final(perm).value().locking_thread() == old(perm).value().locking_thread(),
        final(perm).value().control() == old(perm).value().control(),
        // The `&mut T` linkage.
        *ret == old(perm).value().view(),
        final(perm).value().view() == *final(ret),
{
    unsafe {
        let uptr = &mut *(pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>);
        uptr.borrow_mut(Tracked(lctx), lock_perm)
    }
}

/// TCB: replace the single ghost field of the `RwLock` inside a `PointsTo`,
/// lock-free. Reaching the heap-stored `RwLock` through the opaque `PointsTo`
/// is irreducibly trusted; `LockedMap::update_ghost` is the verified wrapper.
#[verifier::external_body]
pub proof fn update_ghost<T, ROT, GhostT, const HAS_KILL_STATE: bool>(tracked perm: &mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, new_ghost: GhostT)
    requires
        old(perm).is_init(),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        update_ghost_ensures(old(perm).value(), final(perm).value(), new_ghost),
{
    unimplemented!()
}
}

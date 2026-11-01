use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use crate::cpu::Cpu;
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.wlock(); }
    Tracked::assume_new()
}

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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.wunlock(); }
}

#[verifier::external_body]
pub fn rlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.rlock(); }
    Tracked::assume_new()
}

#[verifier::external_body]
pub fn runlock<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.runlock(); }
}

#[verifier::external_body]
pub fn downgrade<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>,
    Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
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
        downgrade_ensures(old(perm).value(), final(perm).value(), final(lctx), lock_perm.view(), ret.view()),
        downgrade_lctx_ensures(old(lctx), final(lctx), old(perm).lock_id(), obj_id.view()),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.downgrade(); }
    Tracked::assume_new()
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    if unsafe { (*p).lock.wlock_unless_killed() }.is_err() { None } else { Some(Tracked::assume_new()) }
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
            &&& final(perm).value().killer_info_from_control() == Some(killer_info)
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    if unsafe { (*p).lock.try_wlock_and_mark_kill(killer_info) }.is_err() { (false, None) } else { (true, Some(Tracked::assume_new())) }
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
        final(perm).value().killer_info_from_control() == Some(killer_info),
        final(perm).value().locking_thread() == old(perm).value().locking_thread(),
        final(perm).value().is_init() == old(perm).value().is_init(),
        final(perm).value().view() == old(perm).value().view(),
        final(perm).value().view_rodata() == old(perm).value().view_rodata(),
        final(perm).value().view_ghost() == old(perm).value().view_ghost(),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { (*p).lock.mark_kill(killer_info); }
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    match unsafe { (*p).lock.dynamic_wlock(requested) } {
        Ok(()) => DynamicWLockResult::Acquired(Tracked::assume_new()),
        Err(LockControl::Killed(killer_info)) => DynamicWLockResult::Killed(killer_info),
        Err(LockControl::DynamicProcess(observed_owner)) => DynamicWLockResult::DepthConflict { observed_owner },
        Err(LockControl::Clear) => unreachable!(),
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { (*p).lock.dynamic_wunlock(); }
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
            &&& final(perm).value().killer_info_from_control() == Some(killer_info)
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    if unsafe { (*p).lock.try_wlock_and_mark_kill(killer_info) }.is_err() { (false, None) } else { (true, Some(Tracked::assume_new())) }
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { (*p).lock.wunlock(); }
}

/// `RwLockInner::wlock_unless_killed` of lock array cell `index` at `pptr`, under the ordering id derived from the cell: the
/// object's owners, the major of its current state, and the cell index as minor; a marked object returns `None` with its
/// token unchanged.
#[verifier::external_body]
pub fn wlock_unless_killed_array_cell<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(index): Ghost<usize>, obj_id: Ghost<KernelObjId>)
    -> (ret: Option<Tracked<LockPerm>>)
    where RwLock<T, ROT, GhostT, HAS_KILL_STATE>: TokenCellBase
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>(RwLock::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base_spec(), index as int),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        wlock_requires(old(perm).value(), old(lctx)),
        !old(perm).value().being_killed() ==> old(lctx).lock_id_acyclic(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        ret is None ==> {
            &&& old(perm).value().being_killed() == true
            &&& *final(perm) == *old(perm)
            &&& *final(lctx) == *old(lctx)
        },
        ret is Some ==> {
            &&& old(perm).value().being_killed() == false
            &&& wlock_ensures(old(perm).value(), final(perm).value(), LockId {
                container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
                final(lctx), ret.unwrap().view())
            &&& lock_ensures(old(lctx), final(lctx), LockId {
                container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
                obj_id.view())
        },
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    if unsafe { (*p).lock.wlock_unless_killed() }.is_err() { None } else { Some(Tracked::assume_new()) }
}

/// `wlock_unless_killed_array_cell` that also clears the calling cpu's interrupt flag when it takes the lock.
#[verifier::external_body]
pub fn wlock_unless_killed_cli_array_cell<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(index): Ghost<usize>, obj_id: Ghost<KernelObjId>)
    -> (ret: Option<Tracked<LockPerm>>)
    where RwLock<T, ROT, GhostT, HAS_KILL_STATE>: TokenCellBase
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>(RwLock::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base_spec(), index as int),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        wlock_requires(old(perm).value(), old(lctx)),
        !old(perm).value().being_killed() ==> old(lctx).lock_id_acyclic(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        ret is None ==> {
            &&& old(perm).value().being_killed() == true
            &&& *final(perm) == *old(perm)
            &&& *final(lctx) == *old(lctx)
        },
        ret is Some ==> {
            &&& old(perm).value().being_killed() == false
            &&& wlock_ensures(old(perm).value(), final(perm).value(), LockId {
                container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
                final(lctx), ret.unwrap().view())
            &&& lock_ensures(old(lctx), final(lctx), LockId {
                container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
                obj_id.view())
        },
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    if unsafe { (*p).lock.wlock_unless_killed_cli() }.is_err() { None } else { Some(Tracked::assume_new()) }
}

/// `RwLockInner::wunlock` of lock array cell `index` at `pptr`, registered under the ordering id derived from the cell.
#[verifier::external_body]
pub fn has_kill_state_wunlock_array_cell<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, Ghost(index): Ghost<usize>,
    obj_id: Ghost<KernelObjId>)
    where RwLock<T, ROT, GhostT, HAS_KILL_STATE>: TokenCellBase
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>(RwLock::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base_spec(), index as int),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
            obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        old(perm).value().being_killed() == final(perm).value().being_killed(),
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] }),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { (*p).lock.wunlock(); }
}

/// `has_kill_state_wunlock_array_cell` that also sets the calling cpu's interrupt flag after the release.
#[verifier::external_body]
pub fn wunlock_sti_array_cell<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, Ghost(index): Ghost<usize>,
    obj_id: Ghost<KernelObjId>)
    where RwLock<T, ROT, GhostT, HAS_KILL_STATE>: TokenCellBase
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>(RwLock::<T, ROT, GhostT, HAS_KILL_STATE>::cell_base_spec(), index as int),
        old(perm).is_init(),
        !(old(perm).value().view_rodata().container_source() is Dynamic),
        !(old(perm).value().view_rodata().process_source() is Dynamic),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
            obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        old(perm).value().being_killed() == final(perm).value().being_killed(),
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] }),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { (*p).lock.wunlock_sti(); }
}

/// `RwLockInner::wlock` of lock array cell `index` at `pptr`, under the ordering id derived from the cell: the object's
/// owners, the major of its current state, and the cell index as minor.
#[verifier::external_body]
pub fn wlock_array_cell<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(index): Ghost<usize>, obj_id: Ghost<KernelObjId>)
    -> (ret: Tracked<LockPerm>)
    where RwLock<T, ROT, GhostT, NO_KILL_STATE>: TokenCellBase
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>(RwLock::<T, ROT, GhostT, NO_KILL_STATE>::cell_base_spec(), index as int),
        old(perm).is_init(),
        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wlock_ensures(old(perm).value(), final(perm).value(), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
            final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
            obj_id.view()),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.wlock(); }
    Tracked::assume_new()
}

/// `RwLockInner::wunlock` of lock array cell `index` at `pptr`, registered under the ordering id derived from the cell.
#[verifier::external_body]
pub fn wunlock_array_cell<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, Ghost(index): Ghost<usize>,
    obj_id: Ghost<KernelObjId>)
    where RwLock<T, ROT, GhostT, NO_KILL_STATE>: TokenCellBase
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).addr() == lock_cell_addr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>(RwLock::<T, ROT, GhostT, NO_KILL_STATE>::cell_base_spec(), index as int),
        old(perm).is_init(),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] },
            obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(), minor: seq![index] }),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.wunlock(); }
}

/// `RwLockInner::wlock` of the object at `pptr`, under the ordering id derived from the object: its owners, the major of its
/// current state, and its own minor.
#[verifier::external_body]
pub fn wlock_object_minor<T: LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait, ROT, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(),
            minor: old(perm).value().view().lock_minor() }),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wlock_ensures(old(perm).value(), final(perm).value(), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(),
            minor: old(perm).value().view().lock_minor() }, final(lctx), ret.view()),
        lock_ensures(old(lctx), final(lctx), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(),
            minor: old(perm).value().view().lock_minor() }, obj_id.view()),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.wlock(); }
    Tracked::assume_new()
}

/// `RwLockInner::wunlock` of the object at `pptr`, registered under the ordering id derived from the object.
#[verifier::external_body]
pub fn wunlock_object_minor<T: LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait, ROT, GhostT>(pptr: &PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>,
    Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),
        lock_perm.view().state() is WriteLock,
        lock_perm.view().thread_id() == old(lctx).thread_id(),
        lock_perm.view().lock_id() == old(perm).value().locking_thread()->Write_lock_id,
        old(lctx).lock_entry_contains(LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(),
            minor: old(perm).value().view().lock_minor() }, obj_id.view()),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
            container: old(perm).value().view().container_depth(), process: old(perm).value().view().process_depth(), major: old(perm).value().view().current_lock_major(),
            minor: old(perm).value().view().lock_minor() }),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, NO_KILL_STATE>;
    unsafe { (*p).lock.wunlock(); }
}

/// TCB: clear the mark of the cpu lock at `pptr` while its killer still write-holds it. Only a cpu lock can be
/// unmarked; every other object keeps its mark until it is destroyed.
#[verifier::external_body]
pub fn unkill(pptr: &PPtr<RwLock<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<Cpu, (), Option<CpuId>, HAS_KILL_STATE>>>,
    Tracked(lctx): Tracked<&LocalContext>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        old(perm).value().wlocked_by(lctx),
        old(perm).value().being_killed(),
        lctx.kernel_view_locking_state() is Release,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        !final(perm).value().being_killed(),
        final(perm).value().locking_thread() == old(perm).value().locking_thread(),
        final(perm).value().is_init() == old(perm).value().is_init(),
        final(perm).value().view() == old(perm).value().view(),
        final(perm).value().view_rodata() == old(perm).value().view_rodata(),
        final(perm).value().view_ghost() == old(perm).value().view_ghost(),
{
    let p = pptr.addr() as *mut RwLock<Cpu, (), Option<CpuId>, HAS_KILL_STATE>;
    unsafe { (*p).lock.unkill(); }
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { core::ptr::read(core::ptr::addr_of!((*p).value)) }
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { core::ptr::write(core::ptr::addr_of_mut!((*p).value), v) }
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { &(*p).value }
}

#[verifier::external_body]
pub fn borrow_rodata<'a, T, ROT, GhostT, const HAS_KILL_STATE: bool>(pptr: &PPtr<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&'a PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>) -> (ret: &'a ROT)
    requires
        pptr.addr() == perm.addr(),
        perm.is_init(),
    ensures
        ret == perm.value().view_rodata(),
{
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { &(*p).read_only_value }
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
    let p = pptr.addr() as *mut RwLock<T, ROT, GhostT, HAS_KILL_STATE>;
    unsafe { &mut (*p).value }
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

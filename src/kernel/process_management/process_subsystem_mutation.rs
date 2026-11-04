use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;
use vstd::assert_seqs_equal;
use crate::*;
use super::process_subsystem_mutation_eof::*;

verus! {
pub fn thread_map_consume_staged_4k(thrd_mp: &mut ThreadLockedMap, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
    requires
        thread_perms_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(thrd_ptr),
        old(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thrd_mp).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(thrd_mp).spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
        old(thrd_mp).spec_index(thrd_ptr).view().quota_4k >= 1,
    ensures
        thread_perms_wf(*final(thrd_mp)),
        final(thrd_mp).perms_wf(),
        final(thrd_mp).spec_index(thrd_ptr).inv(),
        final(thrd_mp).spec_index(thrd_ptr).wlocked_by(lctx),
        final(thrd_mp).unchanged_except(old(thrd_mp), thrd_ptr),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        forall|ptr: RwLockThreadPtr| #![trigger final(thrd_mp).spec_index(ptr)] old(thrd_mp).dom().contains(ptr) && ptr != thrd_ptr ==> final(thrd_mp).spec_index(ptr) == old(thrd_mp).spec_index(ptr),
        forall|ptr: RwLockThreadPtr|
            #![trigger final(thrd_mp).view().spec_index(ptr).is_init()]
            old(thrd_mp).dom().contains(ptr) ==> {
                &&& final(thrd_mp).view().spec_index(ptr).is_init() == old(thrd_mp).view().spec_index(ptr).is_init()
                &&& final(thrd_mp).view().spec_index(ptr).addr() == old(thrd_mp).view().spec_index(ptr).addr()
            },
        final(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thrd_mp).spec_index(thrd_ptr).view() == (Thread { quota_4k: final(thrd_mp).spec_index(thrd_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(thrd_mp).spec_index(thrd_ptr).view().temp_alloc_cache_4k, ..old(thrd_mp).spec_index(thrd_ptr).view() }),
        final(thrd_mp).spec_index(thrd_ptr).view().temp_alloc_cache_4k.view() == old(thrd_mp).spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().remove(pg_ptr),
        final(thrd_mp).spec_index(thrd_ptr).view().quota_4k == old(thrd_mp).spec_index(thrd_ptr).view().quota_4k - 1,
        final(thrd_mp).lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr),
        final(thrd_mp).spec_index(thrd_ptr).locking_thread() == old(thrd_mp).spec_index(thrd_ptr).locking_thread(),
        final(thrd_mp).spec_index(thrd_ptr).being_killed() == old(thrd_mp).spec_index(thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(thrd_ptr).killer_info() == old(thrd_mp).spec_index(thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(thrd_ptr).view_ghost() == old(thrd_mp).spec_index(thrd_ptr).view_ghost(),
{
    assert(thrd_mp.perms_wf() && thrd_mp.spec_index(thrd_ptr).is_init()
        && thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_map(*thrd_mp); thread_perms_wf_at(*thrd_mp, thrd_ptr); };
    let thread = thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.consume_staged_4k(pg_ptr);
    proof {
        thread_map_consume_staged_4k_eof_thread_perms_wf(*old(thrd_mp), *thrd_mp, thrd_ptr);
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thrd_mp.lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_add_free_quota_pending_4k(thrd_mp: &mut ThreadLockedMap, thrd_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
    requires
        thread_perms_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(thrd_ptr),
        old(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thrd_mp).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        depth <= old(thrd_mp).spec_index(thrd_ptr).view().container_depth,
        *old(counter) == old(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_4k_at_depth(depth),
        *old(counter) < usize::MAX,
    ensures
        thread_perms_wf(*final(thrd_mp)),
        final(thrd_mp).perms_wf(),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        final(thrd_mp).unchanged_except(old(thrd_mp), thrd_ptr),
        final(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thrd_mp).lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr),
        final(thrd_mp).spec_index(thrd_ptr).is_init(),
        final(thrd_mp).spec_index(thrd_ptr).inv(),
        final(thrd_mp).spec_index(thrd_ptr).wlocked_by(lctx),
        final(thrd_mp).spec_index(thrd_ptr).locking_thread() == old(thrd_mp).spec_index(thrd_ptr).locking_thread(),
        final(thrd_mp).spec_index(thrd_ptr).being_killed() == old(thrd_mp).spec_index(thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(thrd_ptr).killer_info() == old(thrd_mp).spec_index(thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(thrd_ptr).view_rodata() == old(thrd_mp).spec_index(thrd_ptr).view_rodata(),
        final(thrd_mp).spec_index(thrd_ptr).view_ghost() == old(thrd_mp).spec_index(thrd_ptr).view_ghost(),
        final(thrd_mp).spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(thrd_mp).spec_index(thrd_ptr).view() }),
        *final(counter) == *old(counter) + 1,
        final(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_4k_at_depth(depth) == *final(counter),
        final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view() == old(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view() + if depth == old(thrd_mp).spec_index(thrd_ptr).view().container_depth { 1int } else { 0int },
        final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(thrd_mp).spec_index(thrd_ptr).view().container_depth { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, *final(counter)) }
            else { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view() },
{
    assert(thrd_mp.perms_wf() && thrd_mp.spec_index(thrd_ptr).is_init() && thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_map(*thrd_mp); thread_perms_wf_at(*thrd_mp, thrd_ptr); };
    let thread = thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.add_free_quota_pending_4k(depth, counter);
    proof {
        thread_map_add_free_quota_pending_4k_eof_thread_perms_wf(*old(thrd_mp), *thrd_mp, thrd_ptr);
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thrd_mp.lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_clear_free_quota_pending_4k(thrd_mp: &mut ThreadLockedMap, thrd_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
    requires
        thread_perms_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(thrd_ptr),
        old(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thrd_mp).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        depth <= old(thrd_mp).spec_index(thrd_ptr).view().container_depth,
        *old(counter) == old(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_4k_at_depth(depth),
    ensures
        thread_perms_wf(*final(thrd_mp)),
        final(thrd_mp).perms_wf(),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        final(thrd_mp).unchanged_except(old(thrd_mp), thrd_ptr),
        final(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thrd_mp).lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr),
        final(thrd_mp).spec_index(thrd_ptr).is_init(),
        final(thrd_mp).spec_index(thrd_ptr).inv(),
        final(thrd_mp).spec_index(thrd_ptr).wlocked_by(lctx),
        final(thrd_mp).spec_index(thrd_ptr).locking_thread() == old(thrd_mp).spec_index(thrd_ptr).locking_thread(),
        final(thrd_mp).spec_index(thrd_ptr).being_killed() == old(thrd_mp).spec_index(thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(thrd_ptr).killer_info() == old(thrd_mp).spec_index(thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(thrd_ptr).view_rodata() == old(thrd_mp).spec_index(thrd_ptr).view_rodata(),
        final(thrd_mp).spec_index(thrd_ptr).view_ghost() == old(thrd_mp).spec_index(thrd_ptr).view_ghost(),
        final(thrd_mp).spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(thrd_mp).spec_index(thrd_ptr).view() }),
        *final(counter) == 0,
        final(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_4k_at_depth(depth) == 0,
        final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view() == if depth == old(thrd_mp).spec_index(thrd_ptr).view().container_depth { 0usize } else { old(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view() },
        final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(thrd_mp).spec_index(thrd_ptr).view().container_depth { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, 0usize) }
            else { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view() },
{
    assert(thrd_mp.perms_wf() && thrd_mp.spec_index(thrd_ptr).is_init() && thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_map(*thrd_mp); thread_perms_wf_at(*thrd_mp, thrd_ptr); };
    let thread = thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.clear_free_quota_pending_4k(depth, counter);
    proof {
        thread_map_clear_free_quota_pending_4k_eof_thread_perms_wf(*old(thrd_mp), *thrd_mp, thrd_ptr);
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thrd_mp.lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_add_free_quota_pending_2m(thrd_mp: &mut ThreadLockedMap, thrd_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
    requires
        thread_perms_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(thrd_ptr),
        old(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thrd_mp).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        depth <= old(thrd_mp).spec_index(thrd_ptr).view().container_depth,
        *old(counter) == old(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
        *old(counter) < usize::MAX,
    ensures
        thread_perms_wf(*final(thrd_mp)),
        final(thrd_mp).perms_wf(),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        final(thrd_mp).unchanged_except(old(thrd_mp), thrd_ptr),
        final(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thrd_mp).lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr),
        final(thrd_mp).spec_index(thrd_ptr).is_init(),
        final(thrd_mp).spec_index(thrd_ptr).inv(),
        final(thrd_mp).spec_index(thrd_ptr).wlocked_by(lctx),
        final(thrd_mp).spec_index(thrd_ptr).locking_thread() == old(thrd_mp).spec_index(thrd_ptr).locking_thread(),
        final(thrd_mp).spec_index(thrd_ptr).being_killed() == old(thrd_mp).spec_index(thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(thrd_ptr).killer_info() == old(thrd_mp).spec_index(thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(thrd_ptr).view_rodata() == old(thrd_mp).spec_index(thrd_ptr).view_rodata(),
        final(thrd_mp).spec_index(thrd_ptr).view_ghost() == old(thrd_mp).spec_index(thrd_ptr).view_ghost(),
        final(thrd_mp).spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..old(thrd_mp).spec_index(thrd_ptr).view() }),
        *final(counter) == *old(counter) + 1,
        final(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth) == *final(counter),
        final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() == old(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() + if depth == old(thrd_mp).spec_index(thrd_ptr).view().container_depth { 1int } else { 0int },
        final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view()
            == if depth < old(thrd_mp).spec_index(thrd_ptr).view().container_depth { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().update(depth as int, *final(counter)) }
            else { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view() },
{
    assert(thrd_mp.perms_wf() && thrd_mp.spec_index(thrd_ptr).is_init() && thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_map(*thrd_mp); thread_perms_wf_at(*thrd_mp, thrd_ptr); };
    let thread = thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.add_free_quota_pending_2m(depth, counter);
    proof {
        thread_map_add_free_quota_pending_2m_eof_thread_perms_wf(*old(thrd_mp), *thrd_mp, thrd_ptr);
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thrd_mp.lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_clear_free_quota_pending_2m(thrd_mp: &mut ThreadLockedMap, thrd_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
    requires
        thread_perms_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(thrd_ptr),
        old(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thrd_mp).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        depth <= old(thrd_mp).spec_index(thrd_ptr).view().container_depth,
        *old(counter) == old(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
    ensures
        thread_perms_wf(*final(thrd_mp)),
        final(thrd_mp).perms_wf(),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        final(thrd_mp).unchanged_except(old(thrd_mp), thrd_ptr),
        final(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thrd_mp).lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr),
        final(thrd_mp).spec_index(thrd_ptr).is_init(),
        final(thrd_mp).spec_index(thrd_ptr).inv(),
        final(thrd_mp).spec_index(thrd_ptr).wlocked_by(lctx),
        final(thrd_mp).spec_index(thrd_ptr).locking_thread() == old(thrd_mp).spec_index(thrd_ptr).locking_thread(),
        final(thrd_mp).spec_index(thrd_ptr).being_killed() == old(thrd_mp).spec_index(thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(thrd_ptr).killer_info() == old(thrd_mp).spec_index(thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(thrd_ptr).view_rodata() == old(thrd_mp).spec_index(thrd_ptr).view_rodata(),
        final(thrd_mp).spec_index(thrd_ptr).view_ghost() == old(thrd_mp).spec_index(thrd_ptr).view_ghost(),
        final(thrd_mp).spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..old(thrd_mp).spec_index(thrd_ptr).view() }),
        *final(counter) == 0,
        final(thrd_mp).spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth) == 0,
        final(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() == if depth == old(thrd_mp).spec_index(thrd_ptr).view().container_depth { 0usize } else { old(thrd_mp).spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() },
        final(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view()
            == if depth < old(thrd_mp).spec_index(thrd_ptr).view().container_depth { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().update(depth as int, 0usize) }
            else { old(thrd_mp).spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view() },
{
    assert(thrd_mp.perms_wf() && thrd_mp.spec_index(thrd_ptr).is_init() && thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_map(*thrd_mp); thread_perms_wf_at(*thrd_mp, thrd_ptr); };
    let thread = thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.clear_free_quota_pending_2m(depth, counter);
    proof {
        thread_map_clear_free_quota_pending_2m_eof_thread_perms_wf(*old(thrd_mp), *thrd_mp, thrd_ptr);
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thrd_mp.lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn process_map_add_owned_thread(prc_mp: &mut ProcessLockedMap, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(process_lock_perm): Tracked<&LockPerm>)
    requires
        process_perms_wf(*old(prc_mp)),
        old(prc_mp).dom().contains(prc_ptr),
        old(prc_mp).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == lctx.thread_id(),
        process_lock_perm.lock_id() == old(prc_mp).spec_index(prc_ptr).locking_thread()->Write_lock_id,
        old(prc_mp).spec_index(prc_ptr).view().state.view() is Creating || old(prc_mp).spec_index(prc_ptr).view().state.view() is Running,
        node_perm.is_init(),
        node_perm.addr() == node_addr,
        !old(prc_mp).spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr),
        old(prc_mp).spec_index(prc_ptr).view().owned_threads.view().len() < usize::MAX,
    ensures
        process_perms_wf(*final(prc_mp)),
        final(prc_mp).unchanged_except(old(prc_mp), prc_ptr),
        final(prc_mp).dom() == old(prc_mp).dom(),
        forall|ptr: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(ptr)] old(prc_mp).dom().contains(ptr) && ptr != prc_ptr ==> final(prc_mp).spec_index(ptr) == old(prc_mp).spec_index(ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).spec_index(ptr)]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& final(prc_mp).spec_index(ptr).view().children == old(prc_mp).spec_index(ptr).view().children
                &&& final(prc_mp).spec_index(ptr).view_ghost().uppertree_seq == old(prc_mp).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(prc_mp).spec_index(ptr).view_ghost().subtree_set == old(prc_mp).spec_index(ptr).view_ghost().subtree_set
                &&& final(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions == old(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(prc_mp).spec_index(ptr).view_rodata() == old(prc_mp).spec_index(ptr).view_rodata()
            },
        final(prc_mp).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(prc_mp).spec_index(prc_ptr).view() == (Process { owned_threads: final(prc_mp).spec_index(prc_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..old(prc_mp).spec_index(prc_ptr).view() }),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.view() == old(prc_mp).spec_index(prc_ptr).view().owned_threads.view().push(thrd_ptr),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.dom() == old(prc_mp).spec_index(prc_ptr).view().owned_threads.dom().insert(node_addr),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.map() == old(prc_mp).spec_index(prc_ptr).view().owned_threads.map().insert(node_addr, thrd_ptr),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.length == old(prc_mp).spec_index(prc_ptr).view().owned_threads.length + 1,
        !old(prc_mp).spec_index(prc_ptr).view().owned_threads.dom().contains(node_addr),
        !old(prc_mp).spec_index(prc_ptr).view().owned_threads.map().dom().contains(node_addr),
        final(prc_mp).spec_index(prc_ptr).view().zombie == old(prc_mp).spec_index(prc_ptr).view().zombie,
        final(prc_mp).spec_index(prc_ptr).view().pagetable == old(prc_mp).spec_index(prc_ptr).view().pagetable,
        final(prc_mp).spec_index(prc_ptr).view().pcid == old(prc_mp).spec_index(prc_ptr).view().pcid,
        final(prc_mp).spec_index(prc_ptr).view_rodata() == old(prc_mp).spec_index(prc_ptr).view_rodata(),
        final(prc_mp).lock_id_by_key(prc_ptr) == old(prc_mp).lock_id_by_key(prc_ptr),
        final(prc_mp).spec_index(prc_ptr).locking_thread() == old(prc_mp).spec_index(prc_ptr).locking_thread(),
        final(prc_mp).spec_index(prc_ptr).being_killed() == old(prc_mp).spec_index(prc_ptr).being_killed(),
{
    assert(prc_mp.perms_wf() && prc_mp.spec_index(prc_ptr).is_init()
        && prc_mp.spec_index(prc_ptr).inv()) by { process_perms_wf_map(*prc_mp); process_perms_wf_at(*prc_mp, prc_ptr); };
    let process = prc_mp.borrow_mut_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(process_lock_perm));
    process.add_owned_thread(thrd_ptr, node_addr, node_perm);
    proof {
        process_map_add_owned_thread_eof_process_perms_wf(*old(prc_mp), *prc_mp, prc_ptr);
        assert(prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn scheduler_map_enqueue_scheduled_thread(
    sched_mp: &mut SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr,
    node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(shard_lock_perm): Tracked<&LockPerm>,
)
    requires
        scheduler_perms_wf(*old(sched_mp)),
        old(sched_mp).dom().contains(sched_ptr),
        index_valid(NUM_CPUS, cpu_id),
        old(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        shard_lock_perm.state() is WriteLock,
        shard_lock_perm.thread_id() == lctx.thread_id(),
        shard_lock_perm.lock_id() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == thrd_ptr,
        !old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view().contains(thrd_ptr),
        old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.length != usize::MAX,
    ensures
        scheduler_perms_wf(*final(sched_mp)),
        final(sched_mp).perms_wf(),
        final(sched_mp).spec_index(sched_ptr).inv(),
        final(sched_mp).unchanged_except(old(sched_mp), sched_ptr),
        final(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(sched_mp).spec_index(sched_ptr).owning_container == old(sched_mp).spec_index(sched_ptr).owning_container,
        final(sched_mp).spec_index(sched_ptr).shards.entries_unchanged_except(&old(sched_mp).spec_index(sched_ptr).shards, cpu_id),
        final(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread(),
        final(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().being_killed() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().being_killed(),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view().push(thrd_ptr),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().insert(node_addr, thrd_ptr),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom().insert(node_addr),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.length == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.length + 1,
        !old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom().contains(node_addr),
        !old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().dom().contains(node_addr),
        scheduler_shards_of(final(sched_mp).spec_index(sched_ptr))
            == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].push(thrd_ptr)),
{
    proof { scheduler_perms_wf_map(*sched_mp); scheduler_perms_wf_at(*sched_mp, sched_ptr); }
    let shard = sched_mp.borrow_mut_shard_typed(sched_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(shard_lock_perm));
    shard.queue.push_tail(node_addr, node_perm);
    proof {
        scheduler_map_enqueue_scheduled_thread_eof_scheduler_perms_wf(*old(sched_mp), *sched_mp, sched_ptr);
        assert(scheduler_shards_of(sched_mp.spec_index(sched_ptr))
            == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].push(thrd_ptr))) by {
            reveal(scheduler_shards_of);
            assert_seqs_equal!(scheduler_shards_of(sched_mp.spec_index(sched_ptr))
                == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].push(thrd_ptr)));
        };
    }
}

/// Removes the thread at `node_addr` from anywhere in shard `cpu_id` of `sched_ptr` and returns its node.
pub fn scheduler_map_remove_scheduled_thread(sched_mp: &mut SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId, node_addr: usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(shard_lock_perm): Tracked<&LockPerm>)
    -> (ret: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
    requires
        scheduler_perms_wf(*old(sched_mp)),
        old(sched_mp).dom().contains(sched_ptr),
        index_valid(NUM_CPUS, cpu_id),
        old(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        shard_lock_perm.state() is WriteLock,
        shard_lock_perm.thread_id() == lctx.thread_id(),
        shard_lock_perm.lock_id() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom().contains(node_addr),
    ensures
        scheduler_perms_wf(*final(sched_mp)),
        final(sched_mp).unchanged_except(old(sched_mp), sched_ptr),
        final(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(sched_mp).spec_index(sched_ptr).owning_container == old(sched_mp).spec_index(sched_ptr).owning_container,
        final(sched_mp).spec_index(sched_ptr).shards.entries_unchanged_except(&old(sched_mp).spec_index(sched_ptr).shards, cpu_id),
        final(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread(),
        final(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().being_killed() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().being_killed(),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view().remove_value(old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().spec_index(node_addr)),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().remove(node_addr),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom().remove(node_addr),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.length == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.length - 1,
        ret.view().is_init(),
        ret.view().addr() == node_addr,
        ret.view().value().view() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().spec_index(node_addr),
        scheduler_shards_of(final(sched_mp).spec_index(sched_ptr)) == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int,
            scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].remove_value(old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().spec_index(node_addr))),
{
    proof { scheduler_perms_wf_map(*sched_mp); scheduler_perms_wf_at(*sched_mp, sched_ptr); }
    let shard = sched_mp.borrow_mut_shard_typed(sched_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(shard_lock_perm));
    let (_, node_perm) = shard.queue.remove(node_addr);
    proof {
        let thrd_ptr = old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().spec_index(node_addr);
        scheduler_map_remove_scheduled_thread_eof_scheduler_perms_wf(*old(sched_mp), *sched_mp, sched_ptr);
        assert(scheduler_shards_of(sched_mp.spec_index(sched_ptr)) == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].remove_value(thrd_ptr))) by {
            reveal(scheduler_shards_of);
            assert_seqs_equal!(scheduler_shards_of(sched_mp.spec_index(sched_ptr))
                == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].remove_value(thrd_ptr)));
        };
    }
    node_perm
}

/// Moves the head of shard `from` of `sched_ptr` to the tail of shard `to` and returns the head's node address.
pub fn scheduler_map_move_shard_head(sched_mp: &mut SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr, from: CpuId, to: CpuId, Tracked(lctx): Tracked<&LocalContext>, Tracked(from_lock_perm): Tracked<&LockPerm>, Tracked(to_lock_perm): Tracked<&LockPerm>) -> (ret: usize)
    requires
        scheduler_perms_wf(*old(sched_mp)),
        old(sched_mp).dom().contains(sched_ptr),
        index_valid(NUM_CPUS, from),
        index_valid(NUM_CPUS, to),
        from != to,
        old(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (sched_ptr, from), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (sched_ptr, to), TypedLockMode::Write),
        from_lock_perm.state() is WriteLock,
        from_lock_perm.thread_id() == lctx.thread_id(),
        from_lock_perm.lock_id() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(from).view().locking_thread()->Write_lock_id,
        to_lock_perm.state() is WriteLock,
        to_lock_perm.thread_id() == lctx.thread_id(),
        to_lock_perm.lock_id() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(to).view().locking_thread()->Write_lock_id,
        old(sched_mp).spec_index(sched_ptr).shard(from).queue.view().len() > 0,
        !old(sched_mp).spec_index(sched_ptr).shard(to).queue.view().contains(old(sched_mp).spec_index(sched_ptr).shard(from).queue.view()[0]),
        old(sched_mp).spec_index(sched_ptr).shard(to).queue.length != usize::MAX,
    ensures
        scheduler_perms_wf(*final(sched_mp)),
        final(sched_mp).unchanged_except(old(sched_mp), sched_ptr),
        final(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(sched_mp).spec_index(sched_ptr).owning_container == old(sched_mp).spec_index(sched_ptr).owning_container,
        forall|c: CpuId| #![trigger final(sched_mp).spec_index(sched_ptr).shards.spec_index(c)]
            index_valid(NUM_CPUS, c) && c != from && c != to ==> final(sched_mp).spec_index(sched_ptr).shards.spec_index(c) == old(sched_mp).spec_index(sched_ptr).shards.spec_index(c),
        forall|c: CpuId| #![trigger final(sched_mp).spec_index(sched_ptr).shards.spec_index(c)]
            index_valid(NUM_CPUS, c) && (c == from || c == to) ==> {
                let shard_before = old(sched_mp).spec_index(sched_ptr).shards.spec_index(c).view();
                let shard_after = final(sched_mp).spec_index(sched_ptr).shards.spec_index(c).view();
                &&& shard_after.is_init() == shard_before.is_init()
                &&& shard_after.view_rodata() == shard_before.view_rodata()
                &&& shard_after.view_ghost() == shard_before.view_ghost()
                &&& shard_after.being_killed() == shard_before.being_killed()
                &&& shard_after.locking_thread() == shard_before.locking_thread()
            },
        old(sched_mp).spec_index(sched_ptr).shard(from).queue.map().dom().contains(ret),
        old(sched_mp).spec_index(sched_ptr).shard(from).queue.map().spec_index(ret) == old(sched_mp).spec_index(sched_ptr).shard(from).queue.view()[0],
        final(sched_mp).spec_index(sched_ptr).shard(from).queue.view() == old(sched_mp).spec_index(sched_ptr).shard(from).queue.view().skip(1),
        final(sched_mp).spec_index(sched_ptr).shard(from).queue.map() == old(sched_mp).spec_index(sched_ptr).shard(from).queue.map().remove(ret),
        final(sched_mp).spec_index(sched_ptr).shard(from).queue.dom() == old(sched_mp).spec_index(sched_ptr).shard(from).queue.dom().remove(ret),
        final(sched_mp).spec_index(sched_ptr).shard(to).queue.view() == old(sched_mp).spec_index(sched_ptr).shard(to).queue.view().push(old(sched_mp).spec_index(sched_ptr).shard(from).queue.view()[0]),
        final(sched_mp).spec_index(sched_ptr).shard(to).queue.map() == old(sched_mp).spec_index(sched_ptr).shard(to).queue.map().insert(ret, old(sched_mp).spec_index(sched_ptr).shard(from).queue.view()[0]),
        final(sched_mp).spec_index(sched_ptr).shard(to).queue.dom() == old(sched_mp).spec_index(sched_ptr).shard(to).queue.dom().insert(ret),
{
    proof { scheduler_perms_wf_map(*sched_mp); scheduler_perms_wf_at(*sched_mp, sched_ptr); sched_mp.spec_index(sched_ptr).shard(from).queue.wf_implies_view_len_eq_len(); }
    let shard = sched_mp.borrow_mut_shard_typed(sched_ptr, from, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(from_lock_perm));
    let (node_addr, node_perm) = shard.queue.pop_head();
    let shard = sched_mp.borrow_mut_shard_typed(sched_ptr, to, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(to_lock_perm));
    shard.queue.push_tail(node_addr, node_perm);
    proof { scheduler_map_move_shard_head_eof_scheduler_perms_wf(*old(sched_mp), *sched_mp, sched_ptr); }
    node_addr
}

/// Moves `bdf` from `sender`'s to `receiver`'s ghost PCI set; the held root-table lock serializes both sets.
pub proof fn process_map_move_pci_function(
    tracked prc_mp: &mut ProcessLockedMap, sender: RwLockProcessPtr, receiver: RwLockProcessPtr, bdf: PciBdf,
    held_locks: Map<RwLockProcessPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        process_perms_wf(*old(prc_mp)),
        old(prc_mp).dom().contains(sender),
        old(prc_mp).dom().contains(receiver),
        sender != receiver,
    ensures
        process_perms_wf(*final(prc_mp)),
        final(prc_mp).perms_wf(),
        final(prc_mp).dom() == old(prc_mp).dom(),
        old(prc_mp).typed_lock_map_aligned(held_locks, thread_id) ==> final(prc_mp).typed_lock_map_aligned(held_locks, thread_id),
        forall|key: RwLockProcessPtr| #![trigger old(prc_mp).spec_index(key)] #![trigger final(prc_mp).spec_index(key)] old(prc_mp).dom().contains(key) ==> {
            let before = old(prc_mp).spec_index(key);
            let after = final(prc_mp).spec_index(key);
            let pci = before.view_ghost().owned_pci_functions.view();
            &&& after.is_init() == before.is_init()
            &&& after.view() == before.view()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.being_killed() == before.being_killed()
            &&& after.killer_info() == before.killer_info()
            &&& after.view_ghost().uppertree_seq == before.view_ghost().uppertree_seq
            &&& after.view_ghost().subtree_set == before.view_ghost().subtree_set
            &&& after.view_ghost().owned_pci_functions.view() == if key == sender { pci.remove(bdf) } else if key == receiver { pci.insert(bdf) } else { pci }
        },
{
    process_perms_wf_map(*prc_mp);
    let ghost sender_ghost = prc_mp.spec_index(sender).view_ghost();
    prc_mp.update_ghost(sender, ProcessGhost { owned_pci_functions: Ghost(sender_ghost.owned_pci_functions.view().remove(bdf)), ..sender_ghost });
    let ghost receiver_ghost = prc_mp.spec_index(receiver).view_ghost();
    prc_mp.update_ghost(receiver, ProcessGhost { owned_pci_functions: Ghost(receiver_ghost.owned_pci_functions.view().insert(bdf)), ..receiver_ghost });
    assert(process_perms_wf(*prc_mp)) by { reveal(process_perms_wf); };
    assert(old(prc_mp).typed_lock_map_aligned(held_locks, thread_id) ==> prc_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

pub fn pcid_allocator_map_alloc(pcid_allc_mp: &mut PcidAllocatorLockedMap, allc_ptr: RwLockPcidAllocatorPtr, prc_ptr: RwLockProcessPtr, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, Tracked(allocator_lock_perm): Tracked<&LockPerm>)
    requires
        pcid_allocator_perms_wf(*old(pcid_allc_mp)),
        old(pcid_allc_mp).dom().contains(allc_ptr),
        old(pcid_allc_mp).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pcid_allocator_lock_map(), allc_ptr, TypedLockMode::Write),
        allocator_lock_perm.state() is WriteLock,
        allocator_lock_perm.thread_id() == lctx.thread_id(),
        allocator_lock_perm.lock_id() == old(pcid_allc_mp).spec_index(allc_ptr).locking_thread()->Write_lock_id,
        old(pcid_allc_mp).spec_index(allc_ptr).view().pcid_is_free(pcid),
        old(pcid_allc_mp).spec_index(allc_ptr).view().process_is_unallocated(prc_ptr),
    ensures
        pcid_allocator_perms_wf(*final(pcid_allc_mp)),
        final(pcid_allc_mp).perms_wf(),
        final(pcid_allc_mp).unchanged_except(old(pcid_allc_mp), allc_ptr),
        final(pcid_allc_mp).dom() == old(pcid_allc_mp).dom(),
        final(pcid_allc_mp).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        final(pcid_allc_mp).spec_index(allc_ptr).view().alloc_ensures(&old(pcid_allc_mp).spec_index(allc_ptr).view(), prc_ptr, pcid),
        final(pcid_allc_mp).spec_index(allc_ptr).locking_thread() == old(pcid_allc_mp).spec_index(allc_ptr).locking_thread(),
        final(pcid_allc_mp).spec_index(allc_ptr).being_killed() == old(pcid_allc_mp).spec_index(allc_ptr).being_killed(),
        final(pcid_allc_mp).spec_index(allc_ptr).inv(),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(pcid_allc_mp).view().spec_index(ptr).is_init()]
            old(pcid_allc_mp).dom().contains(ptr) ==> {
                &&& final(pcid_allc_mp).view().spec_index(ptr).is_init() == old(pcid_allc_mp).view().spec_index(ptr).is_init()
                &&& final(pcid_allc_mp).view().spec_index(ptr).addr() == old(pcid_allc_mp).view().spec_index(ptr).addr()
            },
{
    assert(pcid_allc_mp.perms_wf() && pcid_allc_mp.spec_index(allc_ptr).is_init()
        && pcid_allc_mp.spec_index(allc_ptr).inv()) by { pcid_allocator_perms_wf_map(*pcid_allc_mp); pcid_allocator_perms_wf_at(*pcid_allc_mp, allc_ptr); };
    let allocator = pcid_allc_mp.borrow_mut_typed(allc_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(lctx), Tracked(allocator_lock_perm));
    allocator.alloc(pcid, prc_ptr);
    proof {
        pcid_allocator_map_alloc_eof_pcid_allocator_perms_wf(*old(pcid_allc_mp), *pcid_allc_mp, allc_ptr);
        assert(pcid_allc_mp.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn pcid_allocator_map_release(pcid_allc_mp: &mut PcidAllocatorLockedMap, allc_ptr: RwLockPcidAllocatorPtr, prc_ptr: RwLockProcessPtr, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, Tracked(allocator_lock_perm): Tracked<&LockPerm>)
    requires
        pcid_allocator_perms_wf(*old(pcid_allc_mp)),
        old(pcid_allc_mp).dom().contains(allc_ptr),
        old(pcid_allc_mp).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pcid_allocator_lock_map(), allc_ptr, TypedLockMode::Write),
        allocator_lock_perm.state() is WriteLock,
        allocator_lock_perm.thread_id() == lctx.thread_id(),
        allocator_lock_perm.lock_id() == old(pcid_allc_mp).spec_index(allc_ptr).locking_thread()->Write_lock_id,
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(pcid_allc_mp).spec_index(allc_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(prc_ptr),
    ensures
        pcid_allocator_perms_wf(*final(pcid_allc_mp)),
        final(pcid_allc_mp).perms_wf(),
        final(pcid_allc_mp).unchanged_except(old(pcid_allc_mp), allc_ptr),
        final(pcid_allc_mp).dom() == old(pcid_allc_mp).dom(),
        final(pcid_allc_mp).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        final(pcid_allc_mp).spec_index(allc_ptr).view().release_ensures(&old(pcid_allc_mp).spec_index(allc_ptr).view(), prc_ptr, pcid),
        final(pcid_allc_mp).spec_index(allc_ptr).locking_thread() == old(pcid_allc_mp).spec_index(allc_ptr).locking_thread(),
        final(pcid_allc_mp).spec_index(allc_ptr).being_killed() == old(pcid_allc_mp).spec_index(allc_ptr).being_killed(),
        final(pcid_allc_mp).spec_index(allc_ptr).inv(),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(pcid_allc_mp).view().spec_index(ptr).is_init()]
            old(pcid_allc_mp).dom().contains(ptr) ==> {
                &&& final(pcid_allc_mp).view().spec_index(ptr).is_init() == old(pcid_allc_mp).view().spec_index(ptr).is_init()
                &&& final(pcid_allc_mp).view().spec_index(ptr).addr() == old(pcid_allc_mp).view().spec_index(ptr).addr()
            },
{
    assert(pcid_allc_mp.perms_wf() && pcid_allc_mp.spec_index(allc_ptr).is_init()
        && pcid_allc_mp.spec_index(allc_ptr).inv()) by { pcid_allocator_perms_wf_map(*pcid_allc_mp); pcid_allocator_perms_wf_at(*pcid_allc_mp, allc_ptr); };
    let allocator = pcid_allc_mp.borrow_mut_typed(allc_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(lctx), Tracked(allocator_lock_perm));
    allocator.release(pcid, prc_ptr);
    proof {
        pcid_allocator_map_release_eof_pcid_allocator_perms_wf(*old(pcid_allc_mp), *pcid_allc_mp, allc_ptr);
        assert(pcid_allc_mp.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn process_map_link_new_child(
    prc_mp: &mut ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
    Ghost(ancestors): Ghost<Seq<RwLockProcessPtr>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(child_lock_perm): Tracked<&LockPerm>,
)
    requires
        process_perms_wf(*old(prc_mp)),
        old(prc_mp).dom().contains(parent_ptr),
        old(prc_mp).dom().contains(child_ptr),
        parent_ptr != child_ptr,
        old(prc_mp).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), parent_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), child_ptr, TypedLockMode::Write),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == lctx.thread_id(),
        parent_lock_perm.lock_id() == old(prc_mp).spec_index(parent_ptr).locking_thread()->Write_lock_id,
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == lctx.thread_id(),
        child_lock_perm.lock_id() == old(prc_mp).spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.is_init(),
        !old(prc_mp).spec_index(parent_ptr).view().children.view().contains(child_ptr),
        old(prc_mp).spec_index(parent_ptr).view().children.view().len() < usize::MAX,
        ancestors == old(prc_mp).spec_index(child_ptr).view_ghost().uppertree_seq.view(),
        ancestors.to_set().subset_of(old(prc_mp).dom()),
        ancestors.no_duplicates(),
        !ancestors.to_set().contains(child_ptr),
    ensures
        process_perms_wf(*final(prc_mp)),
        final(prc_mp).perms_wf(),
        final(prc_mp).spec_index(parent_ptr).inv(),
        final(prc_mp).spec_index(child_ptr).inv(),
        final(prc_mp).dom() == old(prc_mp).dom(),
        final(prc_mp).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(prc_mp).spec_index(child_ptr).view() == (Process { parent_linkedlist_node: final(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node, ..old(prc_mp).spec_index(child_ptr).view() }),
        !final(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.is_init(),
        final(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr() == old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        final(prc_mp).spec_index(parent_ptr).view() == (Process { children: final(prc_mp).spec_index(parent_ptr).view().children, ..old(prc_mp).spec_index(parent_ptr).view() }),
        final(prc_mp).spec_index(parent_ptr).view().children.view() == old(prc_mp).spec_index(parent_ptr).view().children.view().push(child_ptr),
        final(prc_mp).spec_index(parent_ptr).view().children.dom() == old(prc_mp).spec_index(parent_ptr).view().children.dom().insert(final(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        final(prc_mp).spec_index(parent_ptr).view().children.map() == old(prc_mp).spec_index(parent_ptr).view().children.map().insert(final(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr(), child_ptr),
        !old(prc_mp).spec_index(parent_ptr).view().children.map().dom().contains(final(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).spec_index(ptr)]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& final(prc_mp).spec_index(ptr).is_init() == old(prc_mp).spec_index(ptr).is_init()
                &&& final(prc_mp).spec_index(ptr).view_rodata() == old(prc_mp).spec_index(ptr).view_rodata()
                &&& final(prc_mp).spec_index(ptr).view_ghost().uppertree_seq == old(prc_mp).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions == old(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(prc_mp).spec_index(ptr).locking_thread() == old(prc_mp).spec_index(ptr).locking_thread()
                &&& final(prc_mp).spec_index(ptr).being_killed() == old(prc_mp).spec_index(ptr).being_killed()
                &&& ptr != parent_ptr && ptr != child_ptr ==> final(prc_mp).spec_index(ptr).view() == old(prc_mp).spec_index(ptr).view()
                &&& ptr != parent_ptr && ptr != child_ptr ==> final(prc_mp).spec_index(ptr).killer_info() == old(prc_mp).spec_index(ptr).killer_info()
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).spec_index(ptr).view_ghost().subtree_set]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& ancestors.to_set().contains(ptr) ==> final(prc_mp).spec_index(ptr).view_ghost().subtree_set.view() == old(prc_mp).spec_index(ptr).view_ghost().subtree_set.view().insert(child_ptr)
                &&& !ancestors.to_set().contains(ptr) ==> final(prc_mp).spec_index(ptr).view_ghost().subtree_set == old(prc_mp).spec_index(ptr).view_ghost().subtree_set
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).view().spec_index(ptr).is_init()]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& final(prc_mp).view().spec_index(ptr).is_init() == old(prc_mp).view().spec_index(ptr).is_init()
                &&& final(prc_mp).view().spec_index(ptr).addr() == old(prc_mp).view().spec_index(ptr).addr()
            },
{
    assert(prc_mp.perms_wf() && prc_mp.spec_index(child_ptr).is_init() && prc_mp.spec_index(child_ptr).inv() && prc_mp.spec_index(parent_ptr).is_init()
        && prc_mp.spec_index(parent_ptr).inv()) by { process_perms_wf_map(*prc_mp); process_perms_wf_at(*prc_mp, child_ptr); process_perms_wf_at(*prc_mp, parent_ptr); };
    let child = prc_mp.borrow_mut_typed(child_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(child_lock_perm));
    let (child_node_addr, child_node_perm) = child.parent_linkedlist_node.take();
    proof { assert(prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let parent = prc_mp.borrow_mut_typed(parent_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(parent_lock_perm));
    parent.add_child(child_ptr, child_node_addr, child_node_perm);
    proof {
        process_map_link_new_child_eof_process_perms_wf(*old(prc_mp), *prc_mp, parent_ptr, child_ptr);
        assert(prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        process_insert_child_into_ancestor_subtree_sets(prc_mp, ancestors, child_ptr, lctx.process_lock_map(), lctx.thread_id());
    }
}

/// Unlinks the retired leaf `child_ptr` from its write-held parent's child list and every ancestor's subtree set.
pub fn process_map_unlink_child(
    prc_mp: &mut ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
    Ghost(ancestors): Ghost<Seq<RwLockProcessPtr>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(child_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PointsTo<Node<RwLockProcessPtr>>>)
    requires
        process_perms_wf(*old(prc_mp)),
        old(prc_mp).dom().contains(parent_ptr),
        old(prc_mp).dom().contains(child_ptr),
        parent_ptr != child_ptr,
        old(prc_mp).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), parent_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), child_ptr, TypedLockMode::Write),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == lctx.thread_id(),
        parent_lock_perm.lock_id() == old(prc_mp).spec_index(parent_ptr).locking_thread()->Write_lock_id,
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == lctx.thread_id(),
        child_lock_perm.lock_id() == old(prc_mp).spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(prc_mp).spec_index(parent_ptr).view().children.map().dom().contains(old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        old(prc_mp).spec_index(parent_ptr).view().children.map().spec_index(old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr,
        ancestors == old(prc_mp).spec_index(child_ptr).view_ghost().uppertree_seq.view(),
        ancestors.to_set().subset_of(old(prc_mp).dom()),
        ancestors.no_duplicates(),
    ensures
        process_perms_wf(*final(prc_mp)),
        final(prc_mp).perms_wf(),
        final(prc_mp).spec_index(parent_ptr).inv(),
        final(prc_mp).dom() == old(prc_mp).dom(),
        final(prc_mp).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(prc_mp).spec_index(parent_ptr).view() == (Process { children: final(prc_mp).spec_index(parent_ptr).view().children, ..old(prc_mp).spec_index(parent_ptr).view() }),
        final(prc_mp).spec_index(parent_ptr).view().children.view() == old(prc_mp).spec_index(parent_ptr).view().children.view().remove_value(child_ptr),
        final(prc_mp).spec_index(parent_ptr).view().children.dom() == old(prc_mp).spec_index(parent_ptr).view().children.dom().remove(old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        final(prc_mp).spec_index(parent_ptr).view().children.map() == old(prc_mp).spec_index(parent_ptr).view().children.map().remove(old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).spec_index(ptr)]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& final(prc_mp).spec_index(ptr).is_init() == old(prc_mp).spec_index(ptr).is_init()
                &&& final(prc_mp).spec_index(ptr).view_rodata() == old(prc_mp).spec_index(ptr).view_rodata()
                &&& final(prc_mp).spec_index(ptr).view_ghost().uppertree_seq == old(prc_mp).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions == old(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(prc_mp).spec_index(ptr).locking_thread() == old(prc_mp).spec_index(ptr).locking_thread()
                &&& final(prc_mp).spec_index(ptr).being_killed() == old(prc_mp).spec_index(ptr).being_killed()
                &&& final(prc_mp).spec_index(ptr).killer_info() == old(prc_mp).spec_index(ptr).killer_info()
                &&& ptr != parent_ptr ==> final(prc_mp).spec_index(ptr).view() == old(prc_mp).spec_index(ptr).view()
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).spec_index(ptr).view_ghost().subtree_set]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& ancestors.to_set().contains(ptr) ==> final(prc_mp).spec_index(ptr).view_ghost().subtree_set.view() == old(prc_mp).spec_index(ptr).view_ghost().subtree_set.view().remove(child_ptr)
                &&& !ancestors.to_set().contains(ptr) ==> final(prc_mp).spec_index(ptr).view_ghost().subtree_set == old(prc_mp).spec_index(ptr).view_ghost().subtree_set
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).view().spec_index(ptr).is_init()]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& final(prc_mp).view().spec_index(ptr).is_init() == old(prc_mp).view().spec_index(ptr).is_init()
                &&& final(prc_mp).view().spec_index(ptr).addr() == old(prc_mp).view().spec_index(ptr).addr()
            },
        ret.view().is_init(),
        ret.view().addr() == old(prc_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        ret.view().value().view() == child_ptr,
{
    assert(prc_mp.perms_wf() && prc_mp.spec_index(child_ptr).is_init()) by { process_perms_wf_map(*prc_mp); process_perms_wf_at(*prc_mp, child_ptr); };
    let node_addr = prc_mp.borrow_typed(child_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(child_lock_perm)).parent_linkedlist_node.addr();
    assert(prc_mp.spec_index(parent_ptr).is_init() && prc_mp.spec_index(parent_ptr).inv() && prc_mp.spec_index(parent_ptr).view().children.dom().contains(node_addr)) by {
        process_perms_wf_at(*prc_mp, parent_ptr); prc_mp.spec_index(parent_ptr).view().children.wf_map_at(node_addr);
    };
    let parent = prc_mp.borrow_mut_typed(parent_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(parent_lock_perm));
    let node_perm = parent.remove_child(node_addr);
    proof {
        assert(prc_mp.spec_index(parent_ptr).view().children.view().no_duplicates()) by { reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
        process_map_unlink_child_eof_process_perms_wf(*old(prc_mp), *prc_mp, parent_ptr, child_ptr);
        process_remove_child_from_ancestor_subtree_sets(prc_mp, ancestors, child_ptr, lctx.process_lock_map(), lctx.thread_id());
    }
    node_perm
}

pub fn process_subsystem_create_scheduled_thread(
    ctn_mp: &ContainerLockedMap, prc_mp: &mut ProcessLockedMap, thrd_mp: &mut ThreadLockedMap,
    sched_mp: &mut SchedulerUnLockedMap, pg_ptr: PagePtr, prc_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId,
    thread_value: Thread, initial_regs: &Registers, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(shard_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<LockPerm>, usize, usize))
    requires
        container_perms_wf(*ctn_mp),
        process_perms_wf(*old(prc_mp)),
        thread_perms_wf(*old(thrd_mp)),
        scheduler_perms_wf(*old(sched_mp)),
        container_process_wf(*ctn_mp, *old(prc_mp)),
        container_thread_wf(*ctn_mp, *old(thrd_mp)),
        container_scheduler_wf(*ctn_mp, *old(sched_mp)),
        process_thread_wf(*old(prc_mp), *old(thrd_mp)),
        container_thread_scheduler_wf(*ctn_mp, *old(thrd_mp), *old(sched_mp)),
        old(prc_mp).dom().contains(prc_ptr),
        old(thrd_mp).dom().contains(staging_thrd_ptr),
        !old(thrd_mp).dom().contains(pg_ptr),
        pg_ptr != staging_thrd_ptr,
        ctn_mp.dom().contains(ctn_ptr),
        old(sched_mp).dom().contains(sched_ptr),
        ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr,
        old(prc_mp).spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        old(sched_mp).spec_index(sched_ptr).owning_container == ctn_ptr,
        index_valid(NUM_CPUS, cpu_id),
        old(prc_mp).spec_index(prc_ptr).view().state.view() is Creating || old(prc_mp).spec_index(prc_ptr).view().state.view() is Running,
        !old(prc_mp).spec_index(prc_ptr).view().owned_threads.view().contains(pg_ptr),
        old(prc_mp).spec_index(prc_ptr).view().owned_threads.view().len() < usize::MAX,
        !old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view().contains(pg_ptr),
        old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.length != usize::MAX,
        old(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![pg_ptr],
        old(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(thrd_mp).spec_index(staging_thrd_ptr).view().free_quota_pending_clean(),
        old(thrd_mp).spec_index(staging_thrd_ptr).view().quota_4k >= 1,
        thread_value.inv(),
        thread_value.state is RUNNING,
        thread_value.scheduler_linkedlist_node.is_init(),
        thread_value.proc_linkedlist_node.is_init(),
        thread_value.owning_container == ctn_ptr,
        thread_value.container_depth == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth,
        thread_value.container_depth == old(prc_mp).spec_index(prc_ptr).view_rodata().view().container_depth,
        thread_value.owning_proc == prc_ptr,
        thread_value.process_depth == old(prc_mp).spec_index(prc_ptr).view_rodata().view().depth,
        thread_value.proc_pagetable_ptr == old(prc_mp).spec_index(prc_ptr).view().pagetable,
        page_perm.is_init(),
        page_perm.addr() == pg_ptr,
        old(prc_mp).typed_lock_map_aligned(old(lctx).process_lock_map(), old(lctx).thread_id()),
        old(thrd_mp).typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id()),
        old(sched_mp).typed_shard_lock_map_aligned(old(lctx).scheduler_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(prc_mp).spec_index(prc_ptr).locking_thread()->Write_lock_id,
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(thrd_mp).spec_index(staging_thrd_ptr).locking_thread()->Write_lock_id,
        shard_lock_perm.state() is WriteLock,
        shard_lock_perm.thread_id() == old(lctx).thread_id(),
        shard_lock_perm.lock_id() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        process_perms_wf(*final(prc_mp)),
        thread_perms_wf(*final(thrd_mp)),
        scheduler_perms_wf(*final(sched_mp)),
        process_subsystem_create_scheduled_thread_eof_transition_framing(*old(prc_mp), *final(prc_mp), *old(thrd_mp), *final(thrd_mp),
            *old(sched_mp), *final(sched_mp), old(lctx), final(lctx), pg_ptr, prc_ptr, staging_thrd_ptr, sched_ptr, cpu_id, final(thrd_mp).spec_index(pg_ptr).view(), ret.2, ret.1),
        process_thread_wf(*final(prc_mp), *final(thrd_mp)),
        container_thread_scheduler_wf(*ctn_mp, *final(thrd_mp), *final(sched_mp)),
        forall|t_ptr: RwLockThreadPtr| #![trigger final(thrd_mp).dom().contains(t_ptr)] final(thrd_mp).dom().contains(t_ptr) ==> ctn_mp.dom().contains(final(thrd_mp).spec_index(t_ptr).view().owning_container),
        forall|c_ptr: RwLockContainerPtr| #![trigger ctn_mp.dom().contains(c_ptr)] ctn_mp.dom().contains(c_ptr) ==> final(sched_mp).dom().contains(ctn_mp.spec_index(c_ptr).view_rodata().view().scheduler),
        final(prc_mp).dom() == old(prc_mp).dom(),
        final(thrd_mp).dom() =~= old(thrd_mp).dom().insert(pg_ptr),
        forall|t: RwLockThreadPtr| #![trigger final(thrd_mp).spec_index(t)]
            old(thrd_mp).dom().contains(t) ==> final(thrd_mp).spec_index(t).view().endpoint_descriptors.view() == old(thrd_mp).spec_index(t).view().endpoint_descriptors.view(),
        final(thrd_mp).spec_index(pg_ptr).view() == (Thread { state: ThreadState::SCHEDULED { cpu_id }, last_cpu: cpu_id, trap_frame: final(thrd_mp).spec_index(pg_ptr).view().trap_frame,
            scheduler_linkedlist_node: final(thrd_mp).spec_index(pg_ptr).view().scheduler_linkedlist_node,
            proc_linkedlist_node: final(thrd_mp).spec_index(pg_ptr).view().proc_linkedlist_node, ..thread_value }),
        final(thrd_mp).spec_index(pg_ptr).view().trap_frame.is_some(),
        *final(thrd_mp).spec_index(pg_ptr).view().trap_frame.get_some_0() == *initial_regs,
        !final(thrd_mp).spec_index(pg_ptr).view().scheduler_linkedlist_node.is_init(),
        !final(thrd_mp).spec_index(pg_ptr).view().proc_linkedlist_node.is_init(),
        ret.1 == final(thrd_mp).spec_index(pg_ptr).view().scheduler_linkedlist_node.addr(),
        ret.2 == final(thrd_mp).spec_index(pg_ptr).view().proc_linkedlist_node.addr(),
        final(thrd_mp).spec_index(pg_ptr).is_init(),
        final(thrd_mp).spec_index(pg_ptr).inv(),
        final(thrd_mp).spec_index(pg_ptr).being_killed() == false,
        final(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() == old(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view().remove(pg_ptr),
        final(thrd_mp).spec_index(staging_thrd_ptr).view().quota_4k == old(thrd_mp).spec_index(staging_thrd_ptr).view().quota_4k - 1,
        final(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_clean(),
        final(thrd_mp).spec_index(staging_thrd_ptr).view().free_quota_pending_clean(),
        final(thrd_mp).spec_index(staging_thrd_ptr).view() == (Thread { quota_4k: final(thrd_mp).spec_index(staging_thrd_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(thrd_mp).spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k, ..old(thrd_mp).spec_index(staging_thrd_ptr).view() }),
        final(thrd_mp).spec_index(staging_thrd_ptr).being_killed() == old(thrd_mp).spec_index(staging_thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(staging_thrd_ptr).killer_info() == old(thrd_mp).spec_index(staging_thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(staging_thrd_ptr).view_ghost() == old(thrd_mp).spec_index(staging_thrd_ptr).view_ghost(),
        final(thrd_mp).spec_index(staging_thrd_ptr).locking_thread() == old(thrd_mp).spec_index(staging_thrd_ptr).locking_thread(),
        final(thrd_mp).lock_id_by_key(staging_thrd_ptr) == old(thrd_mp).lock_id_by_key(staging_thrd_ptr),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.view() == old(prc_mp).spec_index(prc_ptr).view().owned_threads.view().push(pg_ptr),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.dom() == old(prc_mp).spec_index(prc_ptr).view().owned_threads.dom().insert(ret.2),
        final(prc_mp).spec_index(prc_ptr).view().owned_threads.map() == old(prc_mp).spec_index(prc_ptr).view().owned_threads.map().insert(ret.2, pg_ptr),
        !old(prc_mp).spec_index(prc_ptr).view().owned_threads.dom().contains(ret.2),
        !old(prc_mp).spec_index(prc_ptr).view().owned_threads.map().dom().contains(ret.2),
        final(prc_mp).spec_index(prc_ptr).view() == (Process { owned_threads: final(prc_mp).spec_index(prc_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..old(prc_mp).spec_index(prc_ptr).view() }),
        final(prc_mp).spec_index(prc_ptr).view_rodata() == old(prc_mp).spec_index(prc_ptr).view_rodata(),
        final(prc_mp).spec_index(prc_ptr).being_killed() == old(prc_mp).spec_index(prc_ptr).being_killed(),
        final(prc_mp).spec_index(prc_ptr).locking_thread() == old(prc_mp).spec_index(prc_ptr).locking_thread(),
        final(prc_mp).lock_id_by_key(prc_ptr) == old(prc_mp).lock_id_by_key(prc_ptr),
        final(sched_mp).unchanged_except(old(sched_mp), sched_ptr),
        final(sched_mp).spec_index(sched_ptr).owning_container == old(sched_mp).spec_index(sched_ptr).owning_container,
        final(sched_mp).spec_index(sched_ptr).shards.entries_unchanged_except(&old(sched_mp).spec_index(sched_ptr).shards, cpu_id),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.view().push(pg_ptr),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom().insert(ret.1),
        final(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map() == old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().insert(ret.1, pg_ptr),
        !old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.dom().contains(ret.1),
        !old(sched_mp).spec_index(sched_ptr).shard(cpu_id).queue.map().dom().contains(ret.1),
        final(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().being_killed() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().being_killed(),
        final(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(sched_mp).spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread(),
        scheduler_shards_of(final(sched_mp).spec_index(sched_ptr))
            == scheduler_shards_of(old(sched_mp).spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(old(sched_mp).spec_index(sched_ptr))[cpu_id as int].push(pg_ptr)),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(prc_mp).spec_index(ptr)]
            old(prc_mp).dom().contains(ptr) ==> {
                &&& final(prc_mp).spec_index(ptr).view().children == old(prc_mp).spec_index(ptr).view().children
                &&& final(prc_mp).spec_index(ptr).view_ghost().uppertree_seq == old(prc_mp).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(prc_mp).spec_index(ptr).view_ghost().subtree_set == old(prc_mp).spec_index(ptr).view_ghost().subtree_set
                &&& final(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions == old(prc_mp).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(prc_mp).spec_index(ptr).view_rodata() == old(prc_mp).spec_index(ptr).view_rodata()
            },
        forall|ptr: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(ptr)] old(prc_mp).dom().contains(ptr) && ptr != prc_ptr ==> final(prc_mp).spec_index(ptr) == old(prc_mp).spec_index(ptr),
        forall|ptr: RwLockThreadPtr| #![trigger final(thrd_mp).spec_index(ptr)] old(thrd_mp).dom().contains(ptr) && ptr != staging_thrd_ptr ==> final(thrd_mp).spec_index(ptr) == old(thrd_mp).spec_index(ptr),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(thrd_mp).spec_index(pg_ptr).locking_thread()->Write_lock_id,
        final(thrd_mp).spec_index(pg_ptr).write_lock_perm_match(&ret.0.view()),
        !final(thrd_mp).spec_index(pg_ptr).view_ghost().exited,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(pg_ptr), TypedHeldLock { lock_id: final(thrd_mp).lock_id_by_key(pg_ptr), mode: TypedLockMode::Write }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(pg_ptr, TypedHeldLock { lock_id: final(thrd_mp).lock_id_by_key(pg_ptr), mode: TypedLockMode::Write }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(prc_mp).typed_lock_map_aligned(final(lctx).process_lock_map(), final(lctx).thread_id()),
        final(thrd_mp).typed_lock_map_aligned(final(lctx).thread_lock_map(), final(lctx).thread_id()),
        final(sched_mp).typed_shard_lock_map_aligned(final(lctx).scheduler_lock_map(), final(lctx).thread_id()),
{
    thread_map_consume_staged_4k(thrd_mp, staging_thrd_ptr, pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    proof {
        assert(!lctx.thread_lock_map().dom().contains(pg_ptr)
            && lctx.typed_lock_entry(KernelObjId::Thread(pg_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    let Tracked(thread_lock_perm) = thrd_mp.retype_4k_and_insert(pg_ptr, thread_value, (), Ghost(ThreadGhost { chain_end: None, exited: false }), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Thread(pg_ptr)));
    let ghost fresh_lock_id = thrd_mp.lock_id_by_key(pg_ptr);
    proof { assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let thread = thrd_mp.borrow_mut_typed(pg_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let (sched_node_addr, sched_node_perm, process_node_addr, process_node_perm) = thread.fresh_to_scheduled(pg_ptr, cpu_id, initial_regs);
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(pg_ptr), fresh_lock_id, thrd_mp.lock_id_by_key(pg_ptr));
        assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().insert(pg_ptr, TypedHeldLock { lock_id: thrd_mp.lock_id_by_key(pg_ptr), mode: TypedLockMode::Write }));
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    process_map_add_owned_thread(prc_mp, prc_ptr, pg_ptr, process_node_addr, process_node_perm, Tracked(&*lctx), Tracked(process_lock_perm));
    scheduler_map_enqueue_scheduled_thread(sched_mp, sched_ptr, cpu_id, pg_ptr, sched_node_addr, sched_node_perm, Tracked(&*lctx), Tracked(shard_lock_perm));
    let ghost stored_thread = thrd_mp.spec_index(pg_ptr).view();
    proof {
        assert(process_subsystem_create_scheduled_thread_eof_transition_framing(*old(prc_mp), *prc_mp, *old(thrd_mp), *thrd_mp, *old(sched_mp), *sched_mp,
            old(lctx), &*lctx, pg_ptr, prc_ptr, staging_thrd_ptr, sched_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr)) by { reveal(process_subsystem_create_scheduled_thread_eof_transition_framing); };
        assert(!old(prc_mp).spec_index(prc_ptr).view().zombie) by { process_perms_wf_at(*old(prc_mp), prc_ptr); };
        process_subsystem_create_scheduled_thread_eof_process_thread_wf(*old(prc_mp), *prc_mp, *old(thrd_mp), *thrd_mp, *old(sched_mp),
            *sched_mp, old(lctx), &*lctx, pg_ptr, prc_ptr, staging_thrd_ptr, sched_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr);
        process_subsystem_create_scheduled_thread_eof_thread_perms_wf(*old(prc_mp), *prc_mp, *old(thrd_mp), *thrd_mp, *old(sched_mp),
            *sched_mp, old(lctx), &*lctx, pg_ptr, prc_ptr, staging_thrd_ptr, sched_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr);
        process_subsystem_create_scheduled_thread_eof_scheduler_wf(*ctn_mp, *old(prc_mp), *prc_mp, *old(thrd_mp), *thrd_mp,
            *old(sched_mp), *sched_mp, old(lctx), &*lctx, pg_ptr, prc_ptr, staging_thrd_ptr, ctn_ptr, sched_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr);
    }
    (Tracked(thread_lock_perm), sched_node_addr, process_node_addr)
}

pub fn thread_map_consume_new_container_staging(
    threads: &mut ThreadLockedMap, current_thrd_ptr: RwLockThreadPtr, thread_page: PagePtr, funding_page_count: usize,
    Ghost(consumed_4k_pages): Ghost<Set<PagePtr>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(threads)),
        old(threads).dom().contains(current_thrd_ptr),
        old(threads).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == lctx.thread_id(),
        current_thread_lock_perm.lock_id() == old(threads).spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        old(threads).spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view() == consumed_4k_pages.insert(thread_page),
        !consumed_4k_pages.contains(thread_page),
        consumed_4k_pages.len() == 8 + funding_page_count,
        old(threads).spec_index(current_thrd_ptr).view().quota_4k >= 8,
        funding_page_count < old(threads).spec_index(current_thrd_ptr).view().quota_4k - 8,
        old(threads).spec_index(current_thrd_ptr).view().temp_alloc_cache_2m.view().len() == 2,
        old(threads).spec_index(current_thrd_ptr).view().quota_2m >= 2,
    ensures
        final(threads).spec_index(current_thrd_ptr).inv(),
        final(threads).perms_wf(),
        thread_perms_wf(*final(threads)),
        final(threads).unchanged_except(old(threads), current_thrd_ptr),
        final(threads).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(threads).spec_index(current_thrd_ptr).locking_thread() == old(threads).spec_index(current_thrd_ptr).locking_thread(),
        final(threads).spec_index(current_thrd_ptr).being_killed() == old(threads).spec_index(current_thrd_ptr).being_killed(),
        final(threads).spec_index(current_thrd_ptr).killer_info() == old(threads).spec_index(current_thrd_ptr).killer_info(),
        final(threads).spec_index(current_thrd_ptr).view_ghost() == old(threads).spec_index(current_thrd_ptr).view_ghost(),
        thread_quota_4k_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_2m_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_1g_fields_unchanged(*old(threads), *final(threads)),
        final(threads).spec_index(current_thrd_ptr).view() == (Thread { temp_alloc_cache_4k: Ghost(set![thread_page]), temp_alloc_cache_2m: Ghost(Set::empty()),
            quota_4k: (old(threads).spec_index(current_thrd_ptr).view().quota_4k as int - 8 - funding_page_count as int) as usize,
            quota_2m: (old(threads).spec_index(current_thrd_ptr).view().quota_2m as int - 2) as usize, ..old(threads).spec_index(current_thrd_ptr).view() }),
{
    assert(threads.perms_wf() && threads.spec_index(current_thrd_ptr).is_init()
        && threads.spec_index(current_thrd_ptr).view().inv()) by { thread_perms_wf_map(*threads); thread_perms_wf_at(*threads, current_thrd_ptr); };
    let thread = threads.borrow_mut_typed(current_thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(current_thread_lock_perm));
    thread.temp_alloc_cache_4k = Ghost(Set::empty().insert(thread_page));
    thread.temp_alloc_cache_2m = Ghost(Set::empty());
    thread.quota_4k = thread.quota_4k - 8 - funding_page_count;
    thread.quota_2m = thread.quota_2m - 2;
    proof {
        thread_map_consume_new_container_staging_eof_thread_perms_wf(*old(threads), *threads, current_thrd_ptr);
        assert(threads.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(thread_quota_4k_fields_unchanged(*old(threads), *threads)) by { vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page); };
    }
}

/// Publishes a fresh scheduler whose shards are all unlocked.
pub fn scheduler_map_insert_new_4k(sched_mp: &mut SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr, scheduler_value: Scheduler, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&LocalContext>)
    requires
        old(sched_mp).perms_wf(),
        !old(sched_mp).dom().contains(sched_ptr),
        old(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        scheduler_value.inv(),
        forall|cpu_id: CpuId| #![trigger scheduler_value.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> !scheduler_value.shards.spec_index(cpu_id).view().locked(),
        page_perm.is_init(),
        page_perm.addr() == sched_ptr,
    ensures
        final(sched_mp).perms_wf(),
        scheduler_perms_wf(*old(sched_mp)) ==> scheduler_perms_wf(*final(sched_mp)),
        final(sched_mp).dom() =~= old(sched_mp).dom().insert(sched_ptr),
        forall|ptr: RwLockSchedulerPtr| #![trigger final(sched_mp).spec_index(ptr)] old(sched_mp).dom().contains(ptr) ==> final(sched_mp).spec_index(ptr) == old(sched_mp).spec_index(ptr),
        final(sched_mp).spec_index(sched_ptr) == scheduler_value,
        final(sched_mp).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
{
    sched_mp.retype_page_to_scheduler_and_insert(sched_ptr, scheduler_value, Tracked(page_perm), Tracked(lctx));
    proof {
        scheduler_map_insert_new_4k_eof_scheduler_perms_wf(*old(sched_mp), *sched_mp, sched_ptr);
        assert(sched_mp.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id())) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
    }
}

pub fn cpu_set_map_insert_new_4k(cpu_set_mp: &mut CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr, cpu_set_value: CpuSet, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(cpu_set_mp).perms_wf(),
        !old(cpu_set_mp).dom().contains(cpu_set_ptr),
        old(cpu_set_mp).typed_lock_map_aligned(old(lctx).cpu_set_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        cpu_set_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == cpu_set_ptr,
    ensures
        final(cpu_set_mp).perms_wf(),
        cpu_set_perms_wf(*old(cpu_set_mp)) ==> cpu_set_perms_wf(*final(cpu_set_mp)),
        final(cpu_set_mp).dom() =~= old(cpu_set_mp).dom().insert(cpu_set_ptr),
        forall|ptr: RwLockCpuSetPtr| #![trigger final(cpu_set_mp).spec_index(ptr)] old(cpu_set_mp).dom().contains(ptr) ==> final(cpu_set_mp).spec_index(ptr) == old(cpu_set_mp).spec_index(ptr),
        final(cpu_set_mp).spec_index(cpu_set_ptr).view() == cpu_set_value,
        final(cpu_set_mp).spec_index(cpu_set_ptr).inv(),
        !final(cpu_set_mp).spec_index(cpu_set_ptr).being_killed(),
        final(cpu_set_mp).spec_index(cpu_set_ptr).write_lock_perm_match(&ret.view()),
        final(cpu_set_mp).typed_lock_map_aligned(final(lctx).cpu_set_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), TypedHeldLock { lock_id: final(cpu_set_mp).lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::CpuSet(cpu_set_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = cpu_set_mp.retype_4k_and_insert(cpu_set_ptr, cpu_set_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
    proof {
        cpu_set_map_insert_new_4k_eof_cpu_set_perms_wf(*old(cpu_set_mp), *cpu_set_mp, cpu_set_ptr);
        assert(cpu_set_mp.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}

pub fn pcid_allocator_map_insert_new_2m(pcid_allc_mp: &mut PcidAllocatorLockedMap, allc_ptr: RwLockPcidAllocatorPtr, allocator_value: PcidAllocator, Tracked(page_perm): Tracked<PagePerm2m>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(pcid_allc_mp).perms_wf(),
        !old(pcid_allc_mp).dom().contains(allc_ptr),
        old(pcid_allc_mp).typed_lock_map_aligned(old(lctx).pcid_allocator_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        allocator_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == allc_ptr,
    ensures
        final(pcid_allc_mp).perms_wf(),
        pcid_allocator_perms_wf(*old(pcid_allc_mp)) ==> pcid_allocator_perms_wf(*final(pcid_allc_mp)),
        final(pcid_allc_mp).dom() =~= old(pcid_allc_mp).dom().insert(allc_ptr),
        forall|ptr: RwLockPcidAllocatorPtr| #![trigger final(pcid_allc_mp).spec_index(ptr)] old(pcid_allc_mp).dom().contains(ptr) ==> final(pcid_allc_mp).spec_index(ptr) == old(pcid_allc_mp).spec_index(ptr),
        final(pcid_allc_mp).spec_index(allc_ptr).view() == allocator_value,
        final(pcid_allc_mp).spec_index(allc_ptr).is_init(),
        final(pcid_allc_mp).spec_index(allc_ptr).inv(),
        !final(pcid_allc_mp).spec_index(allc_ptr).being_killed(),
        final(pcid_allc_mp).spec_index(allc_ptr).wlocked_by(final(lctx)),
        final(pcid_allc_mp).spec_index(allc_ptr).write_lock_perm_match(&ret.view()),
        final(pcid_allc_mp).typed_lock_map_aligned(final(lctx).pcid_allocator_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PcidAllocator(allc_ptr), TypedHeldLock { lock_id: final(pcid_allc_mp).lock_id_by_key(allc_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(pcid_allc_mp).lock_id_by_key(allc_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::PcidAllocator(allc_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = pcid_allc_mp.retype_2m_and_insert(allc_ptr, allocator_value, (), Ghost(()), Tracked(page_perm),
        Tracked(&mut *lctx), Ghost(KernelObjId::PcidAllocator(allc_ptr)), LockControl::Clear);
    proof {
        pcid_allocator_map_insert_new_2m_eof_pcid_allocator_perms_wf(*old(pcid_allc_mp), *pcid_allc_mp, allc_ptr);
        assert(pcid_allc_mp.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}

pub fn thread_map_set_endpoint_descriptor(
    thrd_mp: &mut ThreadLockedMap, thrd_ptr: RwLockThreadPtr, ep_idx: EndpointIdx, ep_ptr: Option<RwLockEndpointPtr>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(thrd_ptr),
        old(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thrd_mp).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        edp_idx_valid(ep_idx),
        !old(thrd_mp).spec_index(thrd_ptr).view().state.is_endpoint_waiting(),
        !(old(thrd_mp).spec_index(thrd_ptr).view().state is DANGLING),
    ensures
        thread_perms_wf(*final(thrd_mp)),
        final(thrd_mp).perms_wf(),
        final(thrd_mp).spec_index(thrd_ptr).inv(),
        final(thrd_mp).unchanged_except(old(thrd_mp), thrd_ptr),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        forall|ptr: RwLockThreadPtr| #![trigger final(thrd_mp).spec_index(ptr)] old(thrd_mp).dom().contains(ptr) && ptr != thrd_ptr ==> final(thrd_mp).spec_index(ptr) == old(thrd_mp).spec_index(ptr),
        final(thrd_mp).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thrd_mp).spec_index(thrd_ptr).view() == (Thread { endpoint_descriptors: final(thrd_mp).spec_index(thrd_ptr).view().endpoint_descriptors, ..old(thrd_mp).spec_index(thrd_ptr).view() }),
        final(thrd_mp).spec_index(thrd_ptr).view().endpoint_descriptors.view() == old(thrd_mp).spec_index(thrd_ptr).view().endpoint_descriptors.view().update(ep_idx as int, ep_ptr),
        final(thrd_mp).lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr),
        final(thrd_mp).spec_index(thrd_ptr).locking_thread() == old(thrd_mp).spec_index(thrd_ptr).locking_thread(),
        final(thrd_mp).spec_index(thrd_ptr).being_killed() == old(thrd_mp).spec_index(thrd_ptr).being_killed(),
        final(thrd_mp).spec_index(thrd_ptr).killer_info() == old(thrd_mp).spec_index(thrd_ptr).killer_info(),
        final(thrd_mp).spec_index(thrd_ptr).view_ghost() == old(thrd_mp).spec_index(thrd_ptr).view_ghost(),
{
    assert(thrd_mp.perms_wf() && thrd_mp.spec_index(thrd_ptr).is_init() && thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_map(*thrd_mp); thread_perms_wf_at(*thrd_mp, thrd_ptr); };
    let thread = thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.endpoint_descriptors.set(ep_idx, ep_ptr);
    proof {
        thread_map_set_endpoint_descriptor_eof_thread_perms_wf(*old(thrd_mp), *thrd_mp, thrd_ptr);
        assert(thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thrd_mp.lock_id_by_key(thrd_ptr) == old(thrd_mp).lock_id_by_key(thrd_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn endpoint_map_insert_new_4k(ep_mp: &mut EndpointLockedMap, ep_ptr: RwLockEndpointPtr, endpoint_value: Endpoint, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(ep_mp).perms_wf(),
        !old(ep_mp).dom().contains(ep_ptr),
        old(ep_mp).typed_lock_map_aligned(old(lctx).endpoint_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        endpoint_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == ep_ptr,
    ensures
        final(ep_mp).perms_wf(),
        endpoint_perms_wf(*old(ep_mp)) ==> endpoint_perms_wf(*final(ep_mp)),
        final(ep_mp).dom() =~= old(ep_mp).dom().insert(ep_ptr),
        forall|ptr: RwLockEndpointPtr| #![trigger final(ep_mp).spec_index(ptr)] old(ep_mp).dom().contains(ptr) ==> final(ep_mp).spec_index(ptr) == old(ep_mp).spec_index(ptr),
        final(ep_mp).spec_index(ep_ptr).view() == endpoint_value,
        final(ep_mp).spec_index(ep_ptr).is_init(),
        final(ep_mp).spec_index(ep_ptr).inv(),
        !final(ep_mp).spec_index(ep_ptr).being_killed(),
        final(ep_mp).spec_index(ep_ptr).wlocked_by(final(lctx)),
        final(ep_mp).spec_index(ep_ptr).write_lock_perm_match(&ret.view()),
        final(ep_mp).typed_lock_map_aligned(final(lctx).endpoint_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Endpoint(ep_ptr), TypedHeldLock { lock_id: final(ep_mp).lock_id_by_key(ep_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(ep_mp).lock_id_by_key(ep_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::Endpoint(ep_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = ep_mp.retype_4k_and_insert(ep_ptr, endpoint_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Endpoint(ep_ptr)));
    proof {
        endpoint_map_insert_new_4k_eof_endpoint_perms_wf(*old(ep_mp), *ep_mp, ep_ptr);
        assert(ep_mp.typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}
}

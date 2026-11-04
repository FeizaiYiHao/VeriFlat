use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;
use crate::*;
use super::process_subsystem_mutation_eof::*;

verus! {
pub proof fn container_map_add_owned_process(tracked ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        container_perms_wf(*old(ctn_mp)),
        old(ctn_mp).dom().contains(ctn_ptr),
    ensures
        container_perms_wf(*final(ctn_mp)),
        final(ctn_mp).perms_wf(),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        final(ctn_mp).spec_index(ctn_ptr).view() == old(ctn_mp).spec_index(ctn_ptr).view(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == (ContainerGhost { owned_processes: final(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_processes,
            ..old(ctn_mp).spec_index(ctn_ptr).view_ghost() }),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_processes.view() == old(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_processes.view().insert(prc_ptr),
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).spec_index(ctn_ptr).inv(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(ctn_mp).view().spec_index(ptr).is_init()]
            old(ctn_mp).dom().contains(ptr) ==> {
                &&& final(ctn_mp).view().spec_index(ptr).is_init() == old(ctn_mp).view().spec_index(ptr).is_init()
                &&& final(ctn_mp).view().spec_index(ptr).addr() == old(ctn_mp).view().spec_index(ptr).addr()
            },
{
    assert(ctn_mp.perms_wf() && ctn_mp.spec_index(ctn_ptr).inv()) by { container_perms_wf_map(*ctn_mp); container_perms_wf_at(*ctn_mp, ctn_ptr); };
    let ghost pre_ghost = ctn_mp.spec_index(ctn_ptr).view_ghost();
    ctn_mp.update_ghost(ctn_ptr, ContainerGhost { owned_processes: Ghost(pre_ghost.owned_processes.view().insert(prc_ptr)), ..pre_ghost });
    assert(container_perms_wf(*ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

/// Removes `prc_ptr` from the ghost process set of `ctn_ptr`; nothing else changes.
pub proof fn container_map_remove_owned_process(tracked ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        container_perms_wf(*old(ctn_mp)),
        old(ctn_mp).dom().contains(ctn_ptr),
    ensures
        container_perms_wf(*final(ctn_mp)),
        final(ctn_mp).perms_wf(),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        final(ctn_mp).spec_index(ctn_ptr).view() == old(ctn_mp).spec_index(ctn_ptr).view(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == (ContainerGhost { owned_processes: final(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_processes,
            ..old(ctn_mp).spec_index(ctn_ptr).view_ghost() }),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_processes.view() == old(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_processes.view().remove(prc_ptr),
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).spec_index(ctn_ptr).inv(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(ctn_mp).view().spec_index(ptr).is_init()]
            old(ctn_mp).dom().contains(ptr) ==> {
                &&& final(ctn_mp).view().spec_index(ptr).is_init() == old(ctn_mp).view().spec_index(ptr).is_init()
                &&& final(ctn_mp).view().spec_index(ptr).addr() == old(ctn_mp).view().spec_index(ptr).addr()
            },
{
    assert(ctn_mp.perms_wf() && ctn_mp.spec_index(ctn_ptr).inv()) by { container_perms_wf_map(*ctn_mp); container_perms_wf_at(*ctn_mp, ctn_ptr); };
    let ghost pre_ghost = ctn_mp.spec_index(ctn_ptr).view_ghost();
    ctn_mp.update_ghost(ctn_ptr, ContainerGhost { owned_processes: Ghost(pre_ghost.owned_processes.view().remove(prc_ptr)), ..pre_ghost });
    assert(container_perms_wf(*ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

pub proof fn add_thread_to_container_sets(
    tracked ctn_mp: &mut ContainerLockedMap, direct_ctn_ptr: RwLockContainerPtr,
    t_ptr: RwLockThreadPtr, uppers: Seq<RwLockContainerPtr>, thrd_mp: ThreadLockedMap,
    sched_mp: SchedulerUnLockedMap, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(direct_ctn_ptr),
        uppers.to_set().subset_of(old(ctn_mp).dom()),
        uppers.no_duplicates(),
        !uppers.to_set().contains(direct_ctn_ptr),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        container_thread_scheduler_wf(*old(ctn_mp), thrd_mp, sched_mp),
        forall|t: RwLockThreadPtr| #![trigger thrd_mp.dom().contains(t)] thrd_mp.dom().contains(t) ==> old(ctn_mp).dom().contains(thrd_mp.spec_index(t).view().owning_container),
        forall|c: RwLockContainerPtr| #![trigger old(ctn_mp).dom().contains(c)] old(ctn_mp).dom().contains(c) ==> sched_mp.dom().contains(old(ctn_mp).spec_index(c).view_rodata().view().scheduler),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*final(ctn_mp)),
        final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        container_thread_scheduler_wf(*final(ctn_mp), thrd_mp, sched_mp),
        forall|t: RwLockThreadPtr| #![trigger thrd_mp.dom().contains(t)] thrd_mp.dom().contains(t) ==> final(ctn_mp).dom().contains(thrd_mp.spec_index(t).view().owning_container),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).dom().contains(c)] final(ctn_mp).dom().contains(c) ==> sched_mp.dom().contains(final(ctn_mp).spec_index(c).view_rodata().view().scheduler),
        forall|c: RwLockContainerPtr|
            #![trigger final(ctn_mp).spec_index(c)]
            old(ctn_mp).dom().contains(c) ==> {
                &&& final(ctn_mp).spec_index(c).view() == old(ctn_mp).spec_index(c).view()
                &&& final(ctn_mp).spec_index(c).view_rodata() == old(ctn_mp).spec_index(c).view_rodata()
                &&& final(ctn_mp).spec_index(c).locking_thread() == old(ctn_mp).spec_index(c).locking_thread()
                &&& final(ctn_mp).spec_index(c).control() == old(ctn_mp).spec_index(c).control()
                &&& final(ctn_mp).spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: old(ctn_mp).spec_index(c).view_ghost().uppertree_seq, subtree_set: old(ctn_mp).spec_index(c).view_ghost().subtree_set,
                    owned_processes: old(ctn_mp).spec_index(c).view_ghost().owned_processes,
                    owned_threads: if c == direct_ctn_ptr { Ghost(old(ctn_mp).spec_index(c).view_ghost().owned_threads.view().insert(t_ptr)) }
                        else { old(ctn_mp).spec_index(c).view_ghost().owned_threads },
                    owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads.view().insert(t_ptr)) }
                        else { old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads },
                    owned_endpoints: old(ctn_mp).spec_index(c).view_ghost().owned_endpoints, retire_ready: old(ctn_mp).spec_index(c).view_ghost().retire_ready,
                }
            },
    decreases uppers.len(),
{
    if uppers.len() > 0 {
        let c0 = uppers.spec_index(0);
        assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
        assert(uppers.drop_first().to_set().subset_of(ctn_mp.dom())) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        assert(!uppers.drop_first().to_set().contains(direct_ctn_ptr)) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        add_thread_to_container_sets(ctn_mp, direct_ctn_ptr, t_ptr, uppers.drop_first(), thrd_mp, sched_mp, held_locks, thread_id);
        ctn_mp.update_ghost(c0, ContainerGhost { uppertree_seq: ctn_mp.spec_index(c0).view_ghost().uppertree_seq, subtree_set: ctn_mp.spec_index(c0).view_ghost().subtree_set,
            owned_processes: ctn_mp.spec_index(c0).view_ghost().owned_processes, owned_threads: ctn_mp.spec_index(c0).view_ghost().owned_threads,
            owned_indirect_threads: Ghost(ctn_mp.spec_index(c0).view_ghost().owned_indirect_threads.view().insert(t_ptr)),
            owned_endpoints: ctn_mp.spec_index(c0).view_ghost().owned_endpoints, retire_ready: ctn_mp.spec_index(c0).view_ghost().retire_ready });
        assert(ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& !uppers.drop_first().to_set().contains(c0)
            &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    } else {
        ctn_mp.update_ghost(direct_ctn_ptr, ContainerGhost { uppertree_seq: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().uppertree_seq,
            subtree_set: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().subtree_set, owned_processes: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_processes,
            owned_threads: Ghost(ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_threads.view().insert(t_ptr)),
            owned_indirect_threads: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_indirect_threads,
            owned_endpoints: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_endpoints, retire_ready: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().retire_ready });
        assert(ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    assert(container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_thread_scheduler_wf(*ctn_mp, thrd_mp, sched_mp)) by { reveal(container_thread_scheduler_wf); };
}

/// Ghost removal of an exiting thread from its direct container and from every upper container.
pub proof fn remove_thread_from_container_sets(
    tracked ctn_mp: &mut ContainerLockedMap, direct_ctn_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr, uppers: Seq<RwLockContainerPtr>,
    held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(direct_ctn_ptr),
        uppers.to_set().subset_of(old(ctn_mp).dom()),
        uppers.no_duplicates(),
        !uppers.to_set().contains(direct_ctn_ptr),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*final(ctn_mp)),
        final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        forall|c: RwLockContainerPtr|
            #![trigger final(ctn_mp).spec_index(c)]
            old(ctn_mp).dom().contains(c) ==> {
                &&& final(ctn_mp).spec_index(c).view() == old(ctn_mp).spec_index(c).view()
                &&& final(ctn_mp).spec_index(c).is_init() == old(ctn_mp).spec_index(c).is_init()
                &&& final(ctn_mp).spec_index(c).view_rodata() == old(ctn_mp).spec_index(c).view_rodata()
                &&& final(ctn_mp).spec_index(c).locking_thread() == old(ctn_mp).spec_index(c).locking_thread()
                &&& final(ctn_mp).spec_index(c).control() == old(ctn_mp).spec_index(c).control()
                &&& final(ctn_mp).spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: old(ctn_mp).spec_index(c).view_ghost().uppertree_seq, subtree_set: old(ctn_mp).spec_index(c).view_ghost().subtree_set,
                    owned_processes: old(ctn_mp).spec_index(c).view_ghost().owned_processes,
                    owned_threads: if c == direct_ctn_ptr { Ghost(old(ctn_mp).spec_index(c).view_ghost().owned_threads.view().remove(t_ptr)) }
                        else { old(ctn_mp).spec_index(c).view_ghost().owned_threads },
                    owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads.view().remove(t_ptr)) }
                        else { old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads },
                    owned_endpoints: old(ctn_mp).spec_index(c).view_ghost().owned_endpoints, retire_ready: old(ctn_mp).spec_index(c).view_ghost().retire_ready,
                }
            },
    decreases uppers.len(),
{
    if uppers.len() > 0 {
        let c0 = uppers.spec_index(0);
        assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
        assert(uppers.drop_first().to_set().subset_of(ctn_mp.dom())) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        assert(!uppers.drop_first().to_set().contains(direct_ctn_ptr)) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        remove_thread_from_container_sets(ctn_mp, direct_ctn_ptr, t_ptr, uppers.drop_first(), held_locks, thread_id);
        ctn_mp.update_ghost(c0, ContainerGhost { uppertree_seq: ctn_mp.spec_index(c0).view_ghost().uppertree_seq, subtree_set: ctn_mp.spec_index(c0).view_ghost().subtree_set,
            owned_processes: ctn_mp.spec_index(c0).view_ghost().owned_processes, owned_threads: ctn_mp.spec_index(c0).view_ghost().owned_threads,
            owned_indirect_threads: Ghost(ctn_mp.spec_index(c0).view_ghost().owned_indirect_threads.view().remove(t_ptr)),
            owned_endpoints: ctn_mp.spec_index(c0).view_ghost().owned_endpoints, retire_ready: ctn_mp.spec_index(c0).view_ghost().retire_ready });
        assert(ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& !uppers.drop_first().to_set().contains(c0)
            &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    } else {
        ctn_mp.update_ghost(direct_ctn_ptr, ContainerGhost { uppertree_seq: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().uppertree_seq,
            subtree_set: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().subtree_set, owned_processes: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_processes,
            owned_threads: Ghost(ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_threads.view().remove(t_ptr)),
            owned_indirect_threads: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_indirect_threads,
            owned_endpoints: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().owned_endpoints, retire_ready: ctn_mp.spec_index(direct_ctn_ptr).view_ghost().retire_ready });
        assert(ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    assert(container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
}

pub fn container_map_insert_new_2m(
    ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, container_value: Container,
    container_rodata: ReadOnlyNode<ContainerRO>, container_ghost: ContainerGhost, Tracked(page_perm): Tracked<PagePerm2m>,
    Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(ctn_mp).perms_wf(),
        !old(ctn_mp).dom().contains(ctn_ptr),
        old(ctn_mp).typed_lock_map_aligned(old(lctx).container_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        container_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == ctn_ptr,
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() =~= old(ctn_mp).dom().insert(ctn_ptr),
        forall|ptr: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(ptr)] old(ctn_mp).dom().contains(ptr) ==> final(ctn_mp).spec_index(ptr) == old(ctn_mp).spec_index(ptr),
        final(ctn_mp).spec_index(ctn_ptr).view() == container_value,
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == container_rodata,
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == container_ghost,
        final(ctn_mp).spec_index(ctn_ptr).is_init(),
        final(ctn_mp).spec_index(ctn_ptr).inv(),
        final(ctn_mp).spec_index(ctn_ptr).control() == LockControl::DynamicProcess(LockOwnerId::Some(0)),
        final(ctn_mp).lock_id_by_key(ctn_ptr) == dynamic_container_lock_id(ctn_ptr, container_rodata.view().depth, LockOwnerId::Some(0)),
        final(ctn_mp).spec_index(ctn_ptr).wlocked_by(final(lctx)),
        final(ctn_mp).spec_index(ctn_ptr).write_lock_perm_match(&ret.view()),
        final(ctn_mp).typed_lock_map_aligned(final(lctx).container_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(ctn_ptr), TypedHeldLock { lock_id: final(ctn_mp).lock_id_by_key(ctn_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(ctn_mp).lock_id_by_key(ctn_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::Container(ctn_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = ctn_mp.retype_2m_and_insert(ctn_ptr, container_value, container_rodata, Ghost(container_ghost), Tracked(page_perm),
        Tracked(&mut *lctx), Ghost(KernelObjId::Container(ctn_ptr)), LockControl::DynamicProcess(LockOwnerId::Some(0)));
    proof { assert(ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    lock_perm
}

pub fn container_map_take_parent_node(ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<RwLockContainerPtr>>>))
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(ctn_ptr),
        old(ctn_mp).spec_index(ctn_ptr).inv(),
        old(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(ctn_mp).spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        old(ctn_mp).spec_index(ctn_ptr).view().parent_linkedlist_node.is_init(),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        final(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(ctn_mp).spec_index(ctn_ptr).inv(),
        final(ctn_mp).spec_index(ctn_ptr).view() == (Container { parent_linkedlist_node: final(ctn_mp).spec_index(ctn_ptr).view().parent_linkedlist_node, ..old(ctn_mp).spec_index(ctn_ptr).view() }),
        !final(ctn_mp).spec_index(ctn_ptr).view().parent_linkedlist_node.is_init(),
        final(ctn_mp).spec_index(ctn_ptr).view().parent_linkedlist_node.addr() == old(ctn_mp).spec_index(ctn_ptr).view().parent_linkedlist_node.addr(),
        final(ctn_mp).spec_index(ctn_ptr).view().parent_linkedlist_node.addr() == ret.0,
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == ctn_ptr,
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == old(ctn_mp).spec_index(ctn_ptr).view_ghost(),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).lock_id_by_key(ctn_ptr) == old(ctn_mp).lock_id_by_key(ctn_ptr),
{
    let container = ctn_mp.borrow_mut_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm));
    let (node_addr, mut node_perm) = container.parent_linkedlist_node.take();
    node_update_value(node_addr, &mut node_perm, ctn_ptr);
    proof {
        assert(ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
            && old(ctn_mp).view().spec_index(ctn_ptr).is_init()
            && ctn_mp.view().spec_index(ctn_ptr).is_init()) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    (node_addr, node_perm)
}

pub fn container_map_push_child(
    ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr,
    node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockContainerPtr>>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(ctn_ptr),
        old(ctn_mp).spec_index(ctn_ptr).inv(),
        old(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(ctn_mp).spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == child_ptr,
        !old(ctn_mp).spec_index(ctn_ptr).view().children.view().contains(child_ptr),
        old(ctn_mp).spec_index(ctn_ptr).view().children.length != usize::MAX,
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        final(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(ctn_mp).spec_index(ctn_ptr).inv(),
        final(ctn_mp).spec_index(ctn_ptr).view() == (Container { children: final(ctn_mp).spec_index(ctn_ptr).view().children, ..old(ctn_mp).spec_index(ctn_ptr).view() }),
        final(ctn_mp).spec_index(ctn_ptr).view().children.wf(),
        final(ctn_mp).spec_index(ctn_ptr).view().children.view() == old(ctn_mp).spec_index(ctn_ptr).view().children.view().push(child_ptr),
        final(ctn_mp).spec_index(ctn_ptr).view().children.map() == old(ctn_mp).spec_index(ctn_ptr).view().children.map().insert(node_addr, child_ptr),
        final(ctn_mp).spec_index(ctn_ptr).view().children.dom() == old(ctn_mp).spec_index(ctn_ptr).view().children.dom().insert(node_addr),
        final(ctn_mp).spec_index(ctn_ptr).view().children.length == old(ctn_mp).spec_index(ctn_ptr).view().children.length + 1,
        !old(ctn_mp).spec_index(ctn_ptr).view().children.dom().contains(node_addr),
        !old(ctn_mp).spec_index(ctn_ptr).view().children.map().dom().contains(node_addr),
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == old(ctn_mp).spec_index(ctn_ptr).view_ghost(),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).lock_id_by_key(ctn_ptr) == old(ctn_mp).lock_id_by_key(ctn_ptr),
{
    let container = ctn_mp.borrow_mut_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm));
    container.children.push_tail(node_addr, node_perm);
    proof {
        assert(ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
            && old(ctn_mp).view().spec_index(ctn_ptr).is_init()
            && ctn_mp.view().spec_index(ctn_ptr).is_init()) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

/// Unlinks the retired leaf `child_ptr` from its write-held parent's child list and every ancestor's subtree set,
/// returning the child's list node.
pub fn container_map_unlink_child(
    ctn_mp: &mut ContainerLockedMap, parent_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr, Ghost(ancestors): Ghost<Seq<RwLockContainerPtr>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(child_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PointsTo<Node<RwLockContainerPtr>>>)
    requires
        container_perms_wf(*old(ctn_mp)),
        old(ctn_mp).dom().contains(parent_ptr),
        old(ctn_mp).dom().contains(child_ptr),
        parent_ptr != child_ptr,
        old(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), parent_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), child_ptr, TypedLockMode::Write),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == lctx.thread_id(),
        parent_lock_perm.lock_id() == old(ctn_mp).spec_index(parent_ptr).locking_thread()->Write_lock_id,
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == lctx.thread_id(),
        child_lock_perm.lock_id() == old(ctn_mp).spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(ctn_mp).spec_index(parent_ptr).view().children.map().dom().contains(old(ctn_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        old(ctn_mp).spec_index(parent_ptr).view().children.map().spec_index(old(ctn_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr,
        ancestors == old(ctn_mp).spec_index(child_ptr).view_ghost().uppertree_seq.view(),
        ancestors.to_set().subset_of(old(ctn_mp).dom()),
        ancestors.no_duplicates(),
    ensures
        container_perms_wf(*final(ctn_mp)),
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        final(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(ctn_mp).spec_index(parent_ptr).view() == (Container { children: final(ctn_mp).spec_index(parent_ptr).view().children, ..old(ctn_mp).spec_index(parent_ptr).view() }),
        final(ctn_mp).spec_index(parent_ptr).view().children.view() == old(ctn_mp).spec_index(parent_ptr).view().children.view().remove_value(child_ptr),
        final(ctn_mp).spec_index(parent_ptr).view().children.dom() == old(ctn_mp).spec_index(parent_ptr).view().children.dom().remove(old(ctn_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        final(ctn_mp).spec_index(parent_ptr).view().children.map() == old(ctn_mp).spec_index(parent_ptr).view().children.map().remove(old(ctn_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c)]
            old(ctn_mp).dom().contains(c) ==> {
                &&& final(ctn_mp).spec_index(c).is_init() == old(ctn_mp).spec_index(c).is_init()
                &&& final(ctn_mp).spec_index(c).view_rodata() == old(ctn_mp).spec_index(c).view_rodata()
                &&& final(ctn_mp).spec_index(c).view_ghost().uppertree_seq == old(ctn_mp).spec_index(c).view_ghost().uppertree_seq
                &&& final(ctn_mp).spec_index(c).view_ghost().owned_processes == old(ctn_mp).spec_index(c).view_ghost().owned_processes
                &&& final(ctn_mp).spec_index(c).view_ghost().owned_threads == old(ctn_mp).spec_index(c).view_ghost().owned_threads
                &&& final(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads == old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads
                &&& final(ctn_mp).spec_index(c).view_ghost().owned_endpoints == old(ctn_mp).spec_index(c).view_ghost().owned_endpoints
                &&& final(ctn_mp).spec_index(c).view_ghost().retire_ready == old(ctn_mp).spec_index(c).view_ghost().retire_ready
                &&& final(ctn_mp).spec_index(c).locking_thread() == old(ctn_mp).spec_index(c).locking_thread()
                &&& final(ctn_mp).spec_index(c).control() == old(ctn_mp).spec_index(c).control()
                &&& c != parent_ptr ==> final(ctn_mp).spec_index(c).view() == old(ctn_mp).spec_index(c).view()
            },
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().subtree_set]
            old(ctn_mp).dom().contains(c) ==> {
                &&& ancestors.to_set().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().subtree_set.view() == old(ctn_mp).spec_index(c).view_ghost().subtree_set.view().remove(child_ptr)
                &&& !ancestors.to_set().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().subtree_set == old(ctn_mp).spec_index(c).view_ghost().subtree_set
            },
        ret.view().is_init(),
        ret.view().addr() == old(ctn_mp).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        ret.view().value().view() == child_ptr,
{
    assert(ctn_mp.perms_wf() && ctn_mp.spec_index(child_ptr).is_init() && ctn_mp.spec_index(parent_ptr).inv()) by {
        container_perms_wf_map(*ctn_mp); container_perms_wf_at(*ctn_mp, child_ptr); container_perms_wf_at(*ctn_mp, parent_ptr);
    };
    let node_addr = ctn_mp.borrow_typed(child_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(child_lock_perm)).parent_linkedlist_node.addr();
    assert(ctn_mp.spec_index(parent_ptr).view().children.dom().contains(node_addr)) by { ctn_mp.spec_index(parent_ptr).view().children.wf_map_at(node_addr); };
    let parent = ctn_mp.borrow_mut_typed(parent_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(parent_lock_perm));
    let (_, node_perm) = parent.children.remove(node_addr);
    proof {
        assert(ctn_mp.spec_index(parent_ptr).view().children.view().no_duplicates()) by { reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
        assert(ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        container_remove_child_from_ancestor_subtree_sets(ctn_mp, ancestors, child_ptr, lctx.container_lock_map(), lctx.thread_id());
        container_map_unlink_child_eof_container_perms_wf(*old(ctn_mp), *ctn_mp, parent_ptr, child_ptr);
    }
    node_perm
}

pub fn container_map_remove_owned_pages(ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, Ghost(pages): Ghost<Set<PagePtr>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>)
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(ctn_ptr),
        old(ctn_mp).spec_index(ctn_ptr).inv(),
        old(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(ctn_mp).spec_index(ctn_ptr).locking_thread()->Write_lock_id,
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        final(ctn_mp).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(ctn_mp).spec_index(ctn_ptr).inv(),
        final(ctn_mp).spec_index(ctn_ptr).view() == (Container { owned_pages: Ghost(old(ctn_mp).spec_index(ctn_ptr).view().owned_pages.view().difference(pages)),
            ..old(ctn_mp).spec_index(ctn_ptr).view() }),
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == old(ctn_mp).spec_index(ctn_ptr).view_ghost(),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).lock_id_by_key(ctn_ptr) == old(ctn_mp).lock_id_by_key(ctn_ptr),
{
    let container = ctn_mp.borrow_mut_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm));
    container.owned_pages = Ghost(container.owned_pages.view().difference(pages));
    proof {
        assert(ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
            && old(ctn_mp).view().spec_index(ctn_ptr).is_init()
            && ctn_mp.view().spec_index(ctn_ptr).is_init()) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

/// Ghost insertion of `ep_ptr` into the endpoint set of `ctn_ptr`; nothing else changes.
pub proof fn insert_endpoint_into_container_set(
    tracked ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, ep_ptr: RwLockEndpointPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(ctn_ptr),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*final(ctn_mp)),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).spec_index(ctn_ptr).view() == old(ctn_mp).spec_index(ctn_ptr).view(),
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == (ContainerGhost {
            owned_endpoints: Ghost(old(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_endpoints.view().insert(ep_ptr)), ..old(ctn_mp).spec_index(ctn_ptr).view_ghost()
        }),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).lock_id_by_key(ctn_ptr) == old(ctn_mp).lock_id_by_key(ctn_ptr),
{
    let ghost pre_ghost = ctn_mp.spec_index(ctn_ptr).view_ghost();
    ctn_mp.update_ghost(ctn_ptr, ContainerGhost { owned_endpoints: Ghost(pre_ghost.owned_endpoints.view().insert(ep_ptr)), ..pre_ghost });
    assert(container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

/// Ghost removal of `ep_ptr` from the endpoint set of `ctn_ptr`; nothing else changes.
pub proof fn remove_endpoint_from_container_set(
    tracked ctn_mp: &mut ContainerLockedMap, ctn_ptr: RwLockContainerPtr, ep_ptr: RwLockEndpointPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        old(ctn_mp).perms_wf(),
        old(ctn_mp).dom().contains(ctn_ptr),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*final(ctn_mp)),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        final(ctn_mp).unchanged_except(old(ctn_mp), ctn_ptr),
        final(ctn_mp).spec_index(ctn_ptr).view() == old(ctn_mp).spec_index(ctn_ptr).view(),
        final(ctn_mp).spec_index(ctn_ptr).view_rodata() == old(ctn_mp).spec_index(ctn_ptr).view_rodata(),
        final(ctn_mp).spec_index(ctn_ptr).view_ghost() == (ContainerGhost {
            owned_endpoints: Ghost(old(ctn_mp).spec_index(ctn_ptr).view_ghost().owned_endpoints.view().remove(ep_ptr)), ..old(ctn_mp).spec_index(ctn_ptr).view_ghost()
        }),
        final(ctn_mp).spec_index(ctn_ptr).locking_thread() == old(ctn_mp).spec_index(ctn_ptr).locking_thread(),
        final(ctn_mp).spec_index(ctn_ptr).control() == old(ctn_mp).spec_index(ctn_ptr).control(),
        final(ctn_mp).lock_id_by_key(ctn_ptr) == old(ctn_mp).lock_id_by_key(ctn_ptr),
{
    let ghost pre_ghost = ctn_mp.spec_index(ctn_ptr).view_ghost();
    ctn_mp.update_ghost(ctn_ptr, ContainerGhost { owned_endpoints: Ghost(pre_ghost.owned_endpoints.view().remove(ep_ptr)), ..pre_ghost });
    assert(container_perms_wf(*old(ctn_mp)) ==> container_perms_wf(*ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id) ==> ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}
}

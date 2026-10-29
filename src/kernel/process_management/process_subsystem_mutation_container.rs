use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;
use crate::*;
use super::process_subsystem_mutation_eof::*;

verus! {
pub proof fn container_map_add_owned_process(tracked container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        container_perms_wf(*old(container_map)),
        old(container_map).dom().contains(container_ptr),
    ensures
        container_perms_wf(*final(container_map)),
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        final(container_map).spec_index(container_ptr).view() == old(container_map).spec_index(container_ptr).view(),
        final(container_map).spec_index(container_ptr).view_ghost() == (ContainerGhost { owned_processes: final(container_map).spec_index(container_ptr).view_ghost().owned_processes,
            ..old(container_map).spec_index(container_ptr).view_ghost() }),
        final(container_map).spec_index(container_ptr).view_ghost().owned_processes.view() == old(container_map).spec_index(container_ptr).view_ghost().owned_processes.view().insert(process_ptr),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).spec_index(container_ptr).inv(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(container_map).view().spec_index(ptr).is_init()]
            old(container_map).dom().contains(ptr) ==> {
                &&& final(container_map).view().spec_index(ptr).is_init() == old(container_map).view().spec_index(ptr).is_init()
                &&& final(container_map).view().spec_index(ptr).addr() == old(container_map).view().spec_index(ptr).addr()
            },
{
    assert(container_map.perms_wf() && container_map.spec_index(container_ptr).inv()) by { container_perms_wf_map(*container_map); container_perms_wf_at(*container_map, container_ptr); };
    let ghost pre_ghost = container_map.spec_index(container_ptr).view_ghost();
    container_map.update_ghost(container_ptr, ContainerGhost { owned_processes: Ghost(pre_ghost.owned_processes.view().insert(process_ptr)), ..pre_ghost });
    assert(container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

/// Removes `process_ptr` from the ghost process set of `container_ptr`; nothing else changes.
pub proof fn container_map_remove_owned_process(tracked container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        container_perms_wf(*old(container_map)),
        old(container_map).dom().contains(container_ptr),
    ensures
        container_perms_wf(*final(container_map)),
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        final(container_map).spec_index(container_ptr).view() == old(container_map).spec_index(container_ptr).view(),
        final(container_map).spec_index(container_ptr).view_ghost() == (ContainerGhost { owned_processes: final(container_map).spec_index(container_ptr).view_ghost().owned_processes,
            ..old(container_map).spec_index(container_ptr).view_ghost() }),
        final(container_map).spec_index(container_ptr).view_ghost().owned_processes.view() == old(container_map).spec_index(container_ptr).view_ghost().owned_processes.view().remove(process_ptr),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).spec_index(container_ptr).inv(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(container_map).view().spec_index(ptr).is_init()]
            old(container_map).dom().contains(ptr) ==> {
                &&& final(container_map).view().spec_index(ptr).is_init() == old(container_map).view().spec_index(ptr).is_init()
                &&& final(container_map).view().spec_index(ptr).addr() == old(container_map).view().spec_index(ptr).addr()
            },
{
    assert(container_map.perms_wf() && container_map.spec_index(container_ptr).inv()) by { container_perms_wf_map(*container_map); container_perms_wf_at(*container_map, container_ptr); };
    let ghost pre_ghost = container_map.spec_index(container_ptr).view_ghost();
    container_map.update_ghost(container_ptr, ContainerGhost { owned_processes: Ghost(pre_ghost.owned_processes.view().remove(process_ptr)), ..pre_ghost });
    assert(container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

pub proof fn add_thread_to_container_sets(
    tracked container_map: &mut ContainerLockedMap, direct_container_ptr: RwLockContainerPtr,
    t_ptr: RwLockThreadPtr, uppers: Seq<RwLockContainerPtr>, thread_map: ThreadLockedMap,
    scheduler_map: SchedulerUnLockedMap, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(direct_container_ptr),
        uppers.to_set().subset_of(old(container_map).dom()),
        uppers.no_duplicates(),
        !uppers.to_set().contains(direct_container_ptr),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id),
        container_thread_scheduler_wf(*old(container_map), thread_map, scheduler_map),
        forall|t: RwLockThreadPtr| #![trigger thread_map.dom().contains(t)] thread_map.dom().contains(t) ==> old(container_map).dom().contains(thread_map.spec_index(t).view().owning_container),
        forall|c: RwLockContainerPtr| #![trigger old(container_map).dom().contains(c)] old(container_map).dom().contains(c) ==> scheduler_map.dom().contains(old(container_map).spec_index(c).view_rodata().view().scheduler),
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        container_perms_wf(*old(container_map)) ==> container_perms_wf(*final(container_map)),
        final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        container_thread_scheduler_wf(*final(container_map), thread_map, scheduler_map),
        forall|t: RwLockThreadPtr| #![trigger thread_map.dom().contains(t)] thread_map.dom().contains(t) ==> final(container_map).dom().contains(thread_map.spec_index(t).view().owning_container),
        forall|c: RwLockContainerPtr| #![trigger final(container_map).dom().contains(c)] final(container_map).dom().contains(c) ==> scheduler_map.dom().contains(final(container_map).spec_index(c).view_rodata().view().scheduler),
        forall|c: RwLockContainerPtr|
            #![trigger final(container_map).spec_index(c)]
            old(container_map).dom().contains(c) ==> {
                &&& final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                &&& final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                &&& final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                &&& final(container_map).spec_index(c).control() == old(container_map).spec_index(c).control()
                &&& final(container_map).spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: old(container_map).spec_index(c).view_ghost().uppertree_seq, subtree_set: old(container_map).spec_index(c).view_ghost().subtree_set,
                    owned_processes: old(container_map).spec_index(c).view_ghost().owned_processes,
                    owned_threads: if c == direct_container_ptr { Ghost(old(container_map).spec_index(c).view_ghost().owned_threads.view().insert(t_ptr)) }
                        else { old(container_map).spec_index(c).view_ghost().owned_threads },
                    owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(old(container_map).spec_index(c).view_ghost().owned_indirect_threads.view().insert(t_ptr)) }
                        else { old(container_map).spec_index(c).view_ghost().owned_indirect_threads },
                    owned_endpoints: old(container_map).spec_index(c).view_ghost().owned_endpoints, retire_ready: old(container_map).spec_index(c).view_ghost().retire_ready,
                }
            },
    decreases uppers.len(),
{
    if uppers.len() > 0 {
        let c0 = uppers.spec_index(0);
        assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
        assert(uppers.drop_first().to_set().subset_of(container_map.dom())) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        assert(!uppers.drop_first().to_set().contains(direct_container_ptr)) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        add_thread_to_container_sets(container_map, direct_container_ptr, t_ptr, uppers.drop_first(), thread_map, scheduler_map, held_locks, thread_id);
        container_map.update_ghost(c0, ContainerGhost { uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq, subtree_set: container_map.spec_index(c0).view_ghost().subtree_set,
            owned_processes: container_map.spec_index(c0).view_ghost().owned_processes, owned_threads: container_map.spec_index(c0).view_ghost().owned_threads,
            owned_indirect_threads: Ghost(container_map.spec_index(c0).view_ghost().owned_indirect_threads.view().insert(t_ptr)),
            owned_endpoints: container_map.spec_index(c0).view_ghost().owned_endpoints, retire_ready: container_map.spec_index(c0).view_ghost().retire_ready });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& !uppers.drop_first().to_set().contains(c0)
            &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    } else {
        container_map.update_ghost(direct_container_ptr, ContainerGhost { uppertree_seq: container_map.spec_index(direct_container_ptr).view_ghost().uppertree_seq,
            subtree_set: container_map.spec_index(direct_container_ptr).view_ghost().subtree_set, owned_processes: container_map.spec_index(direct_container_ptr).view_ghost().owned_processes,
            owned_threads: Ghost(container_map.spec_index(direct_container_ptr).view_ghost().owned_threads.view().insert(t_ptr)),
            owned_indirect_threads: container_map.spec_index(direct_container_ptr).view_ghost().owned_indirect_threads,
            owned_endpoints: container_map.spec_index(direct_container_ptr).view_ghost().owned_endpoints, retire_ready: container_map.spec_index(direct_container_ptr).view_ghost().retire_ready });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    assert(container_perms_wf(*old(container_map)) ==> container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_thread_scheduler_wf(*container_map, thread_map, scheduler_map)) by { reveal(container_thread_scheduler_wf); };
}

/// Ghost removal of an exiting thread from its direct container and from every upper container.
pub proof fn remove_thread_from_container_sets(
    tracked container_map: &mut ContainerLockedMap, direct_container_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr, uppers: Seq<RwLockContainerPtr>,
    held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(direct_container_ptr),
        uppers.to_set().subset_of(old(container_map).dom()),
        uppers.no_duplicates(),
        !uppers.to_set().contains(direct_container_ptr),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        container_perms_wf(*old(container_map)) ==> container_perms_wf(*final(container_map)),
        final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        forall|c: RwLockContainerPtr|
            #![trigger final(container_map).spec_index(c)]
            old(container_map).dom().contains(c) ==> {
                &&& final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                &&& final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                &&& final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                &&& final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                &&& final(container_map).spec_index(c).control() == old(container_map).spec_index(c).control()
                &&& final(container_map).spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: old(container_map).spec_index(c).view_ghost().uppertree_seq, subtree_set: old(container_map).spec_index(c).view_ghost().subtree_set,
                    owned_processes: old(container_map).spec_index(c).view_ghost().owned_processes,
                    owned_threads: if c == direct_container_ptr { Ghost(old(container_map).spec_index(c).view_ghost().owned_threads.view().remove(t_ptr)) }
                        else { old(container_map).spec_index(c).view_ghost().owned_threads },
                    owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(old(container_map).spec_index(c).view_ghost().owned_indirect_threads.view().remove(t_ptr)) }
                        else { old(container_map).spec_index(c).view_ghost().owned_indirect_threads },
                    owned_endpoints: old(container_map).spec_index(c).view_ghost().owned_endpoints, retire_ready: old(container_map).spec_index(c).view_ghost().retire_ready,
                }
            },
    decreases uppers.len(),
{
    if uppers.len() > 0 {
        let c0 = uppers.spec_index(0);
        assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
        assert(uppers.drop_first().to_set().subset_of(container_map.dom())) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        assert(!uppers.drop_first().to_set().contains(direct_container_ptr)) by { uppers.to_set_ensures(); uppers.drop_first().to_set_ensures(); broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        remove_thread_from_container_sets(container_map, direct_container_ptr, t_ptr, uppers.drop_first(), held_locks, thread_id);
        container_map.update_ghost(c0, ContainerGhost { uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq, subtree_set: container_map.spec_index(c0).view_ghost().subtree_set,
            owned_processes: container_map.spec_index(c0).view_ghost().owned_processes, owned_threads: container_map.spec_index(c0).view_ghost().owned_threads,
            owned_indirect_threads: Ghost(container_map.spec_index(c0).view_ghost().owned_indirect_threads.view().remove(t_ptr)),
            owned_endpoints: container_map.spec_index(c0).view_ghost().owned_endpoints, retire_ready: container_map.spec_index(c0).view_ghost().retire_ready });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& !uppers.drop_first().to_set().contains(c0)
            &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    } else {
        container_map.update_ghost(direct_container_ptr, ContainerGhost { uppertree_seq: container_map.spec_index(direct_container_ptr).view_ghost().uppertree_seq,
            subtree_set: container_map.spec_index(direct_container_ptr).view_ghost().subtree_set, owned_processes: container_map.spec_index(direct_container_ptr).view_ghost().owned_processes,
            owned_threads: Ghost(container_map.spec_index(direct_container_ptr).view_ghost().owned_threads.view().remove(t_ptr)),
            owned_indirect_threads: container_map.spec_index(direct_container_ptr).view_ghost().owned_indirect_threads,
            owned_endpoints: container_map.spec_index(direct_container_ptr).view_ghost().owned_endpoints, retire_ready: container_map.spec_index(direct_container_ptr).view_ghost().retire_ready });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    assert(container_perms_wf(*old(container_map)) ==> container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
}

pub fn container_map_insert_new_2m(
    container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, container_value: Container,
    container_rodata: ReadOnlyNode<ContainerRO>, container_ghost: ContainerGhost, Tracked(page_perm): Tracked<PagePerm2m>,
    Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(container_map).perms_wf(),
        !old(container_map).dom().contains(container_ptr),
        old(container_map).typed_lock_map_aligned(old(lctx).container_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        container_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == container_ptr,
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() =~= old(container_map).dom().insert(container_ptr),
        forall|ptr: RwLockContainerPtr| #![trigger final(container_map).spec_index(ptr)] old(container_map).dom().contains(ptr) ==> final(container_map).spec_index(ptr) == old(container_map).spec_index(ptr),
        final(container_map).spec_index(container_ptr).view() == container_value,
        final(container_map).spec_index(container_ptr).view_rodata() == container_rodata,
        final(container_map).spec_index(container_ptr).view_ghost() == container_ghost,
        final(container_map).spec_index(container_ptr).is_init(),
        final(container_map).spec_index(container_ptr).inv(),
        final(container_map).spec_index(container_ptr).control() == LockControl::DynamicProcess(LockOwnerId::Some(0)),
        final(container_map).lock_id_by_key(container_ptr) == dynamic_container_lock_id(container_ptr, container_rodata.view().depth, LockOwnerId::Some(0)),
        final(container_map).spec_index(container_ptr).wlocked_by(final(lctx)),
        final(container_map).spec_index(container_ptr).write_lock_perm_match(&ret.view()),
        final(container_map).typed_lock_map_aligned(final(lctx).container_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(container_ptr), TypedHeldLock { lock_id: final(container_map).lock_id_by_key(container_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(container_map).lock_id_by_key(container_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::Container(container_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = container_map.retype_2m_and_insert(container_ptr, container_value, container_rodata, Ghost(container_ghost), Tracked(page_perm),
        Tracked(&mut *lctx), Ghost(KernelObjId::Container(container_ptr)), LockControl::DynamicProcess(LockOwnerId::Some(0)));
    proof { assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    lock_perm
}

pub fn container_map_take_parent_node(container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<RwLockContainerPtr>>>))
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(container_ptr),
        old(container_map).spec_index(container_ptr).inv(),
        old(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(container_map).spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(container_map).spec_index(container_ptr).view().parent_linkedlist_node.is_init(),
    ensures
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        final(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(container_map).spec_index(container_ptr).inv(),
        final(container_map).spec_index(container_ptr).view() == (Container { parent_linkedlist_node: final(container_map).spec_index(container_ptr).view().parent_linkedlist_node, ..old(container_map).spec_index(container_ptr).view() }),
        !final(container_map).spec_index(container_ptr).view().parent_linkedlist_node.is_init(),
        final(container_map).spec_index(container_ptr).view().parent_linkedlist_node.addr() == old(container_map).spec_index(container_ptr).view().parent_linkedlist_node.addr(),
        final(container_map).spec_index(container_ptr).view().parent_linkedlist_node.addr() == ret.0,
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == container_ptr,
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == old(container_map).spec_index(container_ptr).view_ghost(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).lock_id_by_key(container_ptr) == old(container_map).lock_id_by_key(container_ptr),
{
    let container = container_map.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm));
    let (node_addr, mut node_perm) = container.parent_linkedlist_node.take();
    node_update_value(node_addr, &mut node_perm, container_ptr);
    proof {
        assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
            && old(container_map).view().spec_index(container_ptr).is_init()
            && container_map.view().spec_index(container_ptr).is_init()) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    (node_addr, node_perm)
}

pub fn container_map_push_child(
    container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr,
    node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockContainerPtr>>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(container_ptr),
        old(container_map).spec_index(container_ptr).inv(),
        old(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(container_map).spec_index(container_ptr).locking_thread()->Write_lock_id,
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == child_ptr,
        !old(container_map).spec_index(container_ptr).view().children.view().contains(child_ptr),
        old(container_map).spec_index(container_ptr).view().children.length != usize::MAX,
    ensures
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        final(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(container_map).spec_index(container_ptr).inv(),
        final(container_map).spec_index(container_ptr).view() == (Container { children: final(container_map).spec_index(container_ptr).view().children, ..old(container_map).spec_index(container_ptr).view() }),
        final(container_map).spec_index(container_ptr).view().children.wf(),
        final(container_map).spec_index(container_ptr).view().children.view() == old(container_map).spec_index(container_ptr).view().children.view().push(child_ptr),
        final(container_map).spec_index(container_ptr).view().children.map() == old(container_map).spec_index(container_ptr).view().children.map().insert(node_addr, child_ptr),
        final(container_map).spec_index(container_ptr).view().children.dom() == old(container_map).spec_index(container_ptr).view().children.dom().insert(node_addr),
        final(container_map).spec_index(container_ptr).view().children.length == old(container_map).spec_index(container_ptr).view().children.length + 1,
        !old(container_map).spec_index(container_ptr).view().children.dom().contains(node_addr),
        !old(container_map).spec_index(container_ptr).view().children.map().dom().contains(node_addr),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == old(container_map).spec_index(container_ptr).view_ghost(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).lock_id_by_key(container_ptr) == old(container_map).lock_id_by_key(container_ptr),
{
    let container = container_map.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm));
    container.children.push_tail(node_addr, node_perm);
    proof {
        assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
            && old(container_map).view().spec_index(container_ptr).is_init()
            && container_map.view().spec_index(container_ptr).is_init()) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

/// Unlinks the retired leaf `child_ptr` from its write-held parent's child list and every ancestor's subtree set,
/// returning the child's list node.
pub fn container_map_unlink_child(
    container_map: &mut ContainerLockedMap, parent_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr, Ghost(ancestors): Ghost<Seq<RwLockContainerPtr>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(child_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PointsTo<Node<RwLockContainerPtr>>>)
    requires
        container_perms_wf(*old(container_map)),
        old(container_map).dom().contains(parent_ptr),
        old(container_map).dom().contains(child_ptr),
        parent_ptr != child_ptr,
        old(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), parent_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), child_ptr, TypedLockMode::Write),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == lctx.thread_id(),
        parent_lock_perm.lock_id() == old(container_map).spec_index(parent_ptr).locking_thread()->Write_lock_id,
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == lctx.thread_id(),
        child_lock_perm.lock_id() == old(container_map).spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(container_map).spec_index(parent_ptr).view().children.map().dom().contains(old(container_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        old(container_map).spec_index(parent_ptr).view().children.map().spec_index(old(container_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr,
        ancestors == old(container_map).spec_index(child_ptr).view_ghost().uppertree_seq.view(),
        ancestors.to_set().subset_of(old(container_map).dom()),
        ancestors.no_duplicates(),
    ensures
        container_perms_wf(*final(container_map)),
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        final(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(container_map).spec_index(parent_ptr).view() == (Container { children: final(container_map).spec_index(parent_ptr).view().children, ..old(container_map).spec_index(parent_ptr).view() }),
        final(container_map).spec_index(parent_ptr).view().children.view() == old(container_map).spec_index(parent_ptr).view().children.view().remove_value(child_ptr),
        final(container_map).spec_index(parent_ptr).view().children.dom() == old(container_map).spec_index(parent_ptr).view().children.dom().remove(old(container_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        final(container_map).spec_index(parent_ptr).view().children.map() == old(container_map).spec_index(parent_ptr).view().children.map().remove(old(container_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c)]
            old(container_map).dom().contains(c) ==> {
                &&& final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                &&& final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                &&& final(container_map).spec_index(c).view_ghost().uppertree_seq == old(container_map).spec_index(c).view_ghost().uppertree_seq
                &&& final(container_map).spec_index(c).view_ghost().owned_processes == old(container_map).spec_index(c).view_ghost().owned_processes
                &&& final(container_map).spec_index(c).view_ghost().owned_threads == old(container_map).spec_index(c).view_ghost().owned_threads
                &&& final(container_map).spec_index(c).view_ghost().owned_indirect_threads == old(container_map).spec_index(c).view_ghost().owned_indirect_threads
                &&& final(container_map).spec_index(c).view_ghost().owned_endpoints == old(container_map).spec_index(c).view_ghost().owned_endpoints
                &&& final(container_map).spec_index(c).view_ghost().retire_ready == old(container_map).spec_index(c).view_ghost().retire_ready
                &&& final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                &&& final(container_map).spec_index(c).control() == old(container_map).spec_index(c).control()
                &&& c != parent_ptr ==> final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
            },
        forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().subtree_set]
            old(container_map).dom().contains(c) ==> {
                &&& ancestors.to_set().contains(c) ==> final(container_map).spec_index(c).view_ghost().subtree_set.view() == old(container_map).spec_index(c).view_ghost().subtree_set.view().remove(child_ptr)
                &&& !ancestors.to_set().contains(c) ==> final(container_map).spec_index(c).view_ghost().subtree_set == old(container_map).spec_index(c).view_ghost().subtree_set
            },
        ret.view().is_init(),
        ret.view().addr() == old(container_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        ret.view().value().view() == child_ptr,
{
    assert(container_map.perms_wf() && container_map.spec_index(child_ptr).is_init() && container_map.spec_index(parent_ptr).inv()) by {
        container_perms_wf_map(*container_map); container_perms_wf_at(*container_map, child_ptr); container_perms_wf_at(*container_map, parent_ptr);
    };
    let node_addr = container_map.borrow_typed(child_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(child_lock_perm)).parent_linkedlist_node.addr();
    assert(container_map.spec_index(parent_ptr).view().children.dom().contains(node_addr)) by { container_map.spec_index(parent_ptr).view().children.wf_map_at(node_addr); };
    let parent = container_map.borrow_mut_typed(parent_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(parent_lock_perm));
    let (_, node_perm) = parent.children.remove(node_addr);
    proof {
        assert(container_map.spec_index(parent_ptr).view().children.view().no_duplicates()) by { reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
        assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        container_remove_child_from_ancestor_subtree_sets(container_map, ancestors, child_ptr, lctx.container_lock_map(), lctx.thread_id());
        container_map_unlink_child_eof_container_perms_wf(*old(container_map), *container_map, parent_ptr, child_ptr);
    }
    node_perm
}

pub fn container_map_remove_owned_pages(container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, Ghost(pages): Ghost<Set<PagePtr>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(container_ptr),
        old(container_map).spec_index(container_ptr).inv(),
        old(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(container_map).spec_index(container_ptr).locking_thread()->Write_lock_id,
    ensures
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        final(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(container_map).spec_index(container_ptr).inv(),
        final(container_map).spec_index(container_ptr).view() == (Container { owned_pages: Ghost(old(container_map).spec_index(container_ptr).view().owned_pages.view().difference(pages)),
            ..old(container_map).spec_index(container_ptr).view() }),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == old(container_map).spec_index(container_ptr).view_ghost(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).lock_id_by_key(container_ptr) == old(container_map).lock_id_by_key(container_ptr),
{
    let container = container_map.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm));
    container.owned_pages = Ghost(container.owned_pages.view().difference(pages));
    proof {
        assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
            && old(container_map).view().spec_index(container_ptr).is_init()
            && container_map.view().spec_index(container_ptr).is_init()) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

/// Ghost insertion of `endpoint_ptr` into the endpoint set of `container_ptr`; nothing else changes.
pub proof fn insert_endpoint_into_container_set(
    tracked container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, endpoint_ptr: RwLockEndpointPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(container_ptr),
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        container_perms_wf(*old(container_map)) ==> container_perms_wf(*final(container_map)),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).spec_index(container_ptr).view() == old(container_map).spec_index(container_ptr).view(),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_endpoints: Ghost(old(container_map).spec_index(container_ptr).view_ghost().owned_endpoints.view().insert(endpoint_ptr)), ..old(container_map).spec_index(container_ptr).view_ghost()
        }),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).lock_id_by_key(container_ptr) == old(container_map).lock_id_by_key(container_ptr),
{
    let ghost pre_ghost = container_map.spec_index(container_ptr).view_ghost();
    container_map.update_ghost(container_ptr, ContainerGhost { owned_endpoints: Ghost(pre_ghost.owned_endpoints.view().insert(endpoint_ptr)), ..pre_ghost });
    assert(container_perms_wf(*old(container_map)) ==> container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

/// Ghost removal of `endpoint_ptr` from the endpoint set of `container_ptr`; nothing else changes.
pub proof fn remove_endpoint_from_container_set(
    tracked container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, endpoint_ptr: RwLockEndpointPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(container_ptr),
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        container_perms_wf(*old(container_map)) ==> container_perms_wf(*final(container_map)),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).spec_index(container_ptr).view() == old(container_map).spec_index(container_ptr).view(),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_endpoints: Ghost(old(container_map).spec_index(container_ptr).view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..old(container_map).spec_index(container_ptr).view_ghost()
        }),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).control() == old(container_map).spec_index(container_ptr).control(),
        final(container_map).lock_id_by_key(container_ptr) == old(container_map).lock_id_by_key(container_ptr),
{
    let ghost pre_ghost = container_map.spec_index(container_ptr).view_ghost();
    container_map.update_ghost(container_ptr, ContainerGhost { owned_endpoints: Ghost(pre_ghost.owned_endpoints.view().remove(endpoint_ptr)), ..pre_ghost });
    assert(container_perms_wf(*old(container_map)) ==> container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(old(container_map).typed_lock_map_aligned(held_locks, thread_id) ==> container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}
}

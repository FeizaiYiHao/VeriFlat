use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;
use crate::*;

verus! {
pub fn thread_map_consume_staged_4k(
    thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, page_ptr: PagePtr,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        old(thread_map).spec_index(thread_ptr).view().quota_4k >= 1,
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).perms_wf(),
        final(thread_map).spec_index(thread_ptr).inv(),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).dom() == old(thread_map).dom(),
        forall|ptr: RwLockThreadPtr|
            #![trigger final(thread_map).spec_index(ptr)]
            old(thread_map).dom().contains(ptr) && ptr != thread_ptr
            ==> final(thread_map).spec_index(ptr) == old(thread_map).spec_index(ptr),
        forall|ptr: RwLockThreadPtr|
            #![trigger final(thread_map).view().spec_index(ptr).is_init()]
            old(thread_map).dom().contains(ptr) ==> {
                &&& final(thread_map).view().spec_index(ptr).is_init()
                    == old(thread_map).view().spec_index(ptr).is_init()
                &&& final(thread_map).view().spec_index(ptr).addr()
                    == old(thread_map).view().spec_index(ptr).addr()
            },
        final(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thread_map).spec_index(thread_ptr).view() == (Thread {
            quota_4k: final(thread_map).spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k,
            ..old(thread_map).spec_index(thread_ptr).view()
        }),
        final(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
            == old(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
        final(thread_map).spec_index(thread_ptr).view().quota_4k == old(thread_map).spec_index(thread_ptr).view().quota_4k - 1,
        final(thread_map).lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init()
        && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(
        thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm),
    );
    thread.consume_staged_4k(page_ptr);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(lctx.thread_lock_map().index(thread_ptr).lock_id == thread_map.lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_add_free_quota_pending_4k(
    thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        depth <= old(thread_map).spec_index(thread_ptr).view().container_depth,
        *old(counter) == old(thread_map).spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth),
        *old(counter) < usize::MAX,
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).perms_wf(),
        final(thread_map).dom() == old(thread_map).dom(),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thread_map).lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr),
        final(thread_map).spec_index(thread_ptr).is_init(),
        final(thread_map).spec_index(thread_ptr).inv(),
        final(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(thread_ptr).view_rodata() == old(thread_map).spec_index(thread_ptr).view_rodata(),
        final(thread_map).spec_index(thread_ptr).view_ghost() == old(thread_map).spec_index(thread_ptr).view_ghost(),
        final(thread_map).spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(thread_map).spec_index(thread_ptr).view() }),
        *final(counter) == *old(counter) + 1,
        final(thread_map).spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == *final(counter),
        final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == old(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() + if depth == old(thread_map).spec_index(thread_ptr).view().container_depth { 1int } else { 0int },
        final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() == if depth < old(thread_map).spec_index(thread_ptr).view().container_depth { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, *final(counter)) } else { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init() && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.add_free_quota_pending_4k(depth, counter);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thread_map.lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_clear_free_quota_pending_4k(
    thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == lctx.thread_id(),
        thread_lock_perm.lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        depth <= old(thread_map).spec_index(thread_ptr).view().container_depth,
        *old(counter) == old(thread_map).spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth),
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).perms_wf(),
        final(thread_map).dom() == old(thread_map).dom(),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thread_map).lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr),
        final(thread_map).spec_index(thread_ptr).is_init(),
        final(thread_map).spec_index(thread_ptr).inv(),
        final(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(thread_ptr).view_rodata() == old(thread_map).spec_index(thread_ptr).view_rodata(),
        final(thread_map).spec_index(thread_ptr).view_ghost() == old(thread_map).spec_index(thread_ptr).view_ghost(),
        final(thread_map).spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(thread_map).spec_index(thread_ptr).view() }),
        *final(counter) == 0,
        final(thread_map).spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == 0,
        final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == if depth == old(thread_map).spec_index(thread_ptr).view().container_depth { 0usize } else { old(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() },
        final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() == if depth < old(thread_map).spec_index(thread_ptr).view().container_depth { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, 0usize) } else { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init() && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.clear_free_quota_pending_4k(depth, counter);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thread_map.lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn process_map_add_owned_thread(
    process_map: &mut ProcessLockedMap, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(process_lock_perm): Tracked<&LockPerm>,
)
    requires
        process_perms_wf(*old(process_map)),
        old(process_map).dom().contains(process_ptr),
        old(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == lctx.thread_id(),
        process_lock_perm.lock_id() == old(process_map).spec_index(process_ptr).locking_thread()->Write_lock_id,
        !old(process_map).spec_index(process_ptr).view().zombie,
        node_perm.is_init(),
        node_perm.addr() == node_addr,
        !old(process_map).spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        old(process_map).spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX,
    ensures
        process_perms_wf(*final(process_map)),
        final(process_map).unchanged_except(old(process_map), process_ptr),
        final(process_map).dom() == old(process_map).dom(),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) && ptr != process_ptr
            ==> final(process_map).spec_index(ptr) == old(process_map).spec_index(ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).view().children == old(process_map).spec_index(ptr).view().children
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).view_ghost().subtree_set == old(process_map).spec_index(ptr).view_ghost().subtree_set
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
            },
        final(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(process_map).spec_index(process_ptr).view() == (Process {
            owned_threads: final(process_map).spec_index(process_ptr).view().owned_threads,
            ..old(process_map).spec_index(process_ptr).view()
        }),
        final(process_map).spec_index(process_ptr).view().owned_threads.view()
            == old(process_map).spec_index(process_ptr).view().owned_threads.view().push(thread_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.dom()
            == old(process_map).spec_index(process_ptr).view().owned_threads.dom().insert(node_addr),
        final(process_map).spec_index(process_ptr).view().owned_threads.map()
            == old(process_map).spec_index(process_ptr).view().owned_threads.map().insert(node_addr, thread_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.length
            == old(process_map).spec_index(process_ptr).view().owned_threads.length + 1,
        !old(process_map).spec_index(process_ptr).view().owned_threads.dom().contains(node_addr),
        !old(process_map).spec_index(process_ptr).view().owned_threads.map().dom().contains(node_addr),
        final(process_map).spec_index(process_ptr).view().zombie == old(process_map).spec_index(process_ptr).view().zombie,
        final(process_map).spec_index(process_ptr).view().pagetable == old(process_map).spec_index(process_ptr).view().pagetable,
        final(process_map).spec_index(process_ptr).view().pcid == old(process_map).spec_index(process_ptr).view().pcid,
        final(process_map).spec_index(process_ptr).view_rodata() == old(process_map).spec_index(process_ptr).view_rodata(),
        final(process_map).lock_id_by_key(process_ptr) == old(process_map).lock_id_by_key(process_ptr),
        final(process_map).spec_index(process_ptr).locking_thread() == old(process_map).spec_index(process_ptr).locking_thread(),
        final(process_map).spec_index(process_ptr).being_killed() == old(process_map).spec_index(process_ptr).being_killed(),
{
    assert(process_map.perms_wf() && process_map.spec_index(process_ptr).is_init()
        && process_map.spec_index(process_ptr).inv()) by { process_perms_wf_at(*process_map, process_ptr); };
    let process = process_map.borrow_mut_typed(
        process_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(process_lock_perm),
    );
    process.add_owned_thread(thread_ptr, node_addr, node_perm);
    proof {
        assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
        assert(process_map.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn scheduler_map_enqueue_scheduled_thread(
    scheduler_map: &mut SchedulerLockedMap, scheduler_ptr: RwLockSchedulerPtr, thread_ptr: RwLockThreadPtr,
    node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
)
    requires
        scheduler_perms_wf(*old(scheduler_map)),
        old(scheduler_map).dom().contains(scheduler_ptr),
        old(scheduler_map).typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == lctx.thread_id(),
        scheduler_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == thread_ptr,
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(thread_ptr),
        old(scheduler_map).spec_index(scheduler_ptr).view().queue.length != usize::MAX,
    ensures
        scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).unchanged_except(old(scheduler_map), scheduler_ptr),
        final(scheduler_map).dom() == old(scheduler_map).dom(),
        forall|ptr: RwLockSchedulerPtr|
            #![trigger final(scheduler_map).spec_index(ptr)]
            old(scheduler_map).dom().contains(ptr) && ptr != scheduler_ptr
            ==> final(scheduler_map).spec_index(ptr) == old(scheduler_map).spec_index(ptr),
        final(scheduler_map).typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(scheduler_map).spec_index(scheduler_ptr).view() == (Scheduler {
            queue: final(scheduler_map).spec_index(scheduler_ptr).view().queue,
            ..old(scheduler_map).spec_index(scheduler_ptr).view()
        }),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.view()
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().push(thread_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.map()
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().insert(node_addr, thread_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.dom()
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.dom().insert(node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.map().spec_index(node_addr) == thread_ptr,
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.length
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.length + 1,
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.dom().contains(node_addr),
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).view().owning_container
            == old(scheduler_map).spec_index(scheduler_ptr).view().owning_container,
        final(scheduler_map).lock_id_by_key(scheduler_ptr) == old(scheduler_map).lock_id_by_key(scheduler_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).locking_thread() == old(scheduler_map).spec_index(scheduler_ptr).locking_thread(),
        final(scheduler_map).spec_index(scheduler_ptr).being_killed() == old(scheduler_map).spec_index(scheduler_ptr).being_killed(),
{
    assert(scheduler_map.perms_wf() && scheduler_map.spec_index(scheduler_ptr).is_init()
        && scheduler_map.spec_index(scheduler_ptr).inv()) by { scheduler_perms_wf_at(*scheduler_map, scheduler_ptr); };
    let scheduler = scheduler_map.borrow_mut_typed(
        scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(scheduler_lock_perm),
    );
    scheduler.enqueue_scheduled_thread(thread_ptr, node_addr, node_perm);
    proof {
        assert(scheduler_perms_wf(*scheduler_map)) by { reveal(scheduler_perms_wf); reveal(LinkedList::wf_value_list); };
        assert(scheduler_map.typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(lctx.scheduler_lock_map().index(scheduler_ptr).lock_id == scheduler_map.lock_id_by_key(scheduler_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn container_map_add_owned_process(
    container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(container_lock_perm): Tracked<&LockPerm>,
)
    requires
        container_perms_wf(*old(container_map)),
        old(container_map).dom().contains(container_ptr),
        old(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == lctx.thread_id(),
        container_lock_perm.lock_id() == old(container_map).spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(container_map).spec_index(container_ptr).view().root_process_in_processes(),
    ensures
        container_perms_wf(*final(container_map)),
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        final(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(container_map).spec_index(container_ptr).view() == (Container {
            owned_processes: final(container_map).spec_index(container_ptr).view().owned_processes,
            ..old(container_map).spec_index(container_ptr).view()
        }),
        final(container_map).spec_index(container_ptr).view().owned_processes.view()
            == old(container_map).spec_index(container_ptr).view().owned_processes.view().insert(process_ptr),
        final(container_map).spec_index(container_ptr).view_rodata()
            == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost()
            == old(container_map).spec_index(container_ptr).view_ghost(),
        final(container_map).spec_index(container_ptr).locking_thread()
            == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).being_killed()
            == old(container_map).spec_index(container_ptr).being_killed(),
        final(container_map).spec_index(container_ptr).inv(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(container_map).view().spec_index(ptr).is_init()]
            old(container_map).dom().contains(ptr) ==> {
                &&& final(container_map).view().spec_index(ptr).is_init()
                    == old(container_map).view().spec_index(ptr).is_init()
                &&& final(container_map).view().spec_index(ptr).addr()
                    == old(container_map).view().spec_index(ptr).addr()
            },
{
    assert(container_map.perms_wf() && container_map.spec_index(container_ptr).is_init()
        && container_map.spec_index(container_ptr).inv()) by { container_perms_wf_at(*container_map, container_ptr); };
    let container = container_map.borrow_mut_typed(
        container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(container_lock_perm),
    );
    container.add_owned_process(process_ptr);
    proof {
        assert(container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
        assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn pcid_allocator_map_alloc(
    allocator_map: &mut PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr,
    process_ptr: RwLockProcessPtr, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(allocator_lock_perm): Tracked<&LockPerm>,
)
    requires
        pcid_allocator_perms_wf(*old(allocator_map)),
        old(allocator_map).dom().contains(allocator_ptr),
        old(allocator_map).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pcid_allocator_lock_map(), allocator_ptr, TypedLockMode::Write),
        allocator_lock_perm.state() is WriteLock,
        allocator_lock_perm.thread_id() == lctx.thread_id(),
        allocator_lock_perm.lock_id() == old(allocator_map).spec_index(allocator_ptr).locking_thread()->Write_lock_id,
        old(allocator_map).spec_index(allocator_ptr).view().pcid_is_free(pcid),
        old(allocator_map).spec_index(allocator_ptr).view().process_is_unallocated(process_ptr),
    ensures
        pcid_allocator_perms_wf(*final(allocator_map)),
        final(allocator_map).perms_wf(),
        final(allocator_map).unchanged_except(old(allocator_map), allocator_ptr),
        final(allocator_map).dom() == old(allocator_map).dom(),
        final(allocator_map).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        final(allocator_map).spec_index(allocator_ptr).view().alloc_ensures(
            &old(allocator_map).spec_index(allocator_ptr).view(), process_ptr, pcid,
        ),
        final(allocator_map).spec_index(allocator_ptr).locking_thread()
            == old(allocator_map).spec_index(allocator_ptr).locking_thread(),
        final(allocator_map).spec_index(allocator_ptr).being_killed()
            == old(allocator_map).spec_index(allocator_ptr).being_killed(),
        final(allocator_map).spec_index(allocator_ptr).inv(),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(allocator_map).view().spec_index(ptr).is_init()]
            old(allocator_map).dom().contains(ptr) ==> {
                &&& final(allocator_map).view().spec_index(ptr).is_init()
                    == old(allocator_map).view().spec_index(ptr).is_init()
                &&& final(allocator_map).view().spec_index(ptr).addr()
                    == old(allocator_map).view().spec_index(ptr).addr()
            },
{
    assert(allocator_map.perms_wf() && allocator_map.spec_index(allocator_ptr).is_init()
        && allocator_map.spec_index(allocator_ptr).inv()) by { pcid_allocator_perms_wf_at(*allocator_map, allocator_ptr); };
    let allocator = allocator_map.borrow_mut_typed(
        allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(lctx), Tracked(allocator_lock_perm),
    );
    proof {
        assert(allocator.ref_counters.spec_index(pcid) < usize::MAX) by { assert(0usize < usize::MAX) by (compute); };
    }
    allocator.alloc(pcid, process_ptr);
    proof {
        assert(pcid_allocator_perms_wf(*allocator_map)) by { reveal(pcid_allocator_perms_wf); };
        assert(allocator_map.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn process_map_link_new_child(
    process_map: &mut ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
    Ghost(ancestors): Ghost<Seq<RwLockProcessPtr>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(child_lock_perm): Tracked<&LockPerm>,
)
    requires
        process_perms_wf(*old(process_map)),
        old(process_map).dom().contains(parent_ptr),
        old(process_map).dom().contains(child_ptr),
        parent_ptr != child_ptr,
        old(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), parent_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), child_ptr, TypedLockMode::Write),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == lctx.thread_id(),
        parent_lock_perm.lock_id() == old(process_map).spec_index(parent_ptr).locking_thread()->Write_lock_id,
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == lctx.thread_id(),
        child_lock_perm.lock_id() == old(process_map).spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.is_init(),
        !old(process_map).spec_index(parent_ptr).view().children.view().contains(child_ptr),
        old(process_map).spec_index(parent_ptr).view().children.view().len() < usize::MAX,
        ancestors == old(process_map).spec_index(child_ptr).view_ghost().uppertree_seq.view(),
        ancestors.to_set().subset_of(old(process_map).dom()),
        ancestors.no_duplicates(),
        !ancestors.to_set().contains(child_ptr),
    ensures
        process_perms_wf(*final(process_map)),
        final(process_map).perms_wf(),
        final(process_map).spec_index(parent_ptr).inv(),
        final(process_map).spec_index(child_ptr).inv(),
        final(process_map).dom() == old(process_map).dom(),
        final(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(process_map).spec_index(child_ptr).view() == (Process {
            parent_linkedlist_node: final(process_map).spec_index(child_ptr).view().parent_linkedlist_node,
            ..old(process_map).spec_index(child_ptr).view()
        }),
        !final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.is_init(),
        final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()
            == old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        final(process_map).spec_index(parent_ptr).view() == (Process {
            children: final(process_map).spec_index(parent_ptr).view().children,
            ..old(process_map).spec_index(parent_ptr).view()
        }),
        final(process_map).spec_index(parent_ptr).view().children.view()
            == old(process_map).spec_index(parent_ptr).view().children.view().push(child_ptr),
        final(process_map).spec_index(parent_ptr).view().children.dom()
            == old(process_map).spec_index(parent_ptr).view().children.dom().insert(
                final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
            ),
        final(process_map).spec_index(parent_ptr).view().children.map()
            == old(process_map).spec_index(parent_ptr).view().children.map().insert(
                final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(), child_ptr,
            ),
        !old(process_map).spec_index(parent_ptr).view().children.map().dom().contains(
            final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        ),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).is_init() == old(process_map).spec_index(ptr).is_init()
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq
                    == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).locking_thread() == old(process_map).spec_index(ptr).locking_thread()
                &&& final(process_map).spec_index(ptr).being_killed() == old(process_map).spec_index(ptr).being_killed()
                &&& ptr != parent_ptr && ptr != child_ptr
                    ==> final(process_map).spec_index(ptr).view() == old(process_map).spec_index(ptr).view()
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr).view_ghost().subtree_set]
            old(process_map).dom().contains(ptr) ==> {
                &&& ancestors.to_set().contains(ptr) ==> final(process_map).spec_index(ptr).view_ghost().subtree_set.view()
                    == old(process_map).spec_index(ptr).view_ghost().subtree_set.view().insert(child_ptr)
                &&& !ancestors.to_set().contains(ptr) ==> final(process_map).spec_index(ptr).view_ghost().subtree_set
                    == old(process_map).spec_index(ptr).view_ghost().subtree_set
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).view().spec_index(ptr).is_init()]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).view().spec_index(ptr).is_init()
                    == old(process_map).view().spec_index(ptr).is_init()
                &&& final(process_map).view().spec_index(ptr).addr()
                    == old(process_map).view().spec_index(ptr).addr()
            },
{
    assert(process_map.perms_wf() && process_map.spec_index(child_ptr).is_init()
        && process_map.spec_index(child_ptr).inv()) by { process_perms_wf_at(*process_map, child_ptr); };
    let child = process_map.borrow_mut_typed(
        child_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(child_lock_perm),
    );
    let (child_node_addr, child_node_perm) = child.parent_linkedlist_node.take();
    proof {
        assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
        assert(process_map.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(process_map.perms_wf() && process_map.spec_index(parent_ptr).is_init()
            && process_map.spec_index(parent_ptr).inv()) by { process_perms_wf_at(*process_map, parent_ptr); };
    }
    let parent = process_map.borrow_mut_typed(
        parent_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(parent_lock_perm),
    );
    parent.add_child(child_ptr, child_node_addr, child_node_perm);
    proof {
        assert(process_perms_wf(*process_map)) by {
            reveal(process_perms_wf);
            seq_push_unique_lemma::<RwLockProcessPtr>();
        };
        assert(process_map.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        process_insert_child_into_ancestor_subtree_sets(
            process_map, ancestors, child_ptr, lctx.process_lock_map(), lctx.thread_id(),
        );
    }
}

pub proof fn add_thread_to_container_sets(
    tracked container_map: &mut ContainerLockedMap, direct_container_ptr: RwLockContainerPtr,
    t_ptr: RwLockThreadPtr, uppers: Seq<RwLockContainerPtr>, thread_map: ThreadLockedMap,
    scheduler_map: SchedulerLockedMap, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(direct_container_ptr),
        uppers.to_set().subset_of(old(container_map).dom()),
        uppers.no_duplicates(),
        !uppers.to_set().contains(direct_container_ptr),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id),
        container_thread_scheduler_wf(*old(container_map), thread_map, scheduler_map),
        forall|t: RwLockThreadPtr|
            #![trigger thread_map.dom().contains(t)]
            thread_map.dom().contains(t)
            ==> old(container_map).dom().contains(thread_map.spec_index(t).view().owning_container),
        forall|c: RwLockContainerPtr|
            #![trigger old(container_map).dom().contains(c)]
            old(container_map).dom().contains(c)
            ==> scheduler_map.dom().contains(old(container_map).spec_index(c).view_rodata().view().scheduler),
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        container_perms_wf(*old(container_map)) ==> container_perms_wf(*final(container_map)),
        final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        container_thread_scheduler_wf(*final(container_map), thread_map, scheduler_map),
        forall|t: RwLockThreadPtr|
            #![trigger thread_map.dom().contains(t)]
            thread_map.dom().contains(t)
            ==> final(container_map).dom().contains(thread_map.spec_index(t).view().owning_container),
        forall|c: RwLockContainerPtr|
            #![trigger final(container_map).dom().contains(c)]
            final(container_map).dom().contains(c)
            ==> scheduler_map.dom().contains(final(container_map).spec_index(c).view_rodata().view().scheduler),
        forall|c: RwLockContainerPtr|
            #![trigger final(container_map).spec_index(c)]
            old(container_map).dom().contains(c) ==> {
                &&& final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                &&& final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                &&& final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                &&& final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed()
                &&& final(container_map).spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: old(container_map).spec_index(c).view_ghost().uppertree_seq,
                    subtree_set: old(container_map).spec_index(c).view_ghost().subtree_set,
                    owned_threads: if c == direct_container_ptr {
                        Ghost(old(container_map).spec_index(c).view_ghost().owned_threads.view().insert(t_ptr))
                    } else {
                        old(container_map).spec_index(c).view_ghost().owned_threads
                    },
                    owned_indirect_threads: if uppers.to_set().contains(c) {
                        Ghost(old(container_map).spec_index(c).view_ghost().owned_indirect_threads.view().insert(t_ptr))
                    } else {
                        old(container_map).spec_index(c).view_ghost().owned_indirect_threads
                    },
                }
            },
    decreases uppers.len(),
{
    if uppers.len() > 0 {
        let c0 = uppers.spec_index(0);
        assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
        assert(uppers.drop_first().to_set().subset_of(container_map.dom())) by {
            uppers.to_set_ensures();
            uppers.drop_first().to_set_ensures();
            broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
        };
        assert(!uppers.drop_first().to_set().contains(direct_container_ptr)) by {
            uppers.to_set_ensures();
            uppers.drop_first().to_set_ensures();
            broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
        };
        add_thread_to_container_sets(
            container_map, direct_container_ptr, t_ptr, uppers.drop_first(), thread_map,
            scheduler_map, held_locks, thread_id,
        );
        container_map.update_ghost(c0, ContainerGhost {
            uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq,
            subtree_set: container_map.spec_index(c0).view_ghost().subtree_set,
            owned_threads: container_map.spec_index(c0).view_ghost().owned_threads,
            owned_indirect_threads: Ghost(container_map.spec_index(c0).view_ghost().owned_indirect_threads.view().insert(t_ptr)),
        });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& !uppers.drop_first().to_set().contains(c0)
            &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    } else {
        container_map.update_ghost(direct_container_ptr, ContainerGhost {
            uppertree_seq: container_map.spec_index(direct_container_ptr).view_ghost().uppertree_seq,
            subtree_set: container_map.spec_index(direct_container_ptr).view_ghost().subtree_set,
            owned_threads: Ghost(container_map.spec_index(direct_container_ptr).view_ghost().owned_threads.view().insert(t_ptr)),
            owned_indirect_threads: container_map.spec_index(direct_container_ptr).view_ghost().owned_indirect_threads,
        });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    assert(container_perms_wf(*old(container_map)) ==> container_perms_wf(*container_map)) by {
        reveal(container_perms_wf);
        reveal(container_tree_fields_wf);
    };
    assert(container_thread_scheduler_wf(*container_map, thread_map, scheduler_map)) by { reveal(container_thread_scheduler_wf); };
}

#[verifier::opaque]
pub open spec fn process_subsystem_create_scheduled_thread_transition_framing(
    pre_process: ProcessLockedMap, post_process: ProcessLockedMap,
    pre_thread: ThreadLockedMap, post_thread: ThreadLockedMap,
    pre_scheduler: SchedulerLockedMap, post_scheduler: SchedulerLockedMap,
    pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr, thread_value: Thread, process_node_addr: usize, sched_node_addr: usize,
) -> bool {
    &&& post_process.dom() == pre_process.dom()
    &&& post_process.unchanged_except(&pre_process, process_ptr)
    &&& post_process.spec_index(process_ptr).view() == (Process {
        owned_threads: post_process.spec_index(process_ptr).view().owned_threads,
        ..pre_process.spec_index(process_ptr).view()
    })
    &&& post_process.spec_index(process_ptr).view().owned_threads.view()
        == pre_process.spec_index(process_ptr).view().owned_threads.view().push(page_ptr)
    &&& post_process.spec_index(process_ptr).view().owned_threads.dom()
        == pre_process.spec_index(process_ptr).view().owned_threads.dom().insert(process_node_addr)
    &&& post_process.spec_index(process_ptr).view().owned_threads.map()
        == pre_process.spec_index(process_ptr).view().owned_threads.map().insert(process_node_addr, page_ptr)
    &&& !pre_process.spec_index(process_ptr).view().owned_threads.dom().contains(process_node_addr)
    &&& !pre_process.spec_index(process_ptr).view().owned_threads.map().dom().contains(process_node_addr)
    &&& post_process.spec_index(process_ptr).view_rodata() == pre_process.spec_index(process_ptr).view_rodata()
    &&& post_process.spec_index(process_ptr).view_ghost() == pre_process.spec_index(process_ptr).view_ghost()
    &&& post_process.spec_index(process_ptr).locking_thread() == pre_process.spec_index(process_ptr).locking_thread()
    &&& post_process.spec_index(process_ptr).being_killed() == pre_process.spec_index(process_ptr).being_killed()
    &&& forall|ptr: RwLockProcessPtr|
        #![trigger post_process.spec_index(ptr)]
        pre_process.dom().contains(ptr) && ptr != process_ptr
        ==> post_process.spec_index(ptr) == pre_process.spec_index(ptr)
    &&& post_thread.dom() =~= pre_thread.dom().insert(page_ptr)
    &&& post_thread.spec_index(page_ptr).view() == thread_value
    &&& post_thread.spec_index(page_ptr).is_init()
    &&& !post_thread.spec_index(page_ptr).being_killed()
    &&& post_thread.spec_index(staging_thread_ptr).view() == (Thread {
        quota_4k: post_thread.spec_index(staging_thread_ptr).view().quota_4k,
        temp_alloc_cache_4k: post_thread.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k,
        ..pre_thread.spec_index(staging_thread_ptr).view()
    })
    &&& post_thread.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view()
        == pre_thread.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& post_thread.spec_index(staging_thread_ptr).view().quota_4k
        == pre_thread.spec_index(staging_thread_ptr).view().quota_4k - 1
    &&& post_thread.spec_index(staging_thread_ptr).locking_thread() == pre_thread.spec_index(staging_thread_ptr).locking_thread()
    &&& post_thread.spec_index(staging_thread_ptr).being_killed() == pre_thread.spec_index(staging_thread_ptr).being_killed()
    &&& forall|ptr: RwLockThreadPtr|
        #![trigger post_thread.spec_index(ptr)]
        pre_thread.dom().contains(ptr) && ptr != staging_thread_ptr
        ==> post_thread.spec_index(ptr) == pre_thread.spec_index(ptr)
    &&& post_scheduler.dom() == pre_scheduler.dom()
    &&& post_scheduler.unchanged_except(&pre_scheduler, scheduler_ptr)
    &&& post_scheduler.spec_index(scheduler_ptr).view() == (Scheduler {
        queue: post_scheduler.spec_index(scheduler_ptr).view().queue,
        ..pre_scheduler.spec_index(scheduler_ptr).view()
    })
    &&& post_scheduler.spec_index(scheduler_ptr).view().queue.view()
        == pre_scheduler.spec_index(scheduler_ptr).view().queue.view().push(page_ptr)
    &&& post_scheduler.spec_index(scheduler_ptr).view().queue.dom()
        == pre_scheduler.spec_index(scheduler_ptr).view().queue.dom().insert(sched_node_addr)
    &&& post_scheduler.spec_index(scheduler_ptr).view().queue.map()
        == pre_scheduler.spec_index(scheduler_ptr).view().queue.map().insert(sched_node_addr, page_ptr)
    &&& !pre_scheduler.spec_index(scheduler_ptr).view().queue.dom().contains(sched_node_addr)
    &&& !pre_scheduler.spec_index(scheduler_ptr).view().queue.map().dom().contains(sched_node_addr)
    &&& post_scheduler.spec_index(scheduler_ptr).locking_thread() == pre_scheduler.spec_index(scheduler_ptr).locking_thread()
    &&& post_scheduler.spec_index(scheduler_ptr).being_killed() == pre_scheduler.spec_index(scheduler_ptr).being_killed()
    &&& forall|ptr: RwLockSchedulerPtr|
        #![trigger post_scheduler.spec_index(ptr)]
        pre_scheduler.dom().contains(ptr) && ptr != scheduler_ptr
        ==> post_scheduler.spec_index(ptr) == pre_scheduler.spec_index(ptr)
    &&& post_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& post_lctx.thread_id() == pre_lctx.thread_id()
    &&& post_lctx.kernel_view_locking_state() == pre_lctx.kernel_view_locking_state()
    &&& typed_lock_maps_inserted(pre_lctx, post_lctx, KernelObjId::Thread(page_ptr), TypedHeldLock {
        lock_id: post_thread.lock_id_by_key(page_ptr), mode: TypedLockMode::Write,
    })
}

proof fn process_subsystem_create_scheduled_thread_eof_process_thread_wf(
    pre_process: ProcessLockedMap, post_process: ProcessLockedMap, pre_thread: ThreadLockedMap,
    post_thread: ThreadLockedMap, pre_scheduler: SchedulerLockedMap,
    post_scheduler: SchedulerLockedMap, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr, thread_value: Thread, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        process_thread_wf(pre_process, pre_thread),
        process_perms_wf(post_process),
        pre_process.dom().contains(process_ptr),
        !pre_process.spec_index(process_ptr).view().zombie,
        !pre_process.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr),
        process_subsystem_create_scheduled_thread_transition_framing(
            pre_process, post_process, pre_thread, post_thread, pre_scheduler, post_scheduler, pre_lctx, post_lctx,
            page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, thread_value, process_node_addr, sched_node_addr,
        ),
        !pre_thread.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        thread_value.owning_proc == process_ptr,
        thread_value.process_depth == pre_process.spec_index(process_ptr).view_rodata().view().depth,
        thread_value.owning_container == pre_process.spec_index(process_ptr).view_rodata().view().owning_container,
        thread_value.container_depth == pre_process.spec_index(process_ptr).view_rodata().view().container_depth,
        thread_value.proc_pagetable_ptr == pre_process.spec_index(process_ptr).view().pagetable,
        thread_value.proc_linkedlist_node.addr() == process_node_addr,
    ensures
        process_thread_wf(post_process, post_thread),
{
    reveal(process_subsystem_create_scheduled_thread_transition_framing);
    reveal(process_thread_wf);
    seq_push_lemma::<RwLockThreadPtr>();
    assert(process_empty_lists_wlocked(post_process)) by {
        reveal(process_perms_wf);
        reveal(process_empty_lists_wlocked);
    };
}

proof fn process_subsystem_create_scheduled_thread_eof_scheduler_wf(
    container_map: ContainerLockedMap, pre_process: ProcessLockedMap, post_process: ProcessLockedMap,
    pre_thread: ThreadLockedMap, post_thread: ThreadLockedMap, pre_scheduler: SchedulerLockedMap,
    post_scheduler: SchedulerLockedMap, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, thread_value: Thread,
    process_node_addr: usize, sched_node_addr: usize,
)
    requires
        container_thread_scheduler_wf(container_map, pre_thread, pre_scheduler),
        container_thread_wf(container_map, pre_thread),
        container_scheduler_wf(container_map, pre_scheduler),
        container_map.dom().contains(container_ptr),
        pre_scheduler.dom().contains(scheduler_ptr),
        !pre_scheduler.spec_index(scheduler_ptr).view().queue.view().contains(page_ptr),
        process_subsystem_create_scheduled_thread_transition_framing(
            pre_process, post_process, pre_thread, post_thread, pre_scheduler, post_scheduler, pre_lctx, post_lctx,
            page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, thread_value, process_node_addr, sched_node_addr,
        ),
        !pre_thread.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        thread_value.state is SCHEDULED,
        thread_value.owning_container == container_ptr,
        thread_value.scheduler_linkedlist_node.addr() == sched_node_addr,
    ensures
        container_thread_scheduler_wf(container_map, post_thread, post_scheduler),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger post_thread.dom().contains(t_ptr)]
            post_thread.dom().contains(t_ptr)
            ==> container_map.dom().contains(post_thread.spec_index(t_ptr).view().owning_container),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr)
            ==> post_scheduler.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler),
{
    reveal(process_subsystem_create_scheduled_thread_transition_framing);
    reveal(container_thread_scheduler_wf);
    reveal(container_thread_wf);
    reveal(container_scheduler_wf);
    seq_push_lemma::<RwLockThreadPtr>();
}

pub fn process_subsystem_create_scheduled_thread(
    container_map: &ContainerLockedMap, process_map: &mut ProcessLockedMap, thread_map: &mut ThreadLockedMap,
    scheduler_map: &mut SchedulerLockedMap, page_ptr: PagePtr, process_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
    thread_value: Thread, sched_node_addr: usize, sched_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    process_node_addr: usize, process_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(staging_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<LockPerm>)
    requires
        container_perms_wf(*container_map),
        process_perms_wf(*old(process_map)),
        thread_perms_wf(*old(thread_map)),
        scheduler_perms_wf(*old(scheduler_map)),
        container_process_wf(*container_map, *old(process_map)),
        container_thread_wf(*container_map, *old(thread_map)),
        container_scheduler_wf(*container_map, *old(scheduler_map)),
        process_thread_wf(*old(process_map), *old(thread_map)),
        container_thread_scheduler_wf(*container_map, *old(thread_map), *old(scheduler_map)),
        old(process_map).dom().contains(process_ptr),
        old(thread_map).dom().contains(staging_thread_ptr),
        !old(thread_map).dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        container_map.dom().contains(container_ptr),
        old(scheduler_map).dom().contains(scheduler_ptr),
        container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(process_map).spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(scheduler_map).spec_index(scheduler_ptr).view().owning_container == container_ptr,
        !old(process_map).spec_index(process_ptr).view().zombie,
        !old(process_map).spec_index(process_ptr).view().owned_threads.view().contains(page_ptr),
        old(process_map).spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX,
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(page_ptr),
        old(scheduler_map).spec_index(scheduler_ptr).view().queue.length != usize::MAX,
        old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![page_ptr],
        old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(thread_map).spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        old(thread_map).spec_index(staging_thread_ptr).view().quota_4k >= 1,
        thread_value.inv(),
        thread_value.state is SCHEDULED,
        thread_value.owning_container == container_ptr,
        thread_value.container_depth == container_map.spec_index(container_ptr).view_rodata().view().depth,
        thread_value.container_depth == old(process_map).spec_index(process_ptr).view_rodata().view().container_depth,
        thread_value.owning_proc == process_ptr,
        thread_value.process_depth == old(process_map).spec_index(process_ptr).view_rodata().view().depth,
        thread_value.proc_pagetable_ptr == old(process_map).spec_index(process_ptr).view().pagetable,
        thread_value.scheduler_linkedlist_node.addr() == sched_node_addr,
        thread_value.proc_linkedlist_node.addr() == process_node_addr,
        sched_node_perm.view().is_init(),
        sched_node_perm.view().addr() == sched_node_addr,
        sched_node_perm.view().value().view() == page_ptr,
        process_node_perm.view().is_init(),
        process_node_perm.view().addr() == process_node_addr,
        process_node_perm.view().value().view() == page_ptr,
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        old(process_map).typed_lock_map_aligned(old(lctx).process_lock_map(), old(lctx).thread_id()),
        old(thread_map).typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id()),
        old(scheduler_map).typed_lock_map_aligned(old(lctx).scheduler_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(process_map).spec_index(process_ptr).locking_thread()->Write_lock_id,
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(thread_map).spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
    ensures
        process_perms_wf(*final(process_map)),
        thread_perms_wf(*final(thread_map)),
        scheduler_perms_wf(*final(scheduler_map)),
        process_subsystem_create_scheduled_thread_transition_framing(
            *old(process_map), *final(process_map), *old(thread_map), *final(thread_map),
            *old(scheduler_map), *final(scheduler_map), old(lctx), final(lctx), page_ptr, process_ptr,
            staging_thread_ptr, scheduler_ptr, thread_value, process_node_addr, sched_node_addr,
        ),
        process_thread_wf(*final(process_map), *final(thread_map)),
        container_thread_scheduler_wf(*container_map, *final(thread_map), *final(scheduler_map)),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger final(thread_map).dom().contains(t_ptr)]
            final(thread_map).dom().contains(t_ptr)
            ==> container_map.dom().contains(final(thread_map).spec_index(t_ptr).view().owning_container),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr)
            ==> final(scheduler_map).dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler),
        final(process_map).dom() == old(process_map).dom(),
        final(thread_map).dom() =~= old(thread_map).dom().insert(page_ptr),
        final(scheduler_map).dom() == old(scheduler_map).dom(),
        forall|t: RwLockThreadPtr| #![trigger final(thread_map).spec_index(t)]
            old(thread_map).dom().contains(t) ==> final(thread_map).spec_index(t).view().endpoint_descriptors.view()
                == old(thread_map).spec_index(t).view().endpoint_descriptors.view(),
        final(thread_map).spec_index(page_ptr).view() == thread_value,
        final(thread_map).spec_index(page_ptr).is_init(),
        final(thread_map).spec_index(page_ptr).inv(),
        final(thread_map).spec_index(page_ptr).being_killed() == false,
        final(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view()
            == old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
        final(thread_map).spec_index(staging_thread_ptr).view().quota_4k
            == old(thread_map).spec_index(staging_thread_ptr).view().quota_4k - 1,
        final(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_clean(),
        final(thread_map).spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        final(thread_map).spec_index(staging_thread_ptr).view() == (Thread {
            quota_4k: final(thread_map).spec_index(staging_thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k,
            ..old(thread_map).spec_index(staging_thread_ptr).view()
        }),
        final(thread_map).spec_index(staging_thread_ptr).being_killed()
            == old(thread_map).spec_index(staging_thread_ptr).being_killed(),
        final(thread_map).spec_index(staging_thread_ptr).locking_thread()
            == old(thread_map).spec_index(staging_thread_ptr).locking_thread(),
        final(thread_map).lock_id_by_key(staging_thread_ptr) == old(thread_map).lock_id_by_key(staging_thread_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.view()
            == old(process_map).spec_index(process_ptr).view().owned_threads.view().push(page_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.dom()
            == old(process_map).spec_index(process_ptr).view().owned_threads.dom().insert(process_node_addr),
        final(process_map).spec_index(process_ptr).view().owned_threads.map()
            == old(process_map).spec_index(process_ptr).view().owned_threads.map().insert(process_node_addr, page_ptr),
        !old(process_map).spec_index(process_ptr).view().owned_threads.dom().contains(process_node_addr),
        !old(process_map).spec_index(process_ptr).view().owned_threads.map().dom().contains(process_node_addr),
        final(process_map).spec_index(process_ptr).view() == (Process {
            owned_threads: final(process_map).spec_index(process_ptr).view().owned_threads,
            ..old(process_map).spec_index(process_ptr).view()
        }),
        final(process_map).spec_index(process_ptr).view_rodata() == old(process_map).spec_index(process_ptr).view_rodata(),
        final(process_map).spec_index(process_ptr).being_killed() == old(process_map).spec_index(process_ptr).being_killed(),
        final(process_map).spec_index(process_ptr).locking_thread() == old(process_map).spec_index(process_ptr).locking_thread(),
        final(process_map).lock_id_by_key(process_ptr) == old(process_map).lock_id_by_key(process_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.view()
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().push(page_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.dom()
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.dom().insert(sched_node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.map()
            == old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().insert(sched_node_addr, page_ptr),
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.dom().contains(sched_node_addr),
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(sched_node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).view() == (Scheduler {
            queue: final(scheduler_map).spec_index(scheduler_ptr).view().queue,
            ..old(scheduler_map).spec_index(scheduler_ptr).view()
        }),
        final(scheduler_map).lock_id_by_key(scheduler_ptr) == old(scheduler_map).lock_id_by_key(scheduler_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).being_killed() == old(scheduler_map).spec_index(scheduler_ptr).being_killed(),
        final(scheduler_map).spec_index(scheduler_ptr).locking_thread() == old(scheduler_map).spec_index(scheduler_ptr).locking_thread(),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).view().children == old(process_map).spec_index(ptr).view().children
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).view_ghost().subtree_set == old(process_map).spec_index(ptr).view_ghost().subtree_set
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) && ptr != process_ptr
            ==> final(process_map).spec_index(ptr) == old(process_map).spec_index(ptr),
        forall|ptr: RwLockThreadPtr|
            #![trigger final(thread_map).spec_index(ptr)]
            old(thread_map).dom().contains(ptr) && ptr != staging_thread_ptr
            ==> final(thread_map).spec_index(ptr) == old(thread_map).spec_index(ptr),
        forall|ptr: RwLockSchedulerPtr|
            #![trigger final(scheduler_map).spec_index(ptr)]
            old(scheduler_map).dom().contains(ptr) && ptr != scheduler_ptr
            ==> final(scheduler_map).spec_index(ptr) == old(scheduler_map).spec_index(ptr),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(thread_map).lock_id_by_key(page_ptr),
        ret.view().lock_id() == final(thread_map).spec_index(page_ptr).locking_thread()->Write_lock_id,
        final(thread_map).spec_index(page_ptr).write_lock_perm_match(&ret.view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(page_ptr), TypedHeldLock {
            lock_id: final(thread_map).lock_id_by_key(page_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(page_ptr, TypedHeldLock {
            lock_id: final(thread_map).lock_id_by_key(page_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(process_map).typed_lock_map_aligned(final(lctx).process_lock_map(), final(lctx).thread_id()),
        final(thread_map).typed_lock_map_aligned(final(lctx).thread_lock_map(), final(lctx).thread_id()),
        final(scheduler_map).typed_lock_map_aligned(final(lctx).scheduler_lock_map(), final(lctx).thread_id()),
{
    thread_map_consume_staged_4k(
        thread_map, staging_thread_ptr, page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm),
    );
    proof {
        assert(thread_map.perms_wf()) by { thread_perms_wf_map(*thread_map); };
        assert(!lctx.thread_lock_map().dom().contains(page_ptr)
            && lctx.typed_lock_entry(KernelObjId::Thread(page_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    let Tracked(thread_lock_perm) = thread_map.retype_4k_and_insert(
        page_ptr, thread_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)),
    );
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);

        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    process_map_add_owned_thread(
        process_map, process_ptr, page_ptr, process_node_addr, process_node_perm, Tracked(&*lctx), Tracked(process_lock_perm),
    );
    scheduler_map_enqueue_scheduled_thread(
        scheduler_map, scheduler_ptr, page_ptr, sched_node_addr, sched_node_perm, Tracked(&*lctx), Tracked(scheduler_lock_perm),
    );
    proof {
        assert(process_subsystem_create_scheduled_thread_transition_framing(
            *old(process_map), *process_map, *old(thread_map), *thread_map, *old(scheduler_map), *scheduler_map,
            old(lctx), &*lctx, page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, thread_value,
            process_node_addr, sched_node_addr,
        )) by { reveal(process_subsystem_create_scheduled_thread_transition_framing); };
        process_subsystem_create_scheduled_thread_eof_process_thread_wf(
            *old(process_map), *process_map, *old(thread_map), *thread_map, *old(scheduler_map),
            *scheduler_map, old(lctx), &*lctx, page_ptr, process_ptr,
            staging_thread_ptr, scheduler_ptr, thread_value, process_node_addr, sched_node_addr,
        );
        process_subsystem_create_scheduled_thread_eof_scheduler_wf(
            *container_map, *old(process_map), *process_map, *old(thread_map), *thread_map,
            *old(scheduler_map), *scheduler_map, old(lctx), &*lctx, page_ptr, process_ptr,
            staging_thread_ptr, container_ptr, scheduler_ptr, thread_value, process_node_addr, sched_node_addr,
        );
    }
    Tracked(thread_lock_perm)
}

pub fn thread_map_consume_new_container_staging(
    threads: &mut ThreadLockedMap, current_thread_ptr: RwLockThreadPtr, thread_page: PagePtr, funding_page_count: usize,
    Ghost(consumed_4k_pages): Ghost<Set<PagePtr>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(threads)),
        old(threads).dom().contains(current_thread_ptr),
        old(threads).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == lctx.thread_id(),
        current_thread_lock_perm.lock_id() == old(threads).spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(threads).spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == consumed_4k_pages.insert(thread_page),
        !consumed_4k_pages.contains(thread_page),
        consumed_4k_pages.len() == 8 + funding_page_count,
        old(threads).spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count < old(threads).spec_index(current_thread_ptr).view().quota_4k - 8,
        old(threads).spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().len() == 2,
        old(threads).spec_index(current_thread_ptr).view().quota_2m >= 2,
    ensures
        final(threads).spec_index(current_thread_ptr).inv(),
        final(threads).perms_wf(),
        thread_perms_wf(*final(threads)),
        final(threads).unchanged_except(old(threads), current_thread_ptr),
        final(threads).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(threads).spec_index(current_thread_ptr).locking_thread() == old(threads).spec_index(current_thread_ptr).locking_thread(),
        final(threads).spec_index(current_thread_ptr).being_killed() == old(threads).spec_index(current_thread_ptr).being_killed(),
        thread_quota_4k_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_2m_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_1g_fields_unchanged(*old(threads), *final(threads)),
        final(threads).spec_index(current_thread_ptr).view() == (Thread {
            temp_alloc_cache_4k: Ghost(set![thread_page]),
            temp_alloc_cache_2m: Ghost(Set::empty()),
            quota_4k: (old(threads).spec_index(current_thread_ptr).view().quota_4k as int - 8 - funding_page_count as int) as usize,
            quota_2m: (old(threads).spec_index(current_thread_ptr).view().quota_2m as int - 2) as usize,
            ..old(threads).spec_index(current_thread_ptr).view()
        }),
{
    assert(threads.perms_wf() && threads.spec_index(current_thread_ptr).is_init()
        && threads.spec_index(current_thread_ptr).view().inv()) by { thread_perms_wf_at(*threads, current_thread_ptr); };
    let thread = threads.borrow_mut_typed(
        current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(current_thread_lock_perm),
    );
    thread.temp_alloc_cache_4k = Ghost(Set::empty().insert(thread_page));
    thread.temp_alloc_cache_2m = Ghost(Set::empty());
    thread.quota_4k = thread.quota_4k - 8 - funding_page_count;
    thread.quota_2m = thread.quota_2m - 2;
    proof {
        assert(thread_perms_wf(*threads)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        assert(threads.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(thread_quota_4k_fields_unchanged(*old(threads), *threads)) by { vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page); };
    }
}
pub fn scheduler_map_insert_new_4k(
    scheduler_map: &mut SchedulerLockedMap, scheduler_ptr: RwLockSchedulerPtr, scheduler_value: Scheduler,
    Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(scheduler_map).perms_wf(),
        !old(scheduler_map).dom().contains(scheduler_ptr),
        old(scheduler_map).typed_lock_map_aligned(old(lctx).scheduler_lock_map(), old(lctx).thread_id()),
        scheduler_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == scheduler_ptr,
    ensures
        final(scheduler_map).perms_wf(),
        scheduler_perms_wf(*old(scheduler_map)) ==> scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).dom() =~= old(scheduler_map).dom().insert(scheduler_ptr),
        forall|ptr: RwLockSchedulerPtr|
            #![trigger final(scheduler_map).spec_index(ptr)]
            old(scheduler_map).dom().contains(ptr) ==> final(scheduler_map).spec_index(ptr) == old(scheduler_map).spec_index(ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view() == scheduler_value,
        final(scheduler_map).spec_index(scheduler_ptr).is_init(),
        final(scheduler_map).spec_index(scheduler_ptr).inv(),
        !final(scheduler_map).spec_index(scheduler_ptr).being_killed(),
        final(scheduler_map).spec_index(scheduler_ptr).wlocked_by(final(lctx)),
        final(scheduler_map).spec_index(scheduler_ptr).write_lock_perm_match(&ret.view()),
        final(scheduler_map).typed_lock_map_aligned(final(lctx).scheduler_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr), TypedHeldLock {
            lock_id: final(scheduler_map).lock_id_by_key(scheduler_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(scheduler_map).lock_id_by_key(scheduler_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::Scheduler(scheduler_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = scheduler_map.retype_4k_and_insert(
        scheduler_ptr, scheduler_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Scheduler(scheduler_ptr)),
    );
    proof {
        assert(scheduler_perms_wf(*old(scheduler_map)) ==> scheduler_perms_wf(*scheduler_map)) by { reveal(scheduler_perms_wf); };
        assert(scheduler_map.typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}

pub fn cpu_set_map_insert_new_4k(
    cpu_set_map: &mut CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr, cpu_set_value: CpuSet,
    Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(cpu_set_map).perms_wf(),
        !old(cpu_set_map).dom().contains(cpu_set_ptr),
        old(cpu_set_map).typed_lock_map_aligned(old(lctx).cpu_set_lock_map(), old(lctx).thread_id()),
        cpu_set_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == cpu_set_ptr,
    ensures
        final(cpu_set_map).perms_wf(),
        cpu_set_perms_wf(*old(cpu_set_map)) ==> cpu_set_perms_wf(*final(cpu_set_map)),
        final(cpu_set_map).dom() =~= old(cpu_set_map).dom().insert(cpu_set_ptr),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(cpu_set_map).spec_index(ptr)]
            old(cpu_set_map).dom().contains(ptr) ==> final(cpu_set_map).spec_index(ptr) == old(cpu_set_map).spec_index(ptr),
        final(cpu_set_map).spec_index(cpu_set_ptr).view() == cpu_set_value,
        final(cpu_set_map).spec_index(cpu_set_ptr).inv(),
        !final(cpu_set_map).spec_index(cpu_set_ptr).being_killed(),
        final(cpu_set_map).spec_index(cpu_set_ptr).write_lock_perm_match(&ret.view()),
        final(cpu_set_map).typed_lock_map_aligned(final(lctx).cpu_set_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), TypedHeldLock {
            lock_id: final(cpu_set_map).lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::CpuSet(cpu_set_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = cpu_set_map.retype_4k_and_insert(
        cpu_set_ptr, cpu_set_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)),
    );
    proof {
        assert(cpu_set_perms_wf(*old(cpu_set_map)) ==> cpu_set_perms_wf(*cpu_set_map)) by { reveal(cpu_set_perms_wf); };
        assert(cpu_set_map.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}

pub fn pcid_allocator_map_insert_new_2m(
    allocator_map: &mut PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr, allocator_value: PcidAllocator,
    Tracked(page_perm): Tracked<PagePerm2m>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(allocator_map).perms_wf(),
        !old(allocator_map).dom().contains(allocator_ptr),
        old(allocator_map).typed_lock_map_aligned(old(lctx).pcid_allocator_lock_map(), old(lctx).thread_id()),
        allocator_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == allocator_ptr,
    ensures
        final(allocator_map).perms_wf(),
        pcid_allocator_perms_wf(*old(allocator_map)) ==> pcid_allocator_perms_wf(*final(allocator_map)),
        final(allocator_map).dom() =~= old(allocator_map).dom().insert(allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(allocator_map).spec_index(ptr)]
            old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
        final(allocator_map).spec_index(allocator_ptr).view() == allocator_value,
        final(allocator_map).spec_index(allocator_ptr).is_init(),
        final(allocator_map).spec_index(allocator_ptr).inv(),
        !final(allocator_map).spec_index(allocator_ptr).being_killed(),
        final(allocator_map).spec_index(allocator_ptr).wlocked_by(final(lctx)),
        final(allocator_map).spec_index(allocator_ptr).write_lock_perm_match(&ret.view()),
        final(allocator_map).typed_lock_map_aligned(final(lctx).pcid_allocator_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr), TypedHeldLock {
            lock_id: final(allocator_map).lock_id_by_key(allocator_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(allocator_map).lock_id_by_key(allocator_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::PcidAllocator(allocator_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = allocator_map.retype_2m_and_insert(
        allocator_ptr, allocator_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::PcidAllocator(allocator_ptr)),
    );
    proof {
        assert(pcid_allocator_perms_wf(*old(allocator_map)) ==> pcid_allocator_perms_wf(*allocator_map)) by { reveal(pcid_allocator_perms_wf); };
        assert(allocator_map.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
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
        container_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == container_ptr,
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() =~= old(container_map).dom().insert(container_ptr),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(container_map).spec_index(ptr)]
            old(container_map).dom().contains(ptr) ==> final(container_map).spec_index(ptr) == old(container_map).spec_index(ptr),
        final(container_map).spec_index(container_ptr).view() == container_value,
        final(container_map).spec_index(container_ptr).view_rodata() == container_rodata,
        final(container_map).spec_index(container_ptr).view_ghost() == container_ghost,
        final(container_map).spec_index(container_ptr).is_init(),
        final(container_map).spec_index(container_ptr).inv(),
        !final(container_map).spec_index(container_ptr).being_killed(),
        final(container_map).spec_index(container_ptr).wlocked_by(final(lctx)),
        final(container_map).spec_index(container_ptr).write_lock_perm_match(&ret.view()),
        final(container_map).typed_lock_map_aligned(final(lctx).container_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(container_ptr), TypedHeldLock {
            lock_id: final(container_map).lock_id_by_key(container_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(container_map).lock_id_by_key(container_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::Container(container_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = container_map.retype_2m_and_insert(
        container_ptr, container_value, container_rodata, Ghost(container_ghost), Tracked(page_perm), Tracked(&mut *lctx),
        Ghost(KernelObjId::Container(container_ptr)),
    );
    proof { assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    lock_perm
}

pub fn container_map_take_parent_node(
    container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(container_lock_perm): Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockContainerPtr>>>))
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
        final(container_map).spec_index(container_ptr).view() == (Container {
            parent_linkedlist_node: final(container_map).spec_index(container_ptr).view().parent_linkedlist_node,
            ..old(container_map).spec_index(container_ptr).view()
        }),
        !final(container_map).spec_index(container_ptr).view().parent_linkedlist_node.is_init(),
        final(container_map).spec_index(container_ptr).view().parent_linkedlist_node.addr() == old(container_map).spec_index(container_ptr).view().parent_linkedlist_node.addr(),
        final(container_map).spec_index(container_ptr).view().parent_linkedlist_node.addr() == ret.0,
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == container_ptr,
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == old(container_map).spec_index(container_ptr).view_ghost(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).being_killed() == old(container_map).spec_index(container_ptr).being_killed(),
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
        final(container_map).spec_index(container_ptr).view() == (Container {
            children: final(container_map).spec_index(container_ptr).view().children,
            ..old(container_map).spec_index(container_ptr).view()
        }),
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
        final(container_map).spec_index(container_ptr).being_killed() == old(container_map).spec_index(container_ptr).being_killed(),
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

pub fn container_map_remove_owned_pages(
    container_map: &mut ContainerLockedMap, container_ptr: RwLockContainerPtr, Ghost(pages): Ghost<Set<PagePtr>>,
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
    ensures
        final(container_map).perms_wf(),
        final(container_map).unchanged_except(old(container_map), container_ptr),
        final(container_map).dom() == old(container_map).dom(),
        final(container_map).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        final(container_map).spec_index(container_ptr).inv(),
        final(container_map).spec_index(container_ptr).view() == (Container {
            owned_pages: Ghost(old(container_map).spec_index(container_ptr).view().owned_pages.view().difference(pages)),
            ..old(container_map).spec_index(container_ptr).view()
        }),
        final(container_map).spec_index(container_ptr).view_rodata() == old(container_map).spec_index(container_ptr).view_rodata(),
        final(container_map).spec_index(container_ptr).view_ghost() == old(container_map).spec_index(container_ptr).view_ghost(),
        final(container_map).spec_index(container_ptr).locking_thread() == old(container_map).spec_index(container_ptr).locking_thread(),
        final(container_map).spec_index(container_ptr).being_killed() == old(container_map).spec_index(container_ptr).being_killed(),
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
}

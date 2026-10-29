use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;
use vstd::assert_seqs_equal;
use crate::*;

verus! {
pub fn thread_map_consume_staged_4k(thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, page_ptr: PagePtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
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
        forall|ptr: RwLockThreadPtr| #![trigger final(thread_map).spec_index(ptr)] old(thread_map).dom().contains(ptr) && ptr != thread_ptr ==> final(thread_map).spec_index(ptr) == old(thread_map).spec_index(ptr),
        forall|ptr: RwLockThreadPtr|
            #![trigger final(thread_map).view().spec_index(ptr).is_init()]
            old(thread_map).dom().contains(ptr) ==> {
                &&& final(thread_map).view().spec_index(ptr).is_init() == old(thread_map).view().spec_index(ptr).is_init()
                &&& final(thread_map).view().spec_index(ptr).addr() == old(thread_map).view().spec_index(ptr).addr()
            },
        final(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thread_map).spec_index(thread_ptr).view() == (Thread { quota_4k: final(thread_map).spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k, ..old(thread_map).spec_index(thread_ptr).view() }),
        final(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(thread_map).spec_index(thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
        final(thread_map).spec_index(thread_ptr).view().quota_4k == old(thread_map).spec_index(thread_ptr).view().quota_4k - 1,
        final(thread_map).lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(thread_ptr).killer_info() == old(thread_map).spec_index(thread_ptr).killer_info(),
        final(thread_map).spec_index(thread_ptr).view_ghost() == old(thread_map).spec_index(thread_ptr).view_ghost(),
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init()
        && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_map(*thread_map); thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.consume_staged_4k(page_ptr);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thread_map.lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_add_free_quota_pending_4k(thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
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
        final(thread_map).spec_index(thread_ptr).killer_info() == old(thread_map).spec_index(thread_ptr).killer_info(),
        final(thread_map).spec_index(thread_ptr).view_rodata() == old(thread_map).spec_index(thread_ptr).view_rodata(),
        final(thread_map).spec_index(thread_ptr).view_ghost() == old(thread_map).spec_index(thread_ptr).view_ghost(),
        final(thread_map).spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(thread_map).spec_index(thread_ptr).view() }),
        *final(counter) == *old(counter) + 1,
        final(thread_map).spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == *final(counter),
        final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == old(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() + if depth == old(thread_map).spec_index(thread_ptr).view().container_depth { 1int } else { 0int },
        final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(thread_map).spec_index(thread_ptr).view().container_depth { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, *final(counter)) }
            else { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init() && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_map(*thread_map); thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.add_free_quota_pending_4k(depth, counter);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thread_map.lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn thread_map_clear_free_quota_pending_4k(thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, depth: usize, counter: &mut usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>)
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
        final(thread_map).spec_index(thread_ptr).killer_info() == old(thread_map).spec_index(thread_ptr).killer_info(),
        final(thread_map).spec_index(thread_ptr).view_rodata() == old(thread_map).spec_index(thread_ptr).view_rodata(),
        final(thread_map).spec_index(thread_ptr).view_ghost() == old(thread_map).spec_index(thread_ptr).view_ghost(),
        final(thread_map).spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(thread_map).spec_index(thread_ptr).view() }),
        *final(counter) == 0,
        final(thread_map).spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == 0,
        final(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == if depth == old(thread_map).spec_index(thread_ptr).view().container_depth { 0usize } else { old(thread_map).spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() },
        final(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(thread_map).spec_index(thread_ptr).view().container_depth { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, 0usize) }
            else { old(thread_map).spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init() && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_map(*thread_map); thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.clear_free_quota_pending_4k(depth, counter);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thread_map.lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn process_map_add_owned_thread(process_map: &mut ProcessLockedMap, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(process_lock_perm): Tracked<&LockPerm>)
    requires
        process_perms_wf(*old(process_map)),
        old(process_map).dom().contains(process_ptr),
        old(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == lctx.thread_id(),
        process_lock_perm.lock_id() == old(process_map).spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(process_map).spec_index(process_ptr).view().state.view() is Creating || old(process_map).spec_index(process_ptr).view().state.view() is Running,
        node_perm.is_init(),
        node_perm.addr() == node_addr,
        !old(process_map).spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        old(process_map).spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX,
    ensures
        process_perms_wf(*final(process_map)),
        final(process_map).unchanged_except(old(process_map), process_ptr),
        final(process_map).dom() == old(process_map).dom(),
        forall|ptr: RwLockProcessPtr| #![trigger final(process_map).spec_index(ptr)] old(process_map).dom().contains(ptr) && ptr != process_ptr ==> final(process_map).spec_index(ptr) == old(process_map).spec_index(ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).view().children == old(process_map).spec_index(ptr).view().children
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).view_ghost().subtree_set == old(process_map).spec_index(ptr).view_ghost().subtree_set
                &&& final(process_map).spec_index(ptr).view_ghost().owned_pci_functions == old(process_map).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
            },
        final(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(process_map).spec_index(process_ptr).view() == (Process { owned_threads: final(process_map).spec_index(process_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..old(process_map).spec_index(process_ptr).view() }),
        final(process_map).spec_index(process_ptr).view().owned_threads.view() == old(process_map).spec_index(process_ptr).view().owned_threads.view().push(thread_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.dom() == old(process_map).spec_index(process_ptr).view().owned_threads.dom().insert(node_addr),
        final(process_map).spec_index(process_ptr).view().owned_threads.map() == old(process_map).spec_index(process_ptr).view().owned_threads.map().insert(node_addr, thread_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.length == old(process_map).spec_index(process_ptr).view().owned_threads.length + 1,
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
        && process_map.spec_index(process_ptr).inv()) by { process_perms_wf_map(*process_map); process_perms_wf_at(*process_map, process_ptr); };
    let process = process_map.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(process_lock_perm));
    process.add_owned_thread(thread_ptr, node_addr, node_perm);
    proof {
        assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
        assert(process_map.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn scheduler_map_enqueue_scheduled_thread(
    scheduler_map: &mut SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(shard_lock_perm): Tracked<&LockPerm>,
)
    requires
        scheduler_perms_wf(*old(scheduler_map)),
        old(scheduler_map).dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        old(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        shard_lock_perm.state() is WriteLock,
        shard_lock_perm.thread_id() == lctx.thread_id(),
        shard_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == thread_ptr,
        !old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(thread_ptr),
        old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.length != usize::MAX,
    ensures
        scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).perms_wf(),
        final(scheduler_map).spec_index(scheduler_ptr).inv(),
        final(scheduler_map).unchanged_except(old(scheduler_map), scheduler_ptr),
        final(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(scheduler_map).spec_index(scheduler_ptr).owning_container == old(scheduler_map).spec_index(scheduler_ptr).owning_container,
        final(scheduler_map).spec_index(scheduler_ptr).shards.entries_unchanged_except(&old(scheduler_map).spec_index(scheduler_ptr).shards, cpu_id),
        final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread(),
        final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed(),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view().push(thread_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().insert(node_addr, thread_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom().insert(node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.length == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.length + 1,
        !old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom().contains(node_addr),
        !old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().dom().contains(node_addr),
        scheduler_shards_of(final(scheduler_map).spec_index(scheduler_ptr))
            == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].push(thread_ptr)),
{
    proof { scheduler_perms_wf_map(*scheduler_map); scheduler_perms_wf_at(*scheduler_map, scheduler_ptr); }
    let shard = scheduler_map.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(shard_lock_perm));
    shard.queue.push_tail(node_addr, node_perm);
    proof {
        assert(scheduler_perms_wf(*scheduler_map) && scheduler_map.perms_wf() && scheduler_map.spec_index(scheduler_ptr).inv()) by { reveal(scheduler_perms_wf); };
        assert(scheduler_shards_of(scheduler_map.spec_index(scheduler_ptr))
            == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].push(thread_ptr))) by {
            reveal(scheduler_shards_of);
            assert_seqs_equal!(scheduler_shards_of(scheduler_map.spec_index(scheduler_ptr))
                == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].push(thread_ptr)));
        };
    }
}

/// Removes the thread at `node_addr` from anywhere in shard `cpu_id` of `scheduler_ptr` and returns its node.
pub fn scheduler_map_remove_scheduled_thread(scheduler_map: &mut SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, node_addr: usize, Tracked(lctx): Tracked<&LocalContext>, Tracked(shard_lock_perm): Tracked<&LockPerm>)
    -> (ret: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
    requires
        scheduler_perms_wf(*old(scheduler_map)),
        old(scheduler_map).dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        old(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        shard_lock_perm.state() is WriteLock,
        shard_lock_perm.thread_id() == lctx.thread_id(),
        shard_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom().contains(node_addr),
    ensures
        scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).unchanged_except(old(scheduler_map), scheduler_ptr),
        final(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(scheduler_map).spec_index(scheduler_ptr).owning_container == old(scheduler_map).spec_index(scheduler_ptr).owning_container,
        final(scheduler_map).spec_index(scheduler_ptr).shards.entries_unchanged_except(&old(scheduler_map).spec_index(scheduler_ptr).shards, cpu_id),
        final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread(),
        final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed(),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view().remove_value(old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().spec_index(node_addr)),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().remove(node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom().remove(node_addr),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.length == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.length - 1,
        ret.view().is_init(),
        ret.view().addr() == node_addr,
        ret.view().value().view() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().spec_index(node_addr),
        scheduler_shards_of(final(scheduler_map).spec_index(scheduler_ptr)) == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int,
            scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].remove_value(old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().spec_index(node_addr))),
{
    proof { scheduler_perms_wf_map(*scheduler_map); scheduler_perms_wf_at(*scheduler_map, scheduler_ptr); }
    let shard = scheduler_map.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(shard_lock_perm));
    let (_, node_perm) = shard.queue.remove(node_addr);
    proof {
        let thread_ptr = old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().spec_index(node_addr);
        assert(scheduler_perms_wf(*scheduler_map)) by { reveal(scheduler_perms_wf); };
        assert(scheduler_shards_of(scheduler_map.spec_index(scheduler_ptr)) == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].remove_value(thread_ptr))) by {
            reveal(scheduler_shards_of);
            assert_seqs_equal!(scheduler_shards_of(scheduler_map.spec_index(scheduler_ptr))
                == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].remove_value(thread_ptr)));
        };
    }
    node_perm
}

/// Moves the head of shard `from` of `scheduler_ptr` to the tail of shard `to` and returns the head's node address.
pub fn scheduler_map_move_shard_head(scheduler_map: &mut SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr, from: CpuId, to: CpuId, Tracked(lctx): Tracked<&LocalContext>, Tracked(from_lock_perm): Tracked<&LockPerm>, Tracked(to_lock_perm): Tracked<&LockPerm>) -> (ret: usize)
    requires
        scheduler_perms_wf(*old(scheduler_map)),
        old(scheduler_map).dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, from),
        index_valid(NUM_CPUS, to),
        from != to,
        old(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, from), TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, to), TypedLockMode::Write),
        from_lock_perm.state() is WriteLock,
        from_lock_perm.thread_id() == lctx.thread_id(),
        from_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(from).view().locking_thread()->Write_lock_id,
        to_lock_perm.state() is WriteLock,
        to_lock_perm.thread_id() == lctx.thread_id(),
        to_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(to).view().locking_thread()->Write_lock_id,
        old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view().len() > 0,
        !old(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.view().contains(old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view()[0]),
        old(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.length != usize::MAX,
    ensures
        scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).unchanged_except(old(scheduler_map), scheduler_ptr),
        final(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(scheduler_map).spec_index(scheduler_ptr).owning_container == old(scheduler_map).spec_index(scheduler_ptr).owning_container,
        forall|c: CpuId| #![trigger final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(c)]
            index_valid(NUM_CPUS, c) && c != from && c != to ==> final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(c) == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(c),
        forall|c: CpuId| #![trigger final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(c)]
            index_valid(NUM_CPUS, c) && (c == from || c == to) ==> {
                let shard_before = old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(c).view();
                let shard_after = final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(c).view();
                &&& shard_after.is_init() == shard_before.is_init()
                &&& shard_after.view_rodata() == shard_before.view_rodata()
                &&& shard_after.view_ghost() == shard_before.view_ghost()
                &&& shard_after.being_killed() == shard_before.being_killed()
                &&& shard_after.locking_thread() == shard_before.locking_thread()
            },
        old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.map().dom().contains(ret),
        old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.map().spec_index(ret) == old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view()[0],
        final(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view() == old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view().skip(1),
        final(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.map() == old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.map().remove(ret),
        final(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.dom() == old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.dom().remove(ret),
        final(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.view() == old(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.view().push(old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view()[0]),
        final(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.map() == old(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.map().insert(ret, old(scheduler_map).spec_index(scheduler_ptr).shard(from).queue.view()[0]),
        final(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.dom() == old(scheduler_map).spec_index(scheduler_ptr).shard(to).queue.dom().insert(ret),
{
    proof { scheduler_perms_wf_map(*scheduler_map); scheduler_perms_wf_at(*scheduler_map, scheduler_ptr); scheduler_map.spec_index(scheduler_ptr).shard(from).queue.lemma_len_view(); }
    let shard = scheduler_map.borrow_mut_shard_typed(scheduler_ptr, from, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(from_lock_perm));
    let (node_addr, node_perm) = shard.queue.pop_head();
    let shard = scheduler_map.borrow_mut_shard_typed(scheduler_ptr, to, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(to_lock_perm));
    shard.queue.push_tail(node_addr, node_perm);
    proof { assert(scheduler_perms_wf(*scheduler_map)) by { reveal(scheduler_perms_wf); }; }
    node_addr
}

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

/// Moves `bdf` from `sender`'s to `receiver`'s ghost PCI set; the held root-table lock serializes both sets.
pub proof fn process_map_move_pci_function(
    tracked process_map: &mut ProcessLockedMap, sender: RwLockProcessPtr, receiver: RwLockProcessPtr, bdf: PciBdf,
    held_locks: Map<RwLockProcessPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        process_perms_wf(*old(process_map)),
        old(process_map).dom().contains(sender),
        old(process_map).dom().contains(receiver),
        sender != receiver,
    ensures
        process_perms_wf(*final(process_map)),
        final(process_map).perms_wf(),
        final(process_map).dom() == old(process_map).dom(),
        old(process_map).typed_lock_map_aligned(held_locks, thread_id) ==> final(process_map).typed_lock_map_aligned(held_locks, thread_id),
        forall|key: RwLockProcessPtr| #![trigger old(process_map).spec_index(key)] #![trigger final(process_map).spec_index(key)] old(process_map).dom().contains(key) ==> {
            let before = old(process_map).spec_index(key);
            let after = final(process_map).spec_index(key);
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
    process_perms_wf_map(*process_map);
    let ghost sender_ghost = process_map.spec_index(sender).view_ghost();
    process_map.update_ghost(sender, ProcessGhost { owned_pci_functions: Ghost(sender_ghost.owned_pci_functions.view().remove(bdf)), ..sender_ghost });
    let ghost receiver_ghost = process_map.spec_index(receiver).view_ghost();
    process_map.update_ghost(receiver, ProcessGhost { owned_pci_functions: Ghost(receiver_ghost.owned_pci_functions.view().insert(bdf)), ..receiver_ghost });
    assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
    assert(old(process_map).typed_lock_map_aligned(held_locks, thread_id) ==> process_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
}

pub fn pcid_allocator_map_alloc(allocator_map: &mut PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr, process_ptr: RwLockProcessPtr, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, Tracked(allocator_lock_perm): Tracked<&LockPerm>)
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
        final(allocator_map).spec_index(allocator_ptr).view().alloc_ensures(&old(allocator_map).spec_index(allocator_ptr).view(), process_ptr, pcid),
        final(allocator_map).spec_index(allocator_ptr).locking_thread() == old(allocator_map).spec_index(allocator_ptr).locking_thread(),
        final(allocator_map).spec_index(allocator_ptr).being_killed() == old(allocator_map).spec_index(allocator_ptr).being_killed(),
        final(allocator_map).spec_index(allocator_ptr).inv(),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(allocator_map).view().spec_index(ptr).is_init()]
            old(allocator_map).dom().contains(ptr) ==> {
                &&& final(allocator_map).view().spec_index(ptr).is_init() == old(allocator_map).view().spec_index(ptr).is_init()
                &&& final(allocator_map).view().spec_index(ptr).addr() == old(allocator_map).view().spec_index(ptr).addr()
            },
{
    assert(allocator_map.perms_wf() && allocator_map.spec_index(allocator_ptr).is_init()
        && allocator_map.spec_index(allocator_ptr).inv()) by { pcid_allocator_perms_wf_map(*allocator_map); pcid_allocator_perms_wf_at(*allocator_map, allocator_ptr); };
    let allocator = allocator_map.borrow_mut_typed(allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(lctx), Tracked(allocator_lock_perm));
    allocator.alloc(pcid, process_ptr);
    proof {
        assert(pcid_allocator_perms_wf(*allocator_map)) by { reveal(pcid_allocator_perms_wf); };
        assert(allocator_map.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn pcid_allocator_map_release(allocator_map: &mut PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr, process_ptr: RwLockProcessPtr, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, Tracked(allocator_lock_perm): Tracked<&LockPerm>)
    requires
        pcid_allocator_perms_wf(*old(allocator_map)),
        old(allocator_map).dom().contains(allocator_ptr),
        old(allocator_map).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pcid_allocator_lock_map(), allocator_ptr, TypedLockMode::Write),
        allocator_lock_perm.state() is WriteLock,
        allocator_lock_perm.thread_id() == lctx.thread_id(),
        allocator_lock_perm.lock_id() == old(allocator_map).spec_index(allocator_ptr).locking_thread()->Write_lock_id,
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(allocator_map).spec_index(allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(process_ptr),
    ensures
        pcid_allocator_perms_wf(*final(allocator_map)),
        final(allocator_map).perms_wf(),
        final(allocator_map).unchanged_except(old(allocator_map), allocator_ptr),
        final(allocator_map).dom() == old(allocator_map).dom(),
        final(allocator_map).typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id()),
        final(allocator_map).spec_index(allocator_ptr).view().release_ensures(&old(allocator_map).spec_index(allocator_ptr).view(), process_ptr, pcid),
        final(allocator_map).spec_index(allocator_ptr).locking_thread() == old(allocator_map).spec_index(allocator_ptr).locking_thread(),
        final(allocator_map).spec_index(allocator_ptr).being_killed() == old(allocator_map).spec_index(allocator_ptr).being_killed(),
        final(allocator_map).spec_index(allocator_ptr).inv(),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(allocator_map).view().spec_index(ptr).is_init()]
            old(allocator_map).dom().contains(ptr) ==> {
                &&& final(allocator_map).view().spec_index(ptr).is_init() == old(allocator_map).view().spec_index(ptr).is_init()
                &&& final(allocator_map).view().spec_index(ptr).addr() == old(allocator_map).view().spec_index(ptr).addr()
            },
{
    assert(allocator_map.perms_wf() && allocator_map.spec_index(allocator_ptr).is_init()
        && allocator_map.spec_index(allocator_ptr).inv()) by { pcid_allocator_perms_wf_map(*allocator_map); pcid_allocator_perms_wf_at(*allocator_map, allocator_ptr); };
    let allocator = allocator_map.borrow_mut_typed(allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(lctx), Tracked(allocator_lock_perm));
    allocator.release(pcid, process_ptr);
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
        final(process_map).spec_index(child_ptr).view() == (Process { parent_linkedlist_node: final(process_map).spec_index(child_ptr).view().parent_linkedlist_node, ..old(process_map).spec_index(child_ptr).view() }),
        !final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.is_init(),
        final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr() == old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        final(process_map).spec_index(parent_ptr).view() == (Process { children: final(process_map).spec_index(parent_ptr).view().children, ..old(process_map).spec_index(parent_ptr).view() }),
        final(process_map).spec_index(parent_ptr).view().children.view() == old(process_map).spec_index(parent_ptr).view().children.view().push(child_ptr),
        final(process_map).spec_index(parent_ptr).view().children.dom() == old(process_map).spec_index(parent_ptr).view().children.dom().insert(final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        final(process_map).spec_index(parent_ptr).view().children.map() == old(process_map).spec_index(parent_ptr).view().children.map().insert(final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(), child_ptr),
        !old(process_map).spec_index(parent_ptr).view().children.map().dom().contains(final(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).is_init() == old(process_map).spec_index(ptr).is_init()
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).view_ghost().owned_pci_functions == old(process_map).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(process_map).spec_index(ptr).locking_thread() == old(process_map).spec_index(ptr).locking_thread()
                &&& final(process_map).spec_index(ptr).being_killed() == old(process_map).spec_index(ptr).being_killed()
                &&& ptr != parent_ptr && ptr != child_ptr ==> final(process_map).spec_index(ptr).view() == old(process_map).spec_index(ptr).view()
                &&& ptr != parent_ptr && ptr != child_ptr ==> final(process_map).spec_index(ptr).killer_info() == old(process_map).spec_index(ptr).killer_info()
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr).view_ghost().subtree_set]
            old(process_map).dom().contains(ptr) ==> {
                &&& ancestors.to_set().contains(ptr) ==> final(process_map).spec_index(ptr).view_ghost().subtree_set.view() == old(process_map).spec_index(ptr).view_ghost().subtree_set.view().insert(child_ptr)
                &&& !ancestors.to_set().contains(ptr) ==> final(process_map).spec_index(ptr).view_ghost().subtree_set == old(process_map).spec_index(ptr).view_ghost().subtree_set
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).view().spec_index(ptr).is_init()]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).view().spec_index(ptr).is_init() == old(process_map).view().spec_index(ptr).is_init()
                &&& final(process_map).view().spec_index(ptr).addr() == old(process_map).view().spec_index(ptr).addr()
            },
{
    assert(process_map.perms_wf() && process_map.spec_index(child_ptr).is_init()
        && process_map.spec_index(child_ptr).inv()) by { process_perms_wf_map(*process_map); process_perms_wf_at(*process_map, child_ptr); };
    let child = process_map.borrow_mut_typed(child_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(child_lock_perm));
    let (child_node_addr, child_node_perm) = child.parent_linkedlist_node.take();
    proof {
        assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
        assert(process_map.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(process_map.perms_wf() && process_map.spec_index(parent_ptr).is_init()
            && process_map.spec_index(parent_ptr).inv()) by { process_perms_wf_at(*process_map, parent_ptr); };
    }
    let parent = process_map.borrow_mut_typed(parent_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(parent_lock_perm));
    parent.add_child(child_ptr, child_node_addr, child_node_perm);
    proof {
        assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); seq_push_unique_lemma::<RwLockProcessPtr>(); };
        assert(process_map.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        process_insert_child_into_ancestor_subtree_sets(process_map, ancestors, child_ptr, lctx.process_lock_map(), lctx.thread_id());
    }
}

/// Unlinks the retired leaf `child_ptr` from its write-held parent's child list and every ancestor's subtree set.
pub fn process_map_unlink_child(
    process_map: &mut ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
    Ghost(ancestors): Ghost<Seq<RwLockProcessPtr>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(child_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PointsTo<Node<RwLockProcessPtr>>>)
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
        old(process_map).spec_index(parent_ptr).view().children.map().dom().contains(old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        old(process_map).spec_index(parent_ptr).view().children.map().spec_index(old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr,
        ancestors == old(process_map).spec_index(child_ptr).view_ghost().uppertree_seq.view(),
        ancestors.to_set().subset_of(old(process_map).dom()),
        ancestors.no_duplicates(),
    ensures
        process_perms_wf(*final(process_map)),
        final(process_map).perms_wf(),
        final(process_map).spec_index(parent_ptr).inv(),
        final(process_map).dom() == old(process_map).dom(),
        final(process_map).typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        final(process_map).spec_index(parent_ptr).view() == (Process { children: final(process_map).spec_index(parent_ptr).view().children, ..old(process_map).spec_index(parent_ptr).view() }),
        final(process_map).spec_index(parent_ptr).view().children.view() == old(process_map).spec_index(parent_ptr).view().children.view().remove_value(child_ptr),
        final(process_map).spec_index(parent_ptr).view().children.dom() == old(process_map).spec_index(parent_ptr).view().children.dom().remove(old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        final(process_map).spec_index(parent_ptr).view().children.map() == old(process_map).spec_index(parent_ptr).view().children.map().remove(old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr()),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).is_init() == old(process_map).spec_index(ptr).is_init()
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).view_ghost().owned_pci_functions == old(process_map).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(process_map).spec_index(ptr).locking_thread() == old(process_map).spec_index(ptr).locking_thread()
                &&& final(process_map).spec_index(ptr).being_killed() == old(process_map).spec_index(ptr).being_killed()
                &&& final(process_map).spec_index(ptr).killer_info() == old(process_map).spec_index(ptr).killer_info()
                &&& ptr != parent_ptr ==> final(process_map).spec_index(ptr).view() == old(process_map).spec_index(ptr).view()
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr).view_ghost().subtree_set]
            old(process_map).dom().contains(ptr) ==> {
                &&& ancestors.to_set().contains(ptr) ==> final(process_map).spec_index(ptr).view_ghost().subtree_set.view() == old(process_map).spec_index(ptr).view_ghost().subtree_set.view().remove(child_ptr)
                &&& !ancestors.to_set().contains(ptr) ==> final(process_map).spec_index(ptr).view_ghost().subtree_set == old(process_map).spec_index(ptr).view_ghost().subtree_set
            },
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).view().spec_index(ptr).is_init()]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).view().spec_index(ptr).is_init() == old(process_map).view().spec_index(ptr).is_init()
                &&& final(process_map).view().spec_index(ptr).addr() == old(process_map).view().spec_index(ptr).addr()
            },
        ret.view().is_init(),
        ret.view().addr() == old(process_map).spec_index(child_ptr).view().parent_linkedlist_node.addr(),
        ret.view().value().view() == child_ptr,
{
    assert(process_map.perms_wf() && process_map.spec_index(child_ptr).is_init()) by { process_perms_wf_map(*process_map); process_perms_wf_at(*process_map, child_ptr); };
    let node_addr = process_map.borrow_typed(child_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(child_lock_perm)).parent_linkedlist_node.addr();
    assert(process_map.spec_index(parent_ptr).is_init() && process_map.spec_index(parent_ptr).inv() && process_map.spec_index(parent_ptr).view().children.dom().contains(node_addr)) by {
        process_perms_wf_at(*process_map, parent_ptr); process_map.spec_index(parent_ptr).view().children.wf_map_at(node_addr);
    };
    let parent = process_map.borrow_mut_typed(parent_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(parent_lock_perm));
    let node_perm = parent.remove_child(node_addr);
    proof {
        assert(process_map.spec_index(parent_ptr).view().children.view().no_duplicates()) by { reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
        assert(process_perms_wf(*process_map)) by { reveal(process_perms_wf); lemma_seq_remove_value_membership::<RwLockProcessPtr>(); };
        process_remove_child_from_ancestor_subtree_sets(process_map, ancestors, child_ptr, lctx.process_lock_map(), lctx.thread_id());
    }
    node_perm
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

proof fn process_subsystem_create_scheduled_thread_eof_process_thread_wf(
    pre_process: ProcessLockedMap, post_process: ProcessLockedMap, pre_thread: ThreadLockedMap,
    post_thread: ThreadLockedMap, pre_scheduler: SchedulerUnLockedMap,
    post_scheduler: SchedulerUnLockedMap, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thread_value: Thread, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        process_thread_wf(pre_process, pre_thread),
        process_perms_wf(post_process),
        pre_process.dom().contains(process_ptr),
        !pre_process.spec_index(process_ptr).view().zombie,
        !pre_process.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr),
        process_subsystem_create_scheduled_thread_eof_transition_framing(pre_process, post_process, pre_thread, post_thread, pre_scheduler, post_scheduler, pre_lctx, post_lctx,
            page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, cpu_id, thread_value, process_node_addr, sched_node_addr),
        !pre_thread.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        !pre_process.spec_index(process_ptr).view().owned_threads.dom().contains(process_node_addr),
        !pre_process.spec_index(process_ptr).view().owned_threads.map().dom().contains(process_node_addr),
        thread_value.owning_proc == process_ptr,
        thread_value.process_depth == pre_process.spec_index(process_ptr).view_rodata().view().depth,
        thread_value.owning_container == pre_process.spec_index(process_ptr).view_rodata().view().owning_container,
        thread_value.container_depth == pre_process.spec_index(process_ptr).view_rodata().view().container_depth,
        thread_value.proc_pagetable_ptr == pre_process.spec_index(process_ptr).view().pagetable,
        thread_value.proc_linkedlist_node.addr() == process_node_addr,
        !thread_value.proc_linkedlist_node.is_init(),
    ensures
        process_thread_wf(post_process, post_thread),
{
    reveal(process_subsystem_create_scheduled_thread_eof_transition_framing);
    reveal(process_thread_wf);
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
}

proof fn process_subsystem_create_scheduled_thread_eof_scheduler_wf(
    container_map: ContainerLockedMap, pre_process: ProcessLockedMap, post_process: ProcessLockedMap,
    pre_thread: ThreadLockedMap, post_thread: ThreadLockedMap, pre_scheduler: SchedulerUnLockedMap,
    post_scheduler: SchedulerUnLockedMap, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thread_value: Thread, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        container_thread_scheduler_wf(container_map, pre_thread, pre_scheduler),
        container_thread_wf(container_map, pre_thread),
        container_scheduler_wf(container_map, pre_scheduler),
        container_map.dom().contains(container_ptr),
        pre_scheduler.dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        !pre_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(page_ptr),
        process_subsystem_create_scheduled_thread_eof_transition_framing(pre_process, post_process, pre_thread, post_thread, pre_scheduler, post_scheduler, pre_lctx, post_lctx,
            page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, cpu_id, thread_value, process_node_addr, sched_node_addr),
        !pre_thread.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        !pre_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.dom().contains(sched_node_addr),
        !pre_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.map().dom().contains(sched_node_addr),
        thread_value.state == (ThreadState::SCHEDULED { cpu_id }),
        thread_value.owning_container == container_ptr,
        thread_value.scheduler_linkedlist_node.addr() == sched_node_addr,
    ensures
        container_thread_scheduler_wf(container_map, post_thread, post_scheduler),
        forall|t_ptr: RwLockThreadPtr| #![trigger post_thread.dom().contains(t_ptr)] post_thread.dom().contains(t_ptr) ==> container_map.dom().contains(post_thread.spec_index(t_ptr).view().owning_container),
        forall|c_ptr: RwLockContainerPtr| #![trigger container_map.dom().contains(c_ptr)] container_map.dom().contains(c_ptr) ==> post_scheduler.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler),
{
    reveal(process_subsystem_create_scheduled_thread_eof_transition_framing);
    reveal(container_thread_scheduler_wf);
    reveal(container_thread_wf);
    reveal(container_scheduler_wf);
    seq_push_lemma::<RwLockThreadPtr>();
}

pub fn process_subsystem_create_scheduled_thread(
    container_map: &ContainerLockedMap, process_map: &mut ProcessLockedMap, thread_map: &mut ThreadLockedMap,
    scheduler_map: &mut SchedulerUnLockedMap, page_ptr: PagePtr, process_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId,
    thread_value: Thread, initial_regs: &Registers, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(shard_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<LockPerm>, usize, usize))
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
        old(scheduler_map).spec_index(scheduler_ptr).owning_container == container_ptr,
        index_valid(NUM_CPUS, cpu_id),
        old(process_map).spec_index(process_ptr).view().state.view() is Creating || old(process_map).spec_index(process_ptr).view().state.view() is Running,
        !old(process_map).spec_index(process_ptr).view().owned_threads.view().contains(page_ptr),
        old(process_map).spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX,
        !old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(page_ptr),
        old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.length != usize::MAX,
        old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![page_ptr],
        old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(thread_map).spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        old(thread_map).spec_index(staging_thread_ptr).view().quota_4k >= 1,
        thread_value.inv(),
        thread_value.state is RUNNING,
        thread_value.scheduler_linkedlist_node.is_init(),
        thread_value.proc_linkedlist_node.is_init(),
        thread_value.owning_container == container_ptr,
        thread_value.container_depth == container_map.spec_index(container_ptr).view_rodata().view().depth,
        thread_value.container_depth == old(process_map).spec_index(process_ptr).view_rodata().view().container_depth,
        thread_value.owning_proc == process_ptr,
        thread_value.process_depth == old(process_map).spec_index(process_ptr).view_rodata().view().depth,
        thread_value.proc_pagetable_ptr == old(process_map).spec_index(process_ptr).view().pagetable,
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        old(process_map).typed_lock_map_aligned(old(lctx).process_lock_map(), old(lctx).thread_id()),
        old(thread_map).typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id()),
        old(scheduler_map).typed_shard_lock_map_aligned(old(lctx).scheduler_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(process_map).spec_index(process_ptr).locking_thread()->Write_lock_id,
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(thread_map).spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        shard_lock_perm.state() is WriteLock,
        shard_lock_perm.thread_id() == old(lctx).thread_id(),
        shard_lock_perm.lock_id() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        process_perms_wf(*final(process_map)),
        thread_perms_wf(*final(thread_map)),
        scheduler_perms_wf(*final(scheduler_map)),
        process_subsystem_create_scheduled_thread_eof_transition_framing(*old(process_map), *final(process_map), *old(thread_map), *final(thread_map),
            *old(scheduler_map), *final(scheduler_map), old(lctx), final(lctx), page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, cpu_id, final(thread_map).spec_index(page_ptr).view(), ret.2, ret.1),
        process_thread_wf(*final(process_map), *final(thread_map)),
        container_thread_scheduler_wf(*container_map, *final(thread_map), *final(scheduler_map)),
        forall|t_ptr: RwLockThreadPtr| #![trigger final(thread_map).dom().contains(t_ptr)] final(thread_map).dom().contains(t_ptr) ==> container_map.dom().contains(final(thread_map).spec_index(t_ptr).view().owning_container),
        forall|c_ptr: RwLockContainerPtr| #![trigger container_map.dom().contains(c_ptr)] container_map.dom().contains(c_ptr) ==> final(scheduler_map).dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler),
        final(process_map).dom() == old(process_map).dom(),
        final(thread_map).dom() =~= old(thread_map).dom().insert(page_ptr),
        forall|t: RwLockThreadPtr| #![trigger final(thread_map).spec_index(t)]
            old(thread_map).dom().contains(t) ==> final(thread_map).spec_index(t).view().endpoint_descriptors.view() == old(thread_map).spec_index(t).view().endpoint_descriptors.view(),
        final(thread_map).spec_index(page_ptr).view() == (Thread { state: ThreadState::SCHEDULED { cpu_id }, last_cpu: cpu_id, trap_frame: final(thread_map).spec_index(page_ptr).view().trap_frame,
            scheduler_linkedlist_node: final(thread_map).spec_index(page_ptr).view().scheduler_linkedlist_node,
            proc_linkedlist_node: final(thread_map).spec_index(page_ptr).view().proc_linkedlist_node, ..thread_value }),
        final(thread_map).spec_index(page_ptr).view().trap_frame.is_some(),
        *final(thread_map).spec_index(page_ptr).view().trap_frame.get_some_0() == *initial_regs,
        !final(thread_map).spec_index(page_ptr).view().scheduler_linkedlist_node.is_init(),
        !final(thread_map).spec_index(page_ptr).view().proc_linkedlist_node.is_init(),
        ret.1 == final(thread_map).spec_index(page_ptr).view().scheduler_linkedlist_node.addr(),
        ret.2 == final(thread_map).spec_index(page_ptr).view().proc_linkedlist_node.addr(),
        final(thread_map).spec_index(page_ptr).is_init(),
        final(thread_map).spec_index(page_ptr).inv(),
        final(thread_map).spec_index(page_ptr).being_killed() == false,
        final(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() == old(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
        final(thread_map).spec_index(staging_thread_ptr).view().quota_4k == old(thread_map).spec_index(staging_thread_ptr).view().quota_4k - 1,
        final(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_clean(),
        final(thread_map).spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        final(thread_map).spec_index(staging_thread_ptr).view() == (Thread { quota_4k: final(thread_map).spec_index(staging_thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(thread_map).spec_index(staging_thread_ptr).view().temp_alloc_cache_4k, ..old(thread_map).spec_index(staging_thread_ptr).view() }),
        final(thread_map).spec_index(staging_thread_ptr).being_killed() == old(thread_map).spec_index(staging_thread_ptr).being_killed(),
        final(thread_map).spec_index(staging_thread_ptr).killer_info() == old(thread_map).spec_index(staging_thread_ptr).killer_info(),
        final(thread_map).spec_index(staging_thread_ptr).view_ghost() == old(thread_map).spec_index(staging_thread_ptr).view_ghost(),
        final(thread_map).spec_index(staging_thread_ptr).locking_thread() == old(thread_map).spec_index(staging_thread_ptr).locking_thread(),
        final(thread_map).lock_id_by_key(staging_thread_ptr) == old(thread_map).lock_id_by_key(staging_thread_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.view() == old(process_map).spec_index(process_ptr).view().owned_threads.view().push(page_ptr),
        final(process_map).spec_index(process_ptr).view().owned_threads.dom() == old(process_map).spec_index(process_ptr).view().owned_threads.dom().insert(ret.2),
        final(process_map).spec_index(process_ptr).view().owned_threads.map() == old(process_map).spec_index(process_ptr).view().owned_threads.map().insert(ret.2, page_ptr),
        !old(process_map).spec_index(process_ptr).view().owned_threads.dom().contains(ret.2),
        !old(process_map).spec_index(process_ptr).view().owned_threads.map().dom().contains(ret.2),
        final(process_map).spec_index(process_ptr).view() == (Process { owned_threads: final(process_map).spec_index(process_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..old(process_map).spec_index(process_ptr).view() }),
        final(process_map).spec_index(process_ptr).view_rodata() == old(process_map).spec_index(process_ptr).view_rodata(),
        final(process_map).spec_index(process_ptr).being_killed() == old(process_map).spec_index(process_ptr).being_killed(),
        final(process_map).spec_index(process_ptr).locking_thread() == old(process_map).spec_index(process_ptr).locking_thread(),
        final(process_map).lock_id_by_key(process_ptr) == old(process_map).lock_id_by_key(process_ptr),
        final(scheduler_map).unchanged_except(old(scheduler_map), scheduler_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).owning_container == old(scheduler_map).spec_index(scheduler_ptr).owning_container,
        final(scheduler_map).spec_index(scheduler_ptr).shards.entries_unchanged_except(&old(scheduler_map).spec_index(scheduler_ptr).shards, cpu_id),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.view().push(page_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom().insert(ret.1),
        final(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map() == old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().insert(ret.1, page_ptr),
        !old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.dom().contains(ret.1),
        !old(scheduler_map).spec_index(scheduler_ptr).shard(cpu_id).queue.map().dom().contains(ret.1),
        final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed(),
        final(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread() == old(scheduler_map).spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread(),
        scheduler_shards_of(final(scheduler_map).spec_index(scheduler_ptr))
            == scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(old(scheduler_map).spec_index(scheduler_ptr))[cpu_id as int].push(page_ptr)),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(process_map).spec_index(ptr)]
            old(process_map).dom().contains(ptr) ==> {
                &&& final(process_map).spec_index(ptr).view().children == old(process_map).spec_index(ptr).view().children
                &&& final(process_map).spec_index(ptr).view_ghost().uppertree_seq == old(process_map).spec_index(ptr).view_ghost().uppertree_seq
                &&& final(process_map).spec_index(ptr).view_ghost().subtree_set == old(process_map).spec_index(ptr).view_ghost().subtree_set
                &&& final(process_map).spec_index(ptr).view_ghost().owned_pci_functions == old(process_map).spec_index(ptr).view_ghost().owned_pci_functions
                &&& final(process_map).spec_index(ptr).view_rodata() == old(process_map).spec_index(ptr).view_rodata()
            },
        forall|ptr: RwLockProcessPtr| #![trigger final(process_map).spec_index(ptr)] old(process_map).dom().contains(ptr) && ptr != process_ptr ==> final(process_map).spec_index(ptr) == old(process_map).spec_index(ptr),
        forall|ptr: RwLockThreadPtr| #![trigger final(thread_map).spec_index(ptr)] old(thread_map).dom().contains(ptr) && ptr != staging_thread_ptr ==> final(thread_map).spec_index(ptr) == old(thread_map).spec_index(ptr),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(thread_map).spec_index(page_ptr).locking_thread()->Write_lock_id,
        final(thread_map).spec_index(page_ptr).write_lock_perm_match(&ret.0.view()),
        !final(thread_map).spec_index(page_ptr).view_ghost().exited,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(page_ptr), TypedHeldLock { lock_id: final(thread_map).lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(page_ptr, TypedHeldLock { lock_id: final(thread_map).lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(process_map).typed_lock_map_aligned(final(lctx).process_lock_map(), final(lctx).thread_id()),
        final(thread_map).typed_lock_map_aligned(final(lctx).thread_lock_map(), final(lctx).thread_id()),
        final(scheduler_map).typed_shard_lock_map_aligned(final(lctx).scheduler_lock_map(), final(lctx).thread_id()),
{
    thread_map_consume_staged_4k(thread_map, staging_thread_ptr, page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    proof {
        assert(!lctx.thread_lock_map().dom().contains(page_ptr)
            && lctx.typed_lock_entry(KernelObjId::Thread(page_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    let Tracked(thread_lock_perm) = thread_map.retype_4k_and_insert(page_ptr, thread_value, (), Ghost(ThreadGhost { chain_end: None, exited: false }), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)));
    let ghost fresh_lock_id = thread_map.lock_id_by_key(page_ptr);
    proof { assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let thread = thread_map.borrow_mut_typed(page_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let (sched_node_addr, sched_node_perm, process_node_addr, process_node_perm) = thread.fresh_to_scheduled(page_ptr, cpu_id, initial_regs);
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(page_ptr), fresh_lock_id, thread_map.lock_id_by_key(page_ptr));
        assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().insert(page_ptr, TypedHeldLock { lock_id: thread_map.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }));
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    process_map_add_owned_thread(process_map, process_ptr, page_ptr, process_node_addr, process_node_perm, Tracked(&*lctx), Tracked(process_lock_perm));
    scheduler_map_enqueue_scheduled_thread(scheduler_map, scheduler_ptr, cpu_id, page_ptr, sched_node_addr, sched_node_perm, Tracked(&*lctx), Tracked(shard_lock_perm));
    let ghost stored_thread = thread_map.spec_index(page_ptr).view();
    proof {
        assert(process_subsystem_create_scheduled_thread_eof_transition_framing(*old(process_map), *process_map, *old(thread_map), *thread_map, *old(scheduler_map), *scheduler_map,
            old(lctx), &*lctx, page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr)) by { reveal(process_subsystem_create_scheduled_thread_eof_transition_framing); };
        assert(!old(process_map).spec_index(process_ptr).view().zombie) by { process_perms_wf_at(*old(process_map), process_ptr); };
        process_subsystem_create_scheduled_thread_eof_process_thread_wf(*old(process_map), *process_map, *old(thread_map), *thread_map, *old(scheduler_map),
            *scheduler_map, old(lctx), &*lctx, page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr);
        process_subsystem_create_scheduled_thread_eof_scheduler_wf(*container_map, *old(process_map), *process_map, *old(thread_map), *thread_map,
            *old(scheduler_map), *scheduler_map, old(lctx), &*lctx, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, stored_thread, process_node_addr, sched_node_addr);
    }
    (Tracked(thread_lock_perm), sched_node_addr, process_node_addr)
}

pub fn thread_map_consume_new_container_staging(
    threads: &mut ThreadLockedMap, current_thread_ptr: RwLockThreadPtr, thread_page: PagePtr, funding_page_count: usize,
    Ghost(consumed_4k_pages): Ghost<Set<PagePtr>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
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
        final(threads).spec_index(current_thread_ptr).killer_info() == old(threads).spec_index(current_thread_ptr).killer_info(),
        final(threads).spec_index(current_thread_ptr).view_ghost() == old(threads).spec_index(current_thread_ptr).view_ghost(),
        thread_quota_4k_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_2m_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_1g_fields_unchanged(*old(threads), *final(threads)),
        final(threads).spec_index(current_thread_ptr).view() == (Thread { temp_alloc_cache_4k: Ghost(set![thread_page]), temp_alloc_cache_2m: Ghost(Set::empty()),
            quota_4k: (old(threads).spec_index(current_thread_ptr).view().quota_4k as int - 8 - funding_page_count as int) as usize,
            quota_2m: (old(threads).spec_index(current_thread_ptr).view().quota_2m as int - 2) as usize, ..old(threads).spec_index(current_thread_ptr).view() }),
{
    assert(threads.perms_wf() && threads.spec_index(current_thread_ptr).is_init()
        && threads.spec_index(current_thread_ptr).view().inv()) by { thread_perms_wf_map(*threads); thread_perms_wf_at(*threads, current_thread_ptr); };
    let thread = threads.borrow_mut_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(current_thread_lock_perm));
    thread.temp_alloc_cache_4k = Ghost(Set::empty().insert(thread_page));
    thread.temp_alloc_cache_2m = Ghost(Set::empty());
    thread.quota_4k = thread.quota_4k - 8 - funding_page_count;
    thread.quota_2m = thread.quota_2m - 2;
    proof {
        assert(thread_perms_wf(*threads)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        assert(threads.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(thread_quota_4k_fields_unchanged(*old(threads), *threads)) by { vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page); };
    }
}

/// Publishes a fresh scheduler whose shards are all unlocked.
pub fn scheduler_map_insert_new_4k(scheduler_map: &mut SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr, scheduler_value: Scheduler, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&LocalContext>)
    requires
        old(scheduler_map).perms_wf(),
        !old(scheduler_map).dom().contains(scheduler_ptr),
        old(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        scheduler_value.inv(),
        forall|cpu_id: CpuId| #![trigger scheduler_value.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> !scheduler_value.shards.spec_index(cpu_id).view().locked(),
        page_perm.is_init(),
        page_perm.addr() == scheduler_ptr,
    ensures
        final(scheduler_map).perms_wf(),
        scheduler_perms_wf(*old(scheduler_map)) ==> scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).dom() =~= old(scheduler_map).dom().insert(scheduler_ptr),
        forall|ptr: RwLockSchedulerPtr| #![trigger final(scheduler_map).spec_index(ptr)] old(scheduler_map).dom().contains(ptr) ==> final(scheduler_map).spec_index(ptr) == old(scheduler_map).spec_index(ptr),
        final(scheduler_map).spec_index(scheduler_ptr) == scheduler_value,
        final(scheduler_map).typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
{
    scheduler_map.retype_page_to_scheduler_and_insert(scheduler_ptr, scheduler_value, Tracked(page_perm), Tracked(lctx));
    proof {
        assert(scheduler_perms_wf(*old(scheduler_map)) ==> scheduler_perms_wf(*scheduler_map)) by { reveal(scheduler_perms_wf); };
        assert(scheduler_map.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id())) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
    }
}

pub fn cpu_set_map_insert_new_4k(cpu_set_map: &mut CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr, cpu_set_value: CpuSet, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(cpu_set_map).perms_wf(),
        !old(cpu_set_map).dom().contains(cpu_set_ptr),
        old(cpu_set_map).typed_lock_map_aligned(old(lctx).cpu_set_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        cpu_set_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == cpu_set_ptr,
    ensures
        final(cpu_set_map).perms_wf(),
        cpu_set_perms_wf(*old(cpu_set_map)) ==> cpu_set_perms_wf(*final(cpu_set_map)),
        final(cpu_set_map).dom() =~= old(cpu_set_map).dom().insert(cpu_set_ptr),
        forall|ptr: RwLockCpuSetPtr| #![trigger final(cpu_set_map).spec_index(ptr)] old(cpu_set_map).dom().contains(ptr) ==> final(cpu_set_map).spec_index(ptr) == old(cpu_set_map).spec_index(ptr),
        final(cpu_set_map).spec_index(cpu_set_ptr).view() == cpu_set_value,
        final(cpu_set_map).spec_index(cpu_set_ptr).inv(),
        !final(cpu_set_map).spec_index(cpu_set_ptr).being_killed(),
        final(cpu_set_map).spec_index(cpu_set_ptr).write_lock_perm_match(&ret.view()),
        final(cpu_set_map).typed_lock_map_aligned(final(lctx).cpu_set_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), TypedHeldLock { lock_id: final(cpu_set_map).lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::CpuSet(cpu_set_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = cpu_set_map.retype_4k_and_insert(cpu_set_ptr, cpu_set_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
    proof {
        assert(cpu_set_perms_wf(*old(cpu_set_map)) ==> cpu_set_perms_wf(*cpu_set_map)) by { reveal(cpu_set_perms_wf); };
        assert(cpu_set_map.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}

pub fn pcid_allocator_map_insert_new_2m(allocator_map: &mut PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr, allocator_value: PcidAllocator, Tracked(page_perm): Tracked<PagePerm2m>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(allocator_map).perms_wf(),
        !old(allocator_map).dom().contains(allocator_ptr),
        old(allocator_map).typed_lock_map_aligned(old(lctx).pcid_allocator_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        allocator_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == allocator_ptr,
    ensures
        final(allocator_map).perms_wf(),
        pcid_allocator_perms_wf(*old(allocator_map)) ==> pcid_allocator_perms_wf(*final(allocator_map)),
        final(allocator_map).dom() =~= old(allocator_map).dom().insert(allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr| #![trigger final(allocator_map).spec_index(ptr)] old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
        final(allocator_map).spec_index(allocator_ptr).view() == allocator_value,
        final(allocator_map).spec_index(allocator_ptr).is_init(),
        final(allocator_map).spec_index(allocator_ptr).inv(),
        !final(allocator_map).spec_index(allocator_ptr).being_killed(),
        final(allocator_map).spec_index(allocator_ptr).wlocked_by(final(lctx)),
        final(allocator_map).spec_index(allocator_ptr).write_lock_perm_match(&ret.view()),
        final(allocator_map).typed_lock_map_aligned(final(lctx).pcid_allocator_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr), TypedHeldLock { lock_id: final(allocator_map).lock_id_by_key(allocator_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(allocator_map).lock_id_by_key(allocator_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::PcidAllocator(allocator_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = allocator_map.retype_2m_and_insert(allocator_ptr, allocator_value, (), Ghost(()), Tracked(page_perm),
        Tracked(&mut *lctx), Ghost(KernelObjId::PcidAllocator(allocator_ptr)), LockControl::Clear);
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
        assert(container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); lemma_seq_remove_value_membership::<RwLockContainerPtr>(); };
        assert(container_map.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(container_map.perms_wf()) by { container_perms_wf_map(*container_map); };
        container_remove_child_from_ancestor_subtree_sets(container_map, ancestors, child_ptr, lctx.container_lock_map(), lctx.thread_id());
        assert(container_perms_wf(*container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
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

pub fn thread_map_set_endpoint_descriptor(
    thread_map: &mut ThreadLockedMap, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, endpoint_ptr: Option<RwLockEndpointPtr>,
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
        edp_idx_valid(endpoint_index),
        !old(thread_map).spec_index(thread_ptr).view().state.is_endpoint_waiting(),
        !(old(thread_map).spec_index(thread_ptr).view().state is DANGLING),
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).perms_wf(),
        final(thread_map).spec_index(thread_ptr).inv(),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).dom() == old(thread_map).dom(),
        forall|ptr: RwLockThreadPtr| #![trigger final(thread_map).spec_index(ptr)] old(thread_map).dom().contains(ptr) && ptr != thread_ptr ==> final(thread_map).spec_index(ptr) == old(thread_map).spec_index(ptr),
        final(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        final(thread_map).spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: final(thread_map).spec_index(thread_ptr).view().endpoint_descriptors, ..old(thread_map).spec_index(thread_ptr).view() }),
        final(thread_map).spec_index(thread_ptr).view().endpoint_descriptors.view() == old(thread_map).spec_index(thread_ptr).view().endpoint_descriptors.view().update(endpoint_index as int, endpoint_ptr),
        final(thread_map).lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(thread_ptr).killer_info() == old(thread_map).spec_index(thread_ptr).killer_info(),
        final(thread_map).spec_index(thread_ptr).view_ghost() == old(thread_map).spec_index(thread_ptr).view_ghost(),
{
    assert(thread_map.perms_wf() && thread_map.spec_index(thread_ptr).is_init() && thread_map.spec_index(thread_ptr).inv()) by { thread_perms_wf_map(*thread_map); thread_perms_wf_at(*thread_map, thread_ptr); };
    let thread = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_lock_perm));
    thread.endpoint_descriptors.set(endpoint_index, endpoint_ptr);
    proof {
        assert(thread_perms_wf(*thread_map)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        assert(thread_map.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()) && thread_map.lock_id_by_key(thread_ptr) == old(thread_map).lock_id_by_key(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn endpoint_map_insert_new_4k(endpoint_map: &mut EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr, endpoint_value: Endpoint, Tracked(page_perm): Tracked<PagePerm4k>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
    requires
        old(endpoint_map).perms_wf(),
        !old(endpoint_map).dom().contains(endpoint_ptr),
        old(endpoint_map).typed_lock_map_aligned(old(lctx).endpoint_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        endpoint_value.inv(),
        page_perm.is_init(),
        page_perm.addr() == endpoint_ptr,
    ensures
        final(endpoint_map).perms_wf(),
        endpoint_perms_wf(*old(endpoint_map)) ==> endpoint_perms_wf(*final(endpoint_map)),
        final(endpoint_map).dom() =~= old(endpoint_map).dom().insert(endpoint_ptr),
        forall|ptr: RwLockEndpointPtr| #![trigger final(endpoint_map).spec_index(ptr)] old(endpoint_map).dom().contains(ptr) ==> final(endpoint_map).spec_index(ptr) == old(endpoint_map).spec_index(ptr),
        final(endpoint_map).spec_index(endpoint_ptr).view() == endpoint_value,
        final(endpoint_map).spec_index(endpoint_ptr).is_init(),
        final(endpoint_map).spec_index(endpoint_ptr).inv(),
        !final(endpoint_map).spec_index(endpoint_ptr).being_killed(),
        final(endpoint_map).spec_index(endpoint_ptr).wlocked_by(final(lctx)),
        final(endpoint_map).spec_index(endpoint_ptr).write_lock_perm_match(&ret.view()),
        final(endpoint_map).typed_lock_map_aligned(final(lctx).endpoint_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr), TypedHeldLock { lock_id: final(endpoint_map).lock_id_by_key(endpoint_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().ordering_lock_id() == final(endpoint_map).lock_id_by_key(endpoint_ptr),
{
    proof { assert(lctx.typed_lock_entry(KernelObjId::Endpoint(endpoint_ptr)) is None) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    let lock_perm = endpoint_map.retype_4k_and_insert(endpoint_ptr, endpoint_value, (), Ghost(()), Tracked(page_perm), Tracked(&mut *lctx), Ghost(KernelObjId::Endpoint(endpoint_ptr)));
    proof {
        assert(endpoint_perms_wf(*old(endpoint_map)) ==> endpoint_perms_wf(*endpoint_map)) by { reveal(endpoint_perms_wf); };
        assert(endpoint_map.typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    lock_perm
}
}

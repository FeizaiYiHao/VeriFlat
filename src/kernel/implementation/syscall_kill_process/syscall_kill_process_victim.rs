use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_victim_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_victim_eof::*;

verus! {
/// The write-held thread `victim_ptr`, waiting for a reply or killed, leaves the write-held marked process `process_ptr`,
/// which absorbs its quota and hands back its process node; a thread waiting for a reply becomes a dangling thread.
pub(crate) fn kill_leave_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&LocalContext>, process_ptr: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(victim_lock_perm): Tracked<&LockPerm>,
) -> (callers: Ghost<Set<RwLockThreadPtr>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Killing,
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == lctx.thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(victim_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_lock_perm.state() is WriteLock,
        victim_lock_perm.thread_id() == lctx.thread_id(),
        victim_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(victim_ptr).view().state is WAITING_REPLY || old(krnl).thr_mp.spec_index(victim_ptr).view().state is KILLED,
        old(krnl).thr_mp.spec_index(victim_ptr).view().state is KILLED ==> old(krnl).thr_mp.spec_index(victim_ptr).being_killed() && old(krnl).thr_mp.spec_index(victim_ptr).view().caller is None,
        old(krnl).thr_mp.spec_index(victim_ptr).view().temp_alloc_clean(),
        forall|t: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(t)]
            lctx.thread_lock_map().dom().contains(t) ==> !(old(krnl).thr_mp.spec_index(t).view().state is KILLED) || old(krnl).thr_mp.spec_index(t).being_killed(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        kill_leave_process_eof_transition_framing(*old(krnl), *final(krnl), process_ptr, victim_ptr, callers.view()),
        final(krnl).thr_mp.lock_id_by_key(victim_ptr) == old(krnl).thr_mp.lock_id_by_key(victim_ptr),
        final(krnl).prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr),
{
    let ghost pre = *krnl;
    proof {
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, process_ptr);
        assert({
            &&& krnl.thr_mp.dom().contains(victim_ptr)
            &&& krnl.thr_mp.spec_index(victim_ptr).view().owning_proc == process_ptr
            &&& !krnl.thr_mp.spec_index(victim_ptr).view().proc_linkedlist_node.is_init()
        }) by { process_thread_wf_process_at(krnl.prc_mp, krnl.thr_mp, process_ptr, victim_ptr); };
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, victim_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, victim_ptr);
        assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.dom().contains(krnl.thr_mp.spec_index(victim_ptr).view().proc_linkedlist_node.addr())) by {
            krnl.prc_mp.spec_index(process_ptr).view().owned_threads.wf_map_at(krnl.thr_mp.spec_index(victim_ptr).view().proc_linkedlist_node.addr());
        };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, victim_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
        container_process_thread_quota_sums_bounded(&*krnl, krnl.thr_mp.spec_index(victim_ptr).view().owning_container, process_ptr, victim_ptr);
    }
    let (node_addr, quota_4k, quota_2m, quota_1g, waiting_reply) = {
        let victim = krnl.thr_mp.borrow_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(victim_lock_perm));
        (victim.proc_linkedlist_node.addr(), victim.quota_4k, victim.quota_2m, victim.quota_1g, match victim.state { ThreadState::WAITING_REPLY => true, _ => false })
    };
    let node_perm = {
        let process = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(lctx), Tracked(process_lock_perm));
        process.remove_killed_thread(node_addr, quota_4k, quota_2m, quota_1g)
    };
    let ghost mut callers = Set::<RwLockThreadPtr>::empty();
    proof {
        if waiting_reply {
            let victim = pre.thr_mp.spec_index(victim_ptr).view();
            let callee = pre.thr_mp.spec_index(victim.callee.unwrap());
            let end = if thread_is_dangling(callee) && !callee.being_killed() { callee.view_ghost().chain_end.unwrap() } else { victim.callee.unwrap() };
            callers = thread_map_set_chain_end_up_dangling_callers(&mut krnl.thr_mp, victim_ptr, end);
            assert(krnl.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
    }
    {
        let victim = krnl.thr_mp.borrow_mut_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(victim_lock_perm));
        if waiting_reply { victim.waiting_reply_to_dangling(node_perm); } else { victim.killed_leave_process(node_perm); }
    }
    proof {
        assert(kill_leave_process_eof_transition_framing(pre, *krnl, process_ptr, victim_ptr, callers)) by { reveal(kill_leave_process_eof_transition_framing); };
        assert(krnl.inv()) by { reveal(LockedMap::typed_lock_map_aligned); kill_leave_process_eof(pre, *krnl, process_ptr, victim_ptr, callers, lctx.thread_id()); };
    }
    Ghost(callers)
}

/// Take the write-held marked thread `victim_ptr` off the scheduler shard it is queued on and kill it, write-locking and
/// releasing the shard.
pub(crate) fn kill_dequeue_scheduled_victim(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, victim_ptr: RwLockThreadPtr, Tracked(victim_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().state is SCHEDULED,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_lock_perm.state() is WriteLock,
        victim_lock_perm.thread_id() == old(lctx).thread_id(),
        victim_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
            ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED) || old(krnl).thr_mp.spec_index(held_thread).being_killed(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ({
            let victim = old(krnl).thr_mp.spec_index(victim_ptr);
            let container_ptr = victim.view().owning_container;
            let scheduler_ptr = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler;
            let shard = victim.view().state->SCHEDULED_cpu_id;
            let after = final(krnl).thr_mp.spec_index(victim_ptr);
            &&& index_valid(NUM_CPUS, shard)
            &&& old(krnl).ctn_mp.dom().contains(container_ptr)
            &&& *final(krnl) == (KernelK { sched_mp: final(krnl).sched_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).sched_mp.unchanged_except(&old(krnl).sched_mp, scheduler_ptr)
            &&& scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr))
                == scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)).update(shard as int, scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr))[shard as int].remove_value(victim_ptr))
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, victim_ptr)
            &&& after.view() == (Thread { state: ThreadState::KILLED, error_code: None, scheduler_linkedlist_node: after.view().scheduler_linkedlist_node, ..victim.view() })
            &&& after.locking_thread() == victim.locking_thread()
            &&& after.being_killed() == victim.being_killed()
            &&& final(krnl).thr_mp.lock_id_by_key(victim_ptr) == old(krnl).thr_mp.lock_id_by_key(victim_ptr)
        }),
{
    proof {
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, victim_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, victim_ptr);
        container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, krnl.thr_mp.spec_index(victim_ptr).view().owning_container);
        container_perms_wf_at(krnl.ctn_mp, krnl.thr_mp.spec_index(victim_ptr).view().owning_container);
        assert(index_valid(NUM_CPUS, krnl.thr_mp.spec_index(victim_ptr).view().state->SCHEDULED_cpu_id)) by { container_thread_scheduler_wf_thread_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, victim_ptr); };
    }
    let (container_ptr, shard, node_addr) = {
        let victim = krnl.thr_mp.borrow_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_lock_perm));
        let shard = match victim.state { ThreadState::SCHEDULED { cpu_id } => cpu_id, _ => 0 };
        (victim.owning_container, shard, victim.scheduler_linkedlist_node.addr())
    };
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let Tracked(shard_lock_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, shard, Tracked(&mut *lctx));
    let ghost pre = *krnl;
    proof {
        assert(krnl.sched_mp.spec_index(scheduler_ptr).shard(shard).queue.map().dom().contains(node_addr) && krnl.sched_mp.spec_index(scheduler_ptr).shard(shard).queue.map().spec_index(node_addr) == victim_ptr)
            by { container_thread_scheduler_wf_thread_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, victim_ptr); };
        assert(krnl.sched_mp.spec_index(scheduler_ptr).shard(shard).queue.dom().contains(node_addr)) by { scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); krnl.sched_mp.spec_index(scheduler_ptr).shard(shard).queue.wf_map_at(node_addr); };
    }
    let node_perm = scheduler_map_remove_scheduled_thread(&mut krnl.sched_mp, scheduler_ptr, shard, node_addr, Tracked(&*lctx), Tracked(&shard_lock_perm));
    {
        let victim = krnl.thr_mp.borrow_mut_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_lock_perm));
        victim.scheduled_to_killed(node_perm);
    }
    proof {
        assert(kill_dequeue_scheduled_eof_transition_framing(pre, *krnl, victim_ptr, scheduler_ptr, shard)) by { reveal(kill_dequeue_scheduled_eof_transition_framing); };
        kill_dequeue_scheduled_eof(pre, *krnl, victim_ptr, scheduler_ptr, shard);
    }
    krnl.wunlock_scheduler_shard(scheduler_ptr, shard, Tracked(&mut *lctx), Tracked(shard_lock_perm));
    proof { assert(lctx.scheduler_lock_map() =~= old(lctx).scheduler_lock_map()); }
}

/// Take the write-held marked thread `victim_ptr` out of the queue of the endpoint it waits on and kill it,
/// write-locking and releasing the endpoint.
pub(crate) fn kill_dequeue_endpoint_victim(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, victim_ptr: RwLockThreadPtr, Tracked(victim_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            killer_held_context(*old(krnl), *old(lctx), cpu.current_process->Some_0, cpu.current_thread->Some_0, old(lctx).container_lock_map().dom())
        }),
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().state.is_endpoint_waiting(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_lock_perm.state() is WriteLock,
        victim_lock_perm.thread_id() == old(lctx).thread_id(),
        victim_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ({
            let victim = old(krnl).thr_mp.spec_index(victim_ptr);
            let endpoint_ptr = victim.view().blocking_endpoint_ptr->Some_0;
            let before = old(krnl).ep_mp.spec_index(endpoint_ptr);
            let after_endpoint = final(krnl).ep_mp.spec_index(endpoint_ptr);
            let after = final(krnl).thr_mp.spec_index(victim_ptr);
            &&& victim.view().blocking_endpoint_ptr is Some
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& *final(krnl) == (KernelK { ep_mp: final(krnl).ep_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr)
            &&& after_endpoint.view().queue.view() == before.view().queue.view().remove_value(victim_ptr)
            &&& after_endpoint.view().queue_state == before.view().queue_state
            &&& after_endpoint.view().owning_threads == before.view().owning_threads
            &&& after_endpoint.view().owning_container == before.view().owning_container
            &&& after_endpoint.locking_thread() == before.locking_thread()
            &&& after_endpoint.being_killed() == before.being_killed()
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, victim_ptr)
            &&& after.view() == (Thread {
                state: ThreadState::KILLED, blocking_endpoint_ptr: None, blocking_endpoint_index: None, endpoint_linkedlist_node: after.view().endpoint_linkedlist_node, ..victim.view()
            })
            &&& after.locking_thread() == victim.locking_thread()
            &&& after.being_killed() == victim.being_killed()
            &&& final(krnl).thr_mp.lock_id_by_key(victim_ptr) == old(krnl).thr_mp.lock_id_by_key(victim_ptr)
        }),
{
    proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, victim_ptr); thread_endpoint_queue_wf_thread_at(krnl.thr_mp, krnl.ep_mp, victim_ptr); }
    let (endpoint_ptr, node_addr) = {
        let victim = krnl.thr_mp.borrow_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_lock_perm));
        (victim.blocking_endpoint_ptr.unwrap(), victim.endpoint_linkedlist_node.addr())
    };
    let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
    let ghost pre = *krnl;
    proof {
        thread_endpoint_queue_wf_thread_at(krnl.thr_mp, krnl.ep_mp, victim_ptr); endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr);
        assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.dom().contains(node_addr)) by { krnl.ep_mp.spec_index(endpoint_ptr).view().queue.wf_map_at(node_addr); };
    }
    let node_perm = {
        let endpoint = krnl.ep_mp.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        endpoint.remove_waiter(node_addr)
    };
    {
        let victim = krnl.thr_mp.borrow_mut_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_lock_perm));
        victim.endpoint_waiter_to_killed(node_perm);
    }
    proof {
        assert(kill_dequeue_endpoint_eof_transition_framing(pre, *krnl, victim_ptr, endpoint_ptr)) by { reveal(kill_dequeue_endpoint_eof_transition_framing); };
        kill_dequeue_endpoint_eof(pre, *krnl, victim_ptr, endpoint_ptr);
    }
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    proof { assert(lctx.endpoint_lock_map() =~= old(lctx).endpoint_lock_map()); }
}

/// Force the remote cpu running the write-held marked thread `victim_ptr` from running to idle and kill the thread: the
/// cpu, write-locked, marked with `killer_info` for the running-to-idle IPI and released here, loads the default page
/// table with the default PCID and goes idle.
pub(crate) fn kill_running_victim_cpu_to_idle(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, victim_ptr: RwLockThreadPtr, killer_info: KillerInfo, Tracked(victim_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            let victim = old(krnl).thr_mp.spec_index(victim_ptr).view();
            &&& killer_held_context(*old(krnl), *old(lctx), cpu.current_process->Some_0, cpu.current_thread->Some_0, old(lctx).container_lock_map().dom())
            &&& victim.container_depth > cpu.container_depth || (victim.container_depth == cpu.container_depth && victim.process_depth > cpu.process_depth && !old(lctx).container_lock_map().dom().contains(cpu.owning_container))
        }),
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(victim_ptr).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_lock_perm.state() is WriteLock,
        victim_lock_perm.thread_id() == old(lctx).thread_id(),
        victim_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ({
            let victim = old(krnl).thr_mp.spec_index(victim_ptr);
            let remote = victim.view().state->RUNNING_cpu_id;
            let after = final(krnl).thr_mp.spec_index(victim_ptr);
            let after_cpu = final(krnl).cpu_arr.spec_index(remote).value.view().view();
            &&& index_valid(NUM_CPUS, remote)
            &&& remote != old(lctx).cpu_id()
            &&& final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int] == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int]
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_hw_cr3_pcid: final(krnl).cpu_hw_cr3_pcid, cpu_op: final(krnl).cpu_op, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(remote as int, CpuOpState::Idle)
            &&& forall|c: CpuId| #![trigger final(krnl).cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != remote ==> final(krnl).cpu_arr.spec_index(c) == old(krnl).cpu_arr.spec_index(c)
            &&& final(krnl).cpu_arr.spec_index(remote).value.lock_state_u() == old(krnl).cpu_arr.spec_index(remote).value.lock_state_u()
            &&& final(krnl).cpu_arr.spec_index(remote).value.being_killed() == old(krnl).cpu_arr.spec_index(remote).value.being_killed()
            &&& final(krnl).cpu_arr.spec_index(remote).value.killer_info() == old(krnl).cpu_arr.spec_index(remote).value.killer_info()
            &&& after_cpu.state is Idle
            &&& after_cpu.current_process is None
            &&& after_cpu.current_thread is None
            &&& after_cpu.owning_container == old(krnl).cpu_arr.spec_index(remote).value.view().view().owning_container
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, victim_ptr)
            &&& after.view() == (Thread { state: ThreadState::KILLED, ..victim.view() })
            &&& after.locking_thread() == victim.locking_thread()
            &&& after.being_killed() == victim.being_killed()
            &&& final(krnl).thr_mp.lock_id_by_key(victim_ptr) == old(krnl).thr_mp.lock_id_by_key(victim_ptr)
        }),
{
    proof {
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, victim_ptr);
        let killer_cpu = lctx.cpu_id();
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, killer_cpu);
        assert({
            let remote = krnl.thr_mp.spec_index(victim_ptr).view().state->RUNNING_cpu_id;
            let cpu = krnl.cpu_arr.spec_index(remote).view().view().view();
            &&& index_valid(NUM_CPUS, remote)
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(victim_ptr)
            &&& cpu.container_depth == krnl.thr_mp.spec_index(victim_ptr).view().container_depth
            &&& cpu.process_depth == krnl.thr_mp.spec_index(victim_ptr).view().process_depth
        }) by {
            let remote = krnl.thr_mp.spec_index(victim_ptr).view().state->RUNNING_cpu_id;
            thread_cpu_wf_thread_at(krnl.thr_mp, krnl.cpu_arr, victim_ptr); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, remote); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, remote); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, remote);
            process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, victim_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp.spec_index(victim_ptr).view().owning_proc);
        };
    }
    let remote = {
        let victim = krnl.thr_mp.borrow_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_lock_perm));
        match victim.state { ThreadState::RUNNING { cpu_id } => cpu_id, _ => 0 }
    };
    proof {
        let cpu = krnl.cpu_arr.spec_index(remote).view();
        assert(!cpu.being_killed()) by {
            assert(cpu.being_killed() ==> cpu.wlocked_by_thread(lctx.thread_id())) by {
                thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, remote); krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), victim_ptr);
            };
            reveal(LockedArray::typed_lock_map_aligned);
        };
    }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(remote, Tracked(&mut *lctx)).unwrap();
    let ghost pre = *krnl;
    let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(remote);
    proof {
        assert(krnl.cpu_arr.inv() && krnl.cpu_arr.spec_index(remote).view().is_init() && krnl.cpu_arr.spec_index(remote).view().view().wf()) by {
            cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), remote);
        };
        assert(krnl.cpu_hw_cr3_pcid[remote as int].owner_cpu() == remote) by { cpu_hw_cr3_pcid_wf_at(krnl.cpu_hw_cr3_pcid, krnl.cpu_arr, krnl.pcid_needflush, remote); };
        assert(krnl.cpu_arr.spec_index(remote).view().view().kernel_call_perm() == Some(remote) && !(krnl.cpu_op.view().view()[remote as int] is InStep)) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, remote); };
    }
    let default_cr3 = krnl.dflt_pt.borrow().cr3;
    assert(page_ptr_valid(default_cr3)) by { krnl.default_pagetable_view_inv(); };
    krnl.cpu_arr.ipi_remote_running_to_idle(remote, default_cr3, killer_info, &mut krnl.cpu_hw_cr3_pcid, Tracked(krnl.cpu_op.borrow_mut()), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Cpu(remote), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(remote)); }
    {
        let victim = krnl.thr_mp.borrow_mut_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_lock_perm));
        victim.running_to_killed();
    }
    proof {
        assert(kill_cpu_to_idle_eof_transition_framing(pre, *krnl, victim_ptr, remote, default_cr3)) by { reveal(kill_cpu_to_idle_eof_transition_framing); };
        kill_cpu_to_idle_eof(pre, *krnl, victim_ptr, remote, default_cr3);
    }
    krnl.wunlock_cpu(remote, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { assert(lctx.cpu_lock_map() =~= old(lctx).cpu_lock_map()); }
}
} // verus!

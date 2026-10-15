use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_wake_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_wake_eof::thread_exit_wake_caller_eof;

verus! {
/// Schedule the caller the running exiting thread serves on shard `cpu_id` of its container's scheduler with
/// `ErrorIpcCalleeExited`, drop the exiting thread's caller link, and release the caller.
pub(super) fn thread_exit_wake_caller(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr,
    caller_ptr: RwLockThreadPtr, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(caller_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller == Some(caller_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(caller_ptr),
        old(krnl).thr_mp.spec_index(caller_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(caller_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(caller_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(caller_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(caller_ptr).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write),
        caller_lock_perm.state() is WriteLock,
        caller_lock_perm.thread_id() == old(lctx).thread_id(),
        caller_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id,
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr, caller_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(caller_ptr)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) && t != thread_ptr && t != caller_ptr ==> final(krnl).thr_mp.spec_index(t) == old(krnl).thr_mp.spec_index(t),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { caller: None, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        final(krnl).thr_mp.spec_index(caller_ptr).view() == (Thread {
            state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited),
            scheduler_linkedlist_node: final(krnl).thr_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node, ..old(krnl).thr_mp.spec_index(caller_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(caller_ptr).locking_thread() is None,
        final(krnl).thr_mp.spec_index(caller_ptr).being_killed() == old(krnl).thr_mp.spec_index(caller_ptr).being_killed(),
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger final(krnl).sched_mp.spec_index(s)] old(krnl).sched_mp.dom().contains(s) ==>
            scheduler_shards_of(final(krnl).sched_mp.spec_index(s)) == if s == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler {
                scheduler_shards_of(old(krnl).sched_mp.spec_index(s)).update(cpu_id as int, scheduler_shards_of(old(krnl).sched_mp.spec_index(s))[cpu_id as int].push(caller_ptr))
            } else { scheduler_shards_of(old(krnl).sched_mp.spec_index(s)) },
{
    proof {
        container_perms_wf_at(krnl.ctn_mp, container_ptr); container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_perms_wf_at(krnl.thr_mp, caller_ptr);
        assert(krnl.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY) by { thread_caller_callee_wf_at(krnl.thr_mp, thread_ptr); };
    }
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
    let ghost pre = *krnl;
    proof {
        container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, caller_ptr);
        scheduler_queue_len_bounded(&*krnl, scheduler_ptr, cpu_id);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_perms_wf_at(krnl.thr_mp, caller_ptr);
    }
    {
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        thread_mut.release_caller();
    }
    let ghost old_caller_lock_id = krnl.thr_mp.lock_id_by_key(caller_ptr);
    let (node_addr, node_perm) = {
        let caller_mut = krnl.thr_mp.borrow_mut_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm));
        caller_mut.waiting_reply_to_scheduled(caller_ptr, cpu_id, RetValueType::ErrorIpcCalleeExited)
    };
    scheduler_map_enqueue_scheduled_thread(&mut krnl.sched_mp, scheduler_ptr, cpu_id, caller_ptr, node_addr, node_perm, Tracked(&*lctx), Tracked(&scheduler_lock_perm));
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(caller_ptr), old_caller_lock_id, krnl.thr_mp.lock_id_by_key(caller_ptr));
        scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr);
        assert(thread_exit_wake_caller_transition(pre, *krnl, thread_ptr, caller_ptr, scheduler_ptr, cpu_id)) by { reveal(thread_exit_wake_caller_transition); };
        thread_exit_wake_caller_eof(pre, *krnl, thread_ptr, caller_ptr, scheduler_ptr, cpu_id);
    }
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.wunlock_thread(caller_ptr, Tracked(&mut *lctx), Tracked(caller_lock_perm));
    proof {
        assert(lctx.scheduler_lock_map() =~= old(lctx).scheduler_lock_map());
        assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().remove(caller_ptr));
    }
}
} // verus!

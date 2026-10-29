use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn process_subsystem_create_scheduled_thread_eof_transition_framing(
    pre_process: ProcessLockedMap, post_process: ProcessLockedMap,
    pre_thread: ThreadLockedMap, post_thread: ThreadLockedMap,
    pre_scheduler: SchedulerUnLockedMap, post_scheduler: SchedulerUnLockedMap,
    pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thread_value: Thread, process_node_addr: usize, sched_node_addr: usize,
) -> bool {
    &&& post_process.dom() == pre_process.dom()
    &&& post_process.unchanged_except(&pre_process, process_ptr)
    &&& post_process.spec_index(process_ptr).view() == (Process { owned_threads: post_process.spec_index(process_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..pre_process.spec_index(process_ptr).view() })
    &&& post_process.spec_index(process_ptr).view().owned_threads.view() == pre_process.spec_index(process_ptr).view().owned_threads.view().push(page_ptr)
    &&& post_process.spec_index(process_ptr).view().owned_threads.dom() == pre_process.spec_index(process_ptr).view().owned_threads.dom().insert(process_node_addr)
    &&& post_process.spec_index(process_ptr).view().owned_threads.map() == pre_process.spec_index(process_ptr).view().owned_threads.map().insert(process_node_addr, page_ptr)
    &&& post_process.spec_index(process_ptr).view_rodata() == pre_process.spec_index(process_ptr).view_rodata()
    &&& post_process.spec_index(process_ptr).view_ghost() == pre_process.spec_index(process_ptr).view_ghost()
    &&& post_process.spec_index(process_ptr).locking_thread() == pre_process.spec_index(process_ptr).locking_thread()
    &&& post_process.spec_index(process_ptr).being_killed() == pre_process.spec_index(process_ptr).being_killed()
    &&& forall|ptr: RwLockProcessPtr| #![trigger post_process.spec_index(ptr)] pre_process.dom().contains(ptr) && ptr != process_ptr ==> post_process.spec_index(ptr) == pre_process.spec_index(ptr)
    &&& post_thread.dom() =~= pre_thread.dom().insert(page_ptr)
    &&& post_thread.spec_index(page_ptr).view() == thread_value
    &&& post_thread.spec_index(page_ptr).is_init()
    &&& !post_thread.spec_index(page_ptr).being_killed()
    &&& post_thread.spec_index(staging_thread_ptr).view() == (Thread { quota_4k: post_thread.spec_index(staging_thread_ptr).view().quota_4k,
        temp_alloc_cache_4k: post_thread.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k, ..pre_thread.spec_index(staging_thread_ptr).view() })
    &&& post_thread.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() == pre_thread.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& post_thread.spec_index(staging_thread_ptr).view().quota_4k == pre_thread.spec_index(staging_thread_ptr).view().quota_4k - 1
    &&& post_thread.spec_index(staging_thread_ptr).locking_thread() == pre_thread.spec_index(staging_thread_ptr).locking_thread()
    &&& post_thread.spec_index(staging_thread_ptr).being_killed() == pre_thread.spec_index(staging_thread_ptr).being_killed()
    &&& post_thread.spec_index(staging_thread_ptr).killer_info() == pre_thread.spec_index(staging_thread_ptr).killer_info()
    &&& post_thread.spec_index(staging_thread_ptr).view_ghost() == pre_thread.spec_index(staging_thread_ptr).view_ghost()
    &&& forall|ptr: RwLockThreadPtr| #![trigger post_thread.spec_index(ptr)] pre_thread.dom().contains(ptr) && ptr != staging_thread_ptr ==> post_thread.spec_index(ptr) == pre_thread.spec_index(ptr)
    &&& post_scheduler.unchanged_except(&pre_scheduler, scheduler_ptr)
    &&& post_scheduler.spec_index(scheduler_ptr).owning_container == pre_scheduler.spec_index(scheduler_ptr).owning_container
    &&& post_scheduler.spec_index(scheduler_ptr).shards.entries_unchanged_except(&pre_scheduler.spec_index(scheduler_ptr).shards, cpu_id)
    &&& post_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.view() == pre_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.view().push(page_ptr)
    &&& post_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.dom() == pre_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.dom().insert(sched_node_addr)
    &&& post_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.map() == pre_scheduler.spec_index(scheduler_ptr).shard(cpu_id).queue.map().insert(sched_node_addr, page_ptr)
    &&& post_scheduler.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread() == pre_scheduler.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()
    &&& post_scheduler.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == pre_scheduler.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed()
    &&& scheduler_shards_of(post_scheduler.spec_index(scheduler_ptr))
        == scheduler_shards_of(pre_scheduler.spec_index(scheduler_ptr)).update(cpu_id as int, scheduler_shards_of(pre_scheduler.spec_index(scheduler_ptr))[cpu_id as int].push(page_ptr))
    &&& post_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& post_lctx.thread_id() == pre_lctx.thread_id()
    &&& post_lctx.kernel_view_locking_state() is Release
    &&& typed_lock_maps_inserted(pre_lctx, post_lctx, KernelObjId::Thread(page_ptr), TypedHeldLock { lock_id: post_thread.lock_id_by_key(page_ptr), mode: TypedLockMode::Write })
}

} // verus!

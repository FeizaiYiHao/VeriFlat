use vstd::prelude::*;
use crate::*;

verus! {
/// Each container owns exactly its scheduler.
#[verifier::opaque]
pub open spec fn container_scheduler_wf(ctn_mp: ContainerLockedMap, sched_mp: SchedulerUnLockedMap) -> bool {
    // Container -> scheduler.
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) ==> {
            let sched_ptr = ctn_mp.spec_index(c).view_rodata().view().scheduler;
            &&& sched_mp.dom().contains(sched_ptr)
            &&& sched_mp.spec_index(sched_ptr).owning_container == c
        }
    // Scheduler -> container.
    &&& forall|s: RwLockSchedulerPtr|
        #![trigger sched_mp.dom().contains(s)]
        sched_mp.dom().contains(s) ==> {
            let ctn_ptr = sched_mp.spec_index(s).owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == s
        }
}

pub proof fn container_scheduler_wf_container_at(ctn_mp: ContainerLockedMap, sched_mp: SchedulerUnLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_scheduler_wf(ctn_mp, sched_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        sched_mp.dom().contains(ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler),
        sched_mp.spec_index(ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler).owning_container == ctn_ptr,
{ reveal(container_scheduler_wf); }

/// A thread is `SCHEDULED { cpu_id }` exactly when it is queued on shard `cpu_id` of its container's scheduler.
// Proof dependencies (confirmed): container_thread_wf, container_scheduler_wf.
#[verifier::opaque]
pub open spec fn container_thread_scheduler_wf(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, sched_mp: SchedulerUnLockedMap) -> bool {
    // Scheduled thread -> its shard's queue.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().state]
        #![trigger thrd_mp.spec_index(t).view().owning_container]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().state is SCHEDULED ==> {
            let thread = thrd_mp.spec_index(t).view();
            let queue = sched_mp.spec_index(ctn_mp.spec_index(thread.owning_container).view_rodata().view().scheduler).shard(thread.state->SCHEDULED_cpu_id).queue;
            &&& index_valid(NUM_CPUS, thread.state->SCHEDULED_cpu_id)
            &&& queue.view().contains(t)
            &&& queue.map().dom().contains(thread.scheduler_linkedlist_node.addr())
            &&& queue.map().spec_index(thread.scheduler_linkedlist_node.addr()) == t
        }
    // Shard queue -> scheduled thread of the scheduler's container.
    &&& forall|s: RwLockSchedulerPtr, cpu_id: CpuId, t: RwLockThreadPtr|
        #![trigger sched_mp.spec_index(s).shard(cpu_id).queue.view().contains(t)]
        #![trigger thrd_mp.spec_index(t).view().state, sched_mp.dom().contains(s), index_valid(NUM_CPUS, cpu_id)]
        #![trigger thrd_mp.spec_index(t).view().owning_container, sched_mp.dom().contains(s), index_valid(NUM_CPUS, cpu_id)]
        sched_mp.dom().contains(s)
            && index_valid(NUM_CPUS, cpu_id)
            && sched_mp.spec_index(s).shard(cpu_id).queue.view().contains(t)
            ==> {
                &&& thrd_mp.dom().contains(t)
                &&& thrd_mp.spec_index(t).view().state == (ThreadState::SCHEDULED { cpu_id })
                &&& thrd_mp.spec_index(t).view().owning_container == sched_mp.spec_index(s).owning_container
            }
}

pub proof fn container_thread_scheduler_wf_shard_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, sched_mp: SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        container_thread_scheduler_wf(ctn_mp, thrd_mp, sched_mp),
        sched_mp.dom().contains(sched_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.view().contains(thrd_ptr) ==> {
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& thrd_mp.spec_index(thrd_ptr).view().owning_container == sched_mp.spec_index(sched_ptr).owning_container
        },
{ reveal(container_thread_scheduler_wf); }

pub proof fn container_thread_scheduler_wf_thread_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, sched_mp: SchedulerUnLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        container_thread_scheduler_wf(ctn_mp, thrd_mp, sched_mp),
    ensures
        thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view().state is SCHEDULED ==> {
            let thread = thrd_mp.spec_index(thrd_ptr).view();
            let queue = sched_mp.spec_index(ctn_mp.spec_index(thread.owning_container).view_rodata().view().scheduler).shard(thread.state->SCHEDULED_cpu_id).queue;
            &&& index_valid(NUM_CPUS, thread.state->SCHEDULED_cpu_id)
            &&& queue.view().contains(thrd_ptr)
            &&& queue.map().dom().contains(thread.scheduler_linkedlist_node.addr())
            &&& queue.map().spec_index(thread.scheduler_linkedlist_node.addr()) == thrd_ptr
        },
{ reveal(container_thread_scheduler_wf); }
}

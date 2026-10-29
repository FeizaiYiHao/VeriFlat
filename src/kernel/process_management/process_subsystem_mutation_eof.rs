use vstd::prelude::*;
use crate::*;

verus! {
pub(super) proof fn thread_map_consume_staged_4k_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        post.spec_index(thread_ptr).being_killed() == pre.spec_index(thread_ptr).being_killed(),
        post.spec_index(thread_ptr).view_ghost() == pre.spec_index(thread_ptr).view_ghost(),
        post.spec_index(thread_ptr).view() == (Thread { quota_4k: post.spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.spec_index(thread_ptr).view().temp_alloc_cache_4k, ..pre.spec_index(thread_ptr).view() }),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

pub(super) proof fn thread_map_add_free_quota_pending_4k_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        post.spec_index(thread_ptr).being_killed() == pre.spec_index(thread_ptr).being_killed(),
        post.spec_index(thread_ptr).view_ghost() == pre.spec_index(thread_ptr).view_ghost(),
        post.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: post.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: post.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..pre.spec_index(thread_ptr).view() }),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

pub(super) proof fn thread_map_clear_free_quota_pending_4k_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        post.spec_index(thread_ptr).being_killed() == pre.spec_index(thread_ptr).being_killed(),
        post.spec_index(thread_ptr).view_ghost() == pre.spec_index(thread_ptr).view_ghost(),
        post.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: post.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: post.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..pre.spec_index(thread_ptr).view() }),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

pub(super) proof fn thread_map_consume_new_container_staging_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        post.spec_index(thread_ptr).being_killed() == pre.spec_index(thread_ptr).being_killed(),
        post.spec_index(thread_ptr).view_ghost() == pre.spec_index(thread_ptr).view_ghost(),
        post.spec_index(thread_ptr).view() == (Thread { temp_alloc_cache_4k: post.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            temp_alloc_cache_2m: post.spec_index(thread_ptr).view().temp_alloc_cache_2m, quota_4k: post.spec_index(thread_ptr).view().quota_4k,
            quota_2m: post.spec_index(thread_ptr).view().quota_2m, ..pre.spec_index(thread_ptr).view() }),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

pub(super) proof fn thread_map_set_endpoint_descriptor_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        post.spec_index(thread_ptr).being_killed() == pre.spec_index(thread_ptr).being_killed(),
        post.spec_index(thread_ptr).view_ghost() == pre.spec_index(thread_ptr).view_ghost(),
        post.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: post.spec_index(thread_ptr).view().endpoint_descriptors, ..pre.spec_index(thread_ptr).view() }),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

pub(super) proof fn process_map_add_owned_thread_eof_process_perms_wf(pre: ProcessLockedMap, post: ProcessLockedMap, process_ptr: RwLockProcessPtr)
    requires
        process_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, process_ptr),
        post.spec_index(process_ptr).inv(),
        post.spec_index(process_ptr).view() == (Process { owned_threads: post.spec_index(process_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..pre.spec_index(process_ptr).view() }),
        post.spec_index(process_ptr).view_rodata() == pre.spec_index(process_ptr).view_rodata(),
        post.spec_index(process_ptr).view_ghost() == pre.spec_index(process_ptr).view_ghost(),
    ensures process_perms_wf(post),
{ reveal(process_perms_wf); }

pub(super) proof fn process_map_link_new_child_eof_process_perms_wf(pre: ProcessLockedMap, post: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_perms_wf(pre),
        post.perms_wf(),
        post.dom() == pre.dom(),
        pre.dom().contains(parent_ptr),
        pre.dom().contains(child_ptr),
        parent_ptr != child_ptr,
        forall|ptr: RwLockProcessPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) && ptr != parent_ptr && ptr != child_ptr ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(child_ptr).inv(),
        post.spec_index(child_ptr).view() == (Process { parent_linkedlist_node: post.spec_index(child_ptr).view().parent_linkedlist_node, ..pre.spec_index(child_ptr).view() }),
        post.spec_index(child_ptr).view_rodata() == pre.spec_index(child_ptr).view_rodata(),
        post.spec_index(child_ptr).view_ghost() == pre.spec_index(child_ptr).view_ghost(),
        post.spec_index(parent_ptr).inv(),
        post.spec_index(parent_ptr).view().children.view() == pre.spec_index(parent_ptr).view().children.view().push(child_ptr),
        !pre.spec_index(parent_ptr).view().children.view().contains(child_ptr),
        post.spec_index(parent_ptr).view_rodata() == pre.spec_index(parent_ptr).view_rodata(),
        post.spec_index(parent_ptr).view_ghost() == pre.spec_index(parent_ptr).view_ghost(),
    ensures process_perms_wf(post),
{ reveal(process_perms_wf); seq_push_unique_lemma::<RwLockProcessPtr>(); }

pub(super) proof fn process_map_unlink_child_eof_process_perms_wf(pre: ProcessLockedMap, post: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, parent_ptr),
        post.spec_index(parent_ptr).inv(),
        post.spec_index(parent_ptr).view().children.view() == pre.spec_index(parent_ptr).view().children.view().remove_value(child_ptr),
        post.spec_index(parent_ptr).view().children.view().no_duplicates(),
        post.spec_index(parent_ptr).view_rodata() == pre.spec_index(parent_ptr).view_rodata(),
        post.spec_index(parent_ptr).view_ghost() == pre.spec_index(parent_ptr).view_ghost(),
    ensures process_perms_wf(post),
{ reveal(process_perms_wf); lemma_seq_remove_value_membership::<RwLockProcessPtr>(); }

pub(super) proof fn scheduler_map_enqueue_scheduled_thread_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, scheduler_ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub(super) proof fn scheduler_map_remove_scheduled_thread_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, scheduler_ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub(super) proof fn scheduler_map_move_shard_head_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, scheduler_ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub(super) proof fn scheduler_map_insert_new_4k_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(scheduler_ptr),
        forall|ptr: RwLockSchedulerPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(pre) ==> scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub(super) proof fn pcid_allocator_map_alloc_eof_pcid_allocator_perms_wf(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        pcid_allocator_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, allocator_ptr),
        post.spec_index(allocator_ptr).inv(),
    ensures pcid_allocator_perms_wf(post),
{ reveal(pcid_allocator_perms_wf); }

pub(super) proof fn pcid_allocator_map_release_eof_pcid_allocator_perms_wf(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        pcid_allocator_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, allocator_ptr),
        post.spec_index(allocator_ptr).inv(),
    ensures pcid_allocator_perms_wf(post),
{ reveal(pcid_allocator_perms_wf); }

pub(super) proof fn pcid_allocator_map_insert_new_2m_eof_pcid_allocator_perms_wf(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(allocator_ptr).inv(),
    ensures pcid_allocator_perms_wf(pre) ==> pcid_allocator_perms_wf(post),
{ reveal(pcid_allocator_perms_wf); }

pub(super) proof fn cpu_set_map_insert_new_4k_eof_cpu_set_perms_wf(pre: CpuSetLockedMap, post: CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(cpu_set_ptr),
        forall|ptr: RwLockCpuSetPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(cpu_set_ptr).inv(),
    ensures cpu_set_perms_wf(pre) ==> cpu_set_perms_wf(post),
{ reveal(cpu_set_perms_wf); }

pub(super) proof fn endpoint_map_insert_new_4k_eof_endpoint_perms_wf(pre: EndpointLockedMap, post: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(endpoint_ptr),
        forall|ptr: RwLockEndpointPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(endpoint_ptr).inv(),
    ensures endpoint_perms_wf(pre) ==> endpoint_perms_wf(post),
{ reveal(endpoint_perms_wf); }

pub(super) proof fn container_map_unlink_child_eof_container_perms_wf(pre: ContainerLockedMap, post: ContainerLockedMap, parent_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr)
    requires
        container_perms_wf(pre),
        post.perms_wf(),
        post.dom() == pre.dom(),
        pre.dom().contains(parent_ptr),
        forall|c: RwLockContainerPtr| #![trigger post.spec_index(c)]
            pre.dom().contains(c) ==> {
                &&& post.spec_index(c).is_init() == pre.spec_index(c).is_init()
                &&& post.spec_index(c).view_rodata() == pre.spec_index(c).view_rodata()
                &&& post.spec_index(c).view_ghost().uppertree_seq == pre.spec_index(c).view_ghost().uppertree_seq
                &&& post.spec_index(c).locking_thread() == pre.spec_index(c).locking_thread()
                &&& c != parent_ptr ==> post.spec_index(c).view() == pre.spec_index(c).view()
            },
        post.spec_index(parent_ptr).inv(),
        post.spec_index(parent_ptr).view().children.view() == pre.spec_index(parent_ptr).view().children.view().remove_value(child_ptr),
        post.spec_index(parent_ptr).view().children.view().no_duplicates(),
    ensures container_perms_wf(post),
{ reveal(container_perms_wf); reveal(container_tree_fields_wf); lemma_seq_remove_value_membership::<RwLockContainerPtr>(); }

pub(super) proof fn process_subsystem_create_scheduled_thread_eof_process_thread_wf(
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

pub(super) proof fn process_subsystem_create_scheduled_thread_eof_scheduler_wf(
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

pub(super) proof fn process_subsystem_create_scheduled_thread_eof_thread_perms_wf(
    pre_process: ProcessLockedMap, post_process: ProcessLockedMap, pre_thread: ThreadLockedMap,
    post_thread: ThreadLockedMap, pre_scheduler: SchedulerUnLockedMap,
    post_scheduler: SchedulerUnLockedMap, pre_lctx: &LocalContext, post_lctx: &LocalContext,
    page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thread_value: Thread, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        thread_perms_wf(pre_thread),
        post_thread.perms_wf(),
        process_subsystem_create_scheduled_thread_eof_transition_framing(pre_process, post_process, pre_thread, post_thread, pre_scheduler, post_scheduler, pre_lctx, post_lctx,
            page_ptr, process_ptr, staging_thread_ptr, scheduler_ptr, cpu_id, thread_value, process_node_addr, sched_node_addr),
        !pre_thread.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        post_thread.spec_index(page_ptr).inv(),
        post_thread.spec_index(page_ptr).locking_thread() is Write,
        post_thread.spec_index(page_ptr).view().state is SCHEDULED,
        post_thread.spec_index(staging_thread_ptr).inv(),
        post_thread.spec_index(staging_thread_ptr).locking_thread() is Write,
    ensures thread_perms_wf(post_thread),
{
    reveal(process_subsystem_create_scheduled_thread_eof_transition_framing);
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}
}

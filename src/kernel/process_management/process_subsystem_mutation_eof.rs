use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn thread_map_consume_staged_4k_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
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

pub proof fn thread_map_add_free_quota_pending_4k_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
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

pub proof fn thread_map_clear_free_quota_pending_4k_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
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

pub proof fn thread_map_consume_new_container_staging_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
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

pub proof fn thread_map_set_endpoint_descriptor_eof_thread_perms_wf(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
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

pub proof fn process_map_add_owned_thread_eof_process_perms_wf(pre: ProcessLockedMap, post: ProcessLockedMap, process_ptr: RwLockProcessPtr)
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

pub proof fn process_map_link_new_child_eof_process_perms_wf(pre: ProcessLockedMap, post: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
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

pub proof fn process_map_unlink_child_eof_process_perms_wf(pre: ProcessLockedMap, post: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
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

pub proof fn scheduler_map_enqueue_scheduled_thread_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, scheduler_ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub proof fn scheduler_map_remove_scheduled_thread_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, scheduler_ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub proof fn scheduler_map_move_shard_head_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, scheduler_ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub proof fn scheduler_map_insert_new_4k_eof_scheduler_perms_wf(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(scheduler_ptr),
        forall|ptr: RwLockSchedulerPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(scheduler_ptr).inv(),
    ensures scheduler_perms_wf(pre) ==> scheduler_perms_wf(post),
{ reveal(scheduler_perms_wf); }

pub proof fn pcid_allocator_map_alloc_eof_pcid_allocator_perms_wf(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        pcid_allocator_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, allocator_ptr),
        post.spec_index(allocator_ptr).inv(),
    ensures pcid_allocator_perms_wf(post),
{ reveal(pcid_allocator_perms_wf); }

pub proof fn pcid_allocator_map_release_eof_pcid_allocator_perms_wf(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        pcid_allocator_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, allocator_ptr),
        post.spec_index(allocator_ptr).inv(),
    ensures pcid_allocator_perms_wf(post),
{ reveal(pcid_allocator_perms_wf); }

pub proof fn pcid_allocator_map_insert_new_2m_eof_pcid_allocator_perms_wf(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(allocator_ptr).inv(),
    ensures pcid_allocator_perms_wf(pre) ==> pcid_allocator_perms_wf(post),
{ reveal(pcid_allocator_perms_wf); }

pub proof fn cpu_set_map_insert_new_4k_eof_cpu_set_perms_wf(pre: CpuSetLockedMap, post: CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(cpu_set_ptr),
        forall|ptr: RwLockCpuSetPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(cpu_set_ptr).inv(),
    ensures cpu_set_perms_wf(pre) ==> cpu_set_perms_wf(post),
{ reveal(cpu_set_perms_wf); }

pub proof fn endpoint_map_insert_new_4k_eof_endpoint_perms_wf(pre: EndpointLockedMap, post: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(endpoint_ptr),
        forall|ptr: RwLockEndpointPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(endpoint_ptr).inv(),
    ensures endpoint_perms_wf(pre) ==> endpoint_perms_wf(post),
{ reveal(endpoint_perms_wf); }

pub proof fn container_map_unlink_child_eof_container_perms_wf(pre: ContainerLockedMap, post: ContainerLockedMap, parent_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr)
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
}

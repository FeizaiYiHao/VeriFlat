use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn thread_caller_callee_wf_preserved_for_call_link_eq(old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap)
    requires
        thread_caller_callee_wf(old_thread_map),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().caller == old_thread_map.spec_index(t_ptr).view().caller
                &&& new_thread_map.spec_index(t_ptr).view().callee == old_thread_map.spec_index(t_ptr).view().callee
                &&& new_thread_map.spec_index(t_ptr).view().owning_container == old_thread_map.spec_index(t_ptr).view().owning_container
                &&& new_thread_map.spec_index(t_ptr).view().state.is_reply_waiting() == old_thread_map.spec_index(t_ptr).view().state.is_reply_waiting()
                &&& new_thread_map.spec_index(t_ptr).view().call_depth == old_thread_map.spec_index(t_ptr).view().call_depth
            },
    ensures
        thread_caller_callee_wf(new_thread_map),
{ reveal(thread_caller_callee_wf); }

pub proof fn thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap, old_endpoint_map: EndpointLockedMap, new_endpoint_map: EndpointLockedMap)
    requires
        thread_endpoint_ref_counter_wf(old_thread_map, old_endpoint_map),
        new_thread_map.dom() == old_thread_map.dom(),
        new_endpoint_map.dom() == old_endpoint_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) ==> new_thread_map.spec_index(t_ptr).view().endpoint_descriptors.view() == old_thread_map.spec_index(t_ptr).view().endpoint_descriptors.view(),
        forall|e_ptr: RwLockEndpointPtr|
            #![trigger new_endpoint_map.spec_index(e_ptr)]
            new_endpoint_map.dom().contains(e_ptr) ==> new_endpoint_map.spec_index(e_ptr).view().owning_threads == old_endpoint_map.spec_index(e_ptr).view().owning_threads,
    ensures
        thread_endpoint_ref_counter_wf(new_thread_map, new_endpoint_map),
{ reveal(thread_endpoint_ref_counter_wf); }

pub proof fn thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap)
    requires
        thread_endpoint_queue_wf(old_thread_map, endpoint_map),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) && (old_thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting() || new_thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting()) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().state == old_thread_map.spec_index(t_ptr).view().state
                &&& new_thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr == old_thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr
                &&& new_thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr() == old_thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr()
            },
    ensures
        thread_endpoint_queue_wf(new_thread_map, endpoint_map),
{ reveal(thread_endpoint_queue_wf); }

// The extra wf requires only supply dom membership of looked-up keys (descriptor target via the reference counter, endpoint owner via
// container_endpoint_wf).
pub proof fn container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(
    old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap,
    old_endpoint_map: EndpointLockedMap, new_endpoint_map: EndpointLockedMap,
)
    requires
        container_thread_endpoint_wf(old_container_map, old_thread_map, old_endpoint_map),
        thread_endpoint_ref_counter_wf(old_thread_map, old_endpoint_map),
        container_endpoint_wf(old_container_map, old_endpoint_map),
        new_container_map.dom() == old_container_map.dom(),
        new_thread_map.dom() == old_thread_map.dom(),
        new_endpoint_map.dom() == old_endpoint_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view_ghost().subtree_set == old_container_map.spec_index(c_ptr).view_ghost().subtree_set,
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().endpoint_descriptors == old_thread_map.spec_index(t_ptr).view().endpoint_descriptors
                &&& new_thread_map.spec_index(t_ptr).view().owning_container == old_thread_map.spec_index(t_ptr).view().owning_container
            },
        forall|e_ptr: RwLockEndpointPtr|
            #![trigger new_endpoint_map.spec_index(e_ptr)]
            new_endpoint_map.dom().contains(e_ptr) ==> new_endpoint_map.spec_index(e_ptr).view().owning_container == old_endpoint_map.spec_index(e_ptr).view().owning_container,
    ensures
        container_thread_endpoint_wf(new_container_map, new_thread_map, new_endpoint_map),
{ reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); }

// container_thread_wf(old) only supplies that each scheduled thread's owning container is in the container dom.
pub proof fn container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap, scheduler_map: SchedulerUnLockedMap)
    requires
        container_thread_scheduler_wf(old_container_map, old_thread_map, scheduler_map),
        container_thread_wf(old_container_map, old_thread_map),
        new_container_map.dom() == old_container_map.dom(),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view_rodata().view().scheduler == old_container_map.spec_index(c_ptr).view_rodata().view().scheduler,
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) && (old_thread_map.spec_index(t_ptr).view().state is SCHEDULED || new_thread_map.spec_index(t_ptr).view().state is SCHEDULED) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().state == old_thread_map.spec_index(t_ptr).view().state
                &&& new_thread_map.spec_index(t_ptr).view().owning_container == old_thread_map.spec_index(t_ptr).view().owning_container
                &&& new_thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr() == old_thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()
            },
    ensures
        container_thread_scheduler_wf(new_container_map, new_thread_map, scheduler_map),
{ reveal(container_thread_scheduler_wf); reveal(container_thread_wf); }

pub proof fn container_thread_wf_preserved_for_container_thread_link_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap)
    requires
        container_thread_wf(old_container_map, old_thread_map),
        new_container_map.dom() == old_container_map.dom(),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> {
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_threads == old_container_map.spec_index(c_ptr).view_ghost().owned_threads
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads == old_container_map.spec_index(c_ptr).view_ghost().owned_indirect_threads
                &&& new_container_map.spec_index(c_ptr).view_ghost().uppertree_seq == old_container_map.spec_index(c_ptr).view_ghost().uppertree_seq
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().depth == old_container_map.spec_index(c_ptr).view_rodata().view().depth
            },
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().owning_container == old_thread_map.spec_index(t_ptr).view().owning_container
                &&& new_thread_map.spec_index(t_ptr).view().container_depth == old_thread_map.spec_index(t_ptr).view().container_depth
                &&& new_thread_map.spec_index(t_ptr).view().upper_container_seq == old_thread_map.spec_index(t_ptr).view().upper_container_seq
                &&& thread_is_dangling(new_thread_map.spec_index(t_ptr)) == thread_is_dangling(old_thread_map.spec_index(t_ptr))
            },
    ensures
        container_thread_wf(new_container_map, new_thread_map),
{ reveal(container_thread_wf); }

pub proof fn process_thread_wf_preserved_for_process_thread_link_eq(old_process_map: ProcessLockedMap, new_process_map: ProcessLockedMap, old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap)
    requires
        process_thread_wf(old_process_map, old_thread_map),
        new_process_map.dom() == old_process_map.dom(),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_map.spec_index(p_ptr)]
            new_process_map.dom().contains(p_ptr) ==> {
                &&& new_process_map.spec_index(p_ptr).view().zombie == old_process_map.spec_index(p_ptr).view().zombie
                &&& new_process_map.spec_index(p_ptr).view_rodata() == old_process_map.spec_index(p_ptr).view_rodata()
                &&& new_process_map.spec_index(p_ptr).view().owned_threads == old_process_map.spec_index(p_ptr).view().owned_threads
                &&& new_process_map.spec_index(p_ptr).view().pagetable == old_process_map.spec_index(p_ptr).view().pagetable
                &&& new_process_map.spec_index(p_ptr).being_killed() == old_process_map.spec_index(p_ptr).being_killed()
                &&& new_process_map.spec_index(p_ptr).locking_thread() == old_process_map.spec_index(p_ptr).locking_thread()
            },
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().owning_proc == old_thread_map.spec_index(t_ptr).view().owning_proc
                &&& new_thread_map.spec_index(t_ptr).view().owning_container == old_thread_map.spec_index(t_ptr).view().owning_container
                &&& new_thread_map.spec_index(t_ptr).view().container_depth == old_thread_map.spec_index(t_ptr).view().container_depth
                &&& new_thread_map.spec_index(t_ptr).view().process_depth == old_thread_map.spec_index(t_ptr).view().process_depth
                &&& new_thread_map.spec_index(t_ptr).view().proc_pagetable_ptr == old_thread_map.spec_index(t_ptr).view().proc_pagetable_ptr
                &&& new_thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr() == old_thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr()
                &&& new_thread_map.spec_index(t_ptr).view().proc_linkedlist_node.is_init() == old_thread_map.spec_index(t_ptr).view().proc_linkedlist_node.is_init()
                &&& thread_is_dangling(new_thread_map.spec_index(t_ptr)) == thread_is_dangling(old_thread_map.spec_index(t_ptr))
                &&& new_thread_map.spec_index(t_ptr).being_killed() ==> old_thread_map.spec_index(t_ptr).being_killed() && new_thread_map.spec_index(t_ptr).locking_thread() == old_thread_map.spec_index(t_ptr).locking_thread()
                    && (new_thread_map.spec_index(t_ptr).view().state.is_reply_waiting() ==> old_thread_map.spec_index(t_ptr).view().state.is_reply_waiting())
            },
    ensures
        process_thread_wf(new_process_map, new_thread_map),
{ reveal(process_thread_wf); }

pub proof fn process_emptied_threads_wf_preserved_for_state_owned_threads_exited_eq(old_process_map: ProcessLockedMap, new_process_map: ProcessLockedMap, old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap)
    requires
        process_emptied_threads_wf(old_process_map, old_thread_map),
        new_process_map.dom() == old_process_map.dom(),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_map.spec_index(p_ptr)]
            new_process_map.dom().contains(p_ptr) ==> {
                &&& new_process_map.spec_index(p_ptr).view().state == old_process_map.spec_index(p_ptr).view().state
                &&& new_process_map.spec_index(p_ptr).view().owned_threads == old_process_map.spec_index(p_ptr).view().owned_threads
            },
        forall|t_ptr: RwLockThreadPtr| #![trigger new_thread_map.spec_index(t_ptr)] new_thread_map.dom().contains(t_ptr) ==> new_thread_map.spec_index(t_ptr).view_ghost().exited == old_thread_map.spec_index(t_ptr).view_ghost().exited,
    ensures
        process_emptied_threads_wf(new_process_map, new_thread_map),
{ reveal(process_emptied_threads_wf); }

pub proof fn thread_cpu_wf_preserved_for_running_thread_eq(old_thread_map: ThreadLockedMap, new_thread_map: ThreadLockedMap, old_cpu_array: CpuLockedArray, new_cpu_array: CpuLockedArray)
    requires
        thread_cpu_wf(old_thread_map, old_cpu_array),
        new_thread_map.dom() == old_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger new_thread_map.spec_index(t_ptr)]
            new_thread_map.dom().contains(t_ptr) && (old_thread_map.spec_index(t_ptr).view().state is RUNNING || new_thread_map.spec_index(t_ptr).view().state is RUNNING) ==> {
                &&& new_thread_map.spec_index(t_ptr).view().state == old_thread_map.spec_index(t_ptr).view().state
                &&& new_thread_map.spec_index(t_ptr).view().owning_proc == old_thread_map.spec_index(t_ptr).view().owning_proc
            },
        forall|cpu_i: CpuId|
            #![trigger new_cpu_array.spec_index(cpu_i)]
            index_valid(NUM_CPUS, cpu_i) ==> {
                &&& new_cpu_array.spec_index(cpu_i).view().view().view().state == old_cpu_array.spec_index(cpu_i).view().view().view().state
                &&& new_cpu_array.spec_index(cpu_i).view().view().view().current_thread == old_cpu_array.spec_index(cpu_i).view().view().view().current_thread
                &&& new_cpu_array.spec_index(cpu_i).view().view().view().current_process == old_cpu_array.spec_index(cpu_i).view().view().view().current_process
            },
        forall|cpu_i: CpuId| #![trigger new_cpu_array.spec_index(cpu_i).view().being_killed()]
            index_valid(NUM_CPUS, cpu_i) && new_cpu_array.spec_index(cpu_i).view().being_killed() ==> old_cpu_array.spec_index(cpu_i).view().being_killed()
                && new_cpu_array.spec_index(cpu_i).view().killer_info() == old_cpu_array.spec_index(cpu_i).view().killer_info()
                && new_cpu_array.spec_index(cpu_i).view().locking_thread() == old_cpu_array.spec_index(cpu_i).view().locking_thread(),
        forall|t_ptr: RwLockThreadPtr| #![trigger new_thread_map.spec_index(t_ptr).killer_info()]
            old_thread_map.dom().contains(t_ptr) && old_thread_map.spec_index(t_ptr).view().state is RUNNING && old_thread_map.spec_index(t_ptr).being_killed()
                ==> new_thread_map.spec_index(t_ptr).killer_info() == old_thread_map.spec_index(t_ptr).killer_info()
                && new_thread_map.spec_index(t_ptr).locking_thread() == old_thread_map.spec_index(t_ptr).locking_thread(),
    ensures
        thread_cpu_wf(new_thread_map, new_cpu_array),
{ reveal(thread_cpu_wf); }

pub proof fn container_endpoint_wf_preserved_for_endpoint_owner_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_endpoint_map: EndpointLockedMap, new_endpoint_map: EndpointLockedMap)
    requires
        container_endpoint_wf(old_container_map, old_endpoint_map),
        new_container_map.dom() == old_container_map.dom(),
        new_endpoint_map.dom() == old_endpoint_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view_ghost().owned_endpoints == old_container_map.spec_index(c_ptr).view_ghost().owned_endpoints,
        forall|e_ptr: RwLockEndpointPtr|
            #![trigger new_endpoint_map.spec_index(e_ptr)]
            new_endpoint_map.dom().contains(e_ptr) ==> new_endpoint_map.spec_index(e_ptr).view().owning_container == old_endpoint_map.spec_index(e_ptr).view().owning_container,
    ensures
        container_endpoint_wf(new_container_map, new_endpoint_map),
{ reveal(container_endpoint_wf); }

pub proof fn container_scheduler_wf_preserved_for_scheduler_owner_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_scheduler_map: SchedulerUnLockedMap, new_scheduler_map: SchedulerUnLockedMap)
    requires
        container_scheduler_wf(old_container_map, old_scheduler_map),
        new_container_map.dom() == old_container_map.dom(),
        new_scheduler_map.dom() == old_scheduler_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view_rodata().view().scheduler == old_container_map.spec_index(c_ptr).view_rodata().view().scheduler,
        forall|s_ptr: RwLockSchedulerPtr|
            #![trigger new_scheduler_map.spec_index(s_ptr)]
            new_scheduler_map.dom().contains(s_ptr) ==> new_scheduler_map.spec_index(s_ptr).owning_container == old_scheduler_map.spec_index(s_ptr).owning_container,
    ensures
        container_scheduler_wf(new_container_map, new_scheduler_map),
{ reveal(container_scheduler_wf); }

pub proof fn container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_flags_map: CpuOfflineFlagsUnLockedMap, new_flags_map: CpuOfflineFlagsUnLockedMap)
    requires
        container_cpu_offline_flags_wf(old_container_map, old_flags_map),
        new_container_map.dom() == old_container_map.dom(),
        new_flags_map.dom() == old_flags_map.dom(),
        forall|flags_ptr: RwLockCpuOfflineFlagsPtr|
            #![trigger new_flags_map.spec_index(flags_ptr)]
            new_flags_map.dom().contains(flags_ptr) ==> new_flags_map.spec_index(flags_ptr).owning_container == old_flags_map.spec_index(flags_ptr).owning_container
                && new_flags_map.spec_index(flags_ptr).container_depth == old_flags_map.spec_index(flags_ptr).container_depth,
        forall|c_ptr: RwLockContainerPtr| #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view_rodata().view().depth == old_container_map.spec_index(c_ptr).view_rodata().view().depth,
    ensures
        container_cpu_offline_flags_wf(new_container_map, new_flags_map),
{ reveal(container_cpu_offline_flags_wf); }

pub proof fn container_cpu_wf_preserved_for_container_cpu_fields_eq(old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, cpu_array: CpuLockedArray)
    requires
        container_cpu_wf(old_container_map, cpu_set_map, cpu_array),
        new_container_map.dom() == old_container_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr)]
            new_container_map.dom().contains(c_ptr) ==> {
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().cpu_set == old_container_map.spec_index(c_ptr).view_rodata().view().cpu_set
                &&& new_container_map.spec_index(c_ptr).view_rodata().view().depth == old_container_map.spec_index(c_ptr).view_rodata().view().depth
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_processes == old_container_map.spec_index(c_ptr).view_ghost().owned_processes
                &&& new_container_map.spec_index(c_ptr).view_ghost().owned_threads == old_container_map.spec_index(c_ptr).view_ghost().owned_threads
            },
    ensures
        container_cpu_wf(new_container_map, cpu_set_map, cpu_array),
{ reveal(container_cpu_wf); }

pub proof fn cpu_offline_flags_wf_preserved_for_cpu_owner_eq(flags_map: CpuOfflineFlagsUnLockedMap, old_cpu_array: CpuLockedArray, new_cpu_array: CpuLockedArray)
    requires
        cpu_offline_flags_wf(flags_map, old_cpu_array),
        forall|cpu_id: CpuId|
            #![trigger new_cpu_array.spec_index(cpu_id)]
            index_valid(NUM_CPUS, cpu_id) ==> {
                &&& new_cpu_array.spec_index(cpu_id).view().view().view().owning_container == old_cpu_array.spec_index(cpu_id).view().view().view().owning_container
                &&& (new_cpu_array.spec_index(cpu_id).view().view().view().state is Off ==> new_cpu_array.spec_index(cpu_id).view().view().view().state == old_cpu_array.spec_index(cpu_id).view().view().view().state)
            },
    ensures
        cpu_offline_flags_wf(flags_map, new_cpu_array),
{ reveal(cpu_offline_flags_wf); }
} // verus!

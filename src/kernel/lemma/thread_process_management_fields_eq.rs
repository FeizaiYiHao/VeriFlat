use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn thread_process_management_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
        {
            &&& post.spec_index(t_ptr).view().state
                == pre.spec_index(t_ptr).view().state
            &&& post.spec_index(t_ptr).view().caller
                == pre.spec_index(t_ptr).view().caller
            &&& post.spec_index(t_ptr).view().callee
                == pre.spec_index(t_ptr).view().callee
            &&& post.spec_index(t_ptr).view().owning_container
                == pre.spec_index(t_ptr).view().owning_container
            &&& post.spec_index(t_ptr).view().container_depth
                == pre.spec_index(t_ptr).view().container_depth
            &&& post.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()
                == pre.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()
            &&& post.spec_index(t_ptr).view().owning_proc
                == pre.spec_index(t_ptr).view().owning_proc
            &&& post.spec_index(t_ptr).view().process_depth
                == pre.spec_index(t_ptr).view().process_depth
            &&& post.spec_index(t_ptr).view().proc_pagetable_ptr
                == pre.spec_index(t_ptr).view().proc_pagetable_ptr
            &&& post.spec_index(t_ptr).view().proc_linkedlist_node.addr()
                == pre.spec_index(t_ptr).view().proc_linkedlist_node.addr()
            &&& post.spec_index(t_ptr).view().endpoint_descriptors
                == pre.spec_index(t_ptr).view().endpoint_descriptors
            &&& post.spec_index(t_ptr).view().blocking_endpoint_ptr
                == pre.spec_index(t_ptr).view().blocking_endpoint_ptr
            &&& post.spec_index(t_ptr).view().endpoint_linkedlist_node.addr()
                == pre.spec_index(t_ptr).view().endpoint_linkedlist_node.addr()
            &&& post.spec_index(t_ptr).view().upper_container_seq
                == pre.spec_index(t_ptr).view().upper_container_seq
        }
}

pub proof fn thread_invariant_fields_unchanged_implies_process_management_fields(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        thread_invariant_fields_unchanged(pre, post),
    ensures
        thread_process_management_fields_unchanged(pre, post),
{
    reveal(thread_invariant_fields_unchanged);
}

pub proof fn thread_caller_callee_wf_preserved_for_thread_process_management_fields(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        thread_caller_callee_wf(pre),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        thread_caller_callee_wf(post),
{
    reveal(thread_caller_callee_wf);
}

pub proof fn thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    endpoint_map: EndpointLockedMap,
)
    requires
        thread_endpoint_ref_counter_wf(pre, endpoint_map),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        thread_endpoint_ref_counter_wf(post, endpoint_map),
{
    reveal(thread_endpoint_ref_counter_wf);
}

pub proof fn thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    endpoint_map: EndpointLockedMap,
)
    requires
        thread_endpoint_queue_wf(pre, endpoint_map),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        thread_endpoint_queue_wf(post, endpoint_map),
{
    reveal(thread_endpoint_queue_wf);
}

pub proof fn container_thread_endpoint_wf_preserved_for_thread_process_management_fields(
    container_map: ContainerLockedMap,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    endpoint_map: EndpointLockedMap,
)
    requires
        container_thread_endpoint_wf(container_map, pre, endpoint_map),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        container_thread_endpoint_wf(container_map, post, endpoint_map),
{
    reveal(container_thread_endpoint_wf);
}

pub proof fn container_thread_scheduler_wf_preserved_for_thread_process_management_fields(
    container_map: ContainerLockedMap,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    scheduler_map: SchedulerLockedMap,
)
    requires
        container_thread_scheduler_wf(container_map, pre, scheduler_map),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        container_thread_scheduler_wf(container_map, post, scheduler_map),
{
    reveal(container_thread_scheduler_wf);
}

pub proof fn container_thread_wf_preserved_for_thread_process_management_fields(
    container_map: ContainerLockedMap,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        container_thread_wf(container_map, pre),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        container_thread_wf(container_map, post),
{
    reveal(container_thread_wf);
}

pub proof fn process_thread_wf_preserved_for_thread_process_management_fields(
    process_map: ProcessLockedMap,
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
)
    requires
        process_thread_wf(process_map, pre),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        process_thread_wf(process_map, post),
{
    reveal(process_thread_wf);
}

pub proof fn thread_cpu_wf_preserved_for_thread_process_management_fields(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    cpu_array: CpuLockedArray,
)
    requires
        thread_cpu_wf(pre, cpu_array),
        thread_process_management_fields_unchanged(pre, post),
    ensures
        thread_cpu_wf(post, cpu_array),
{
    reveal(thread_cpu_wf);
}

}

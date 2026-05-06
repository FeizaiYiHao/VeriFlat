use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    pub proof fn container_process_wf_proof()
        ensures
            forall|container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>|
                container_process_wf(container_perms, process_perms) <==> container_process_wf_inner(container_perms, process_perms),
    {}

    pub closed spec fn container_process_wf(container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>) -> bool{
        container_process_wf_inner(container_perms, process_perms)
    }

    pub open spec fn container_process_wf_inner(container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>) -> bool{
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().root_process]
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes]
            container_perms.dom().contains(c_ptr)
            ==>
            {
                &&&
                process_perms.dom().contains(container_perms.spec_index(c_ptr).view().root_process)
                &&&
                container_perms.spec_index(c_ptr).view().owned_processes.view().contains(container_perms.spec_index(c_ptr).view().root_process)
                &&&
                container_perms.spec_index(c_ptr).view().owned_processes.view().subset_of(process_perms.dom())
            }
        &&&
        forall|c_ptr:RwLockContainerPtr, p_ptr:RwLockProcessPtr|
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes, process_perms.spec_index(p_ptr).view().owning_container]
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes.view().contains(p_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().owned_processes.view().contains(p_ptr)
            ==>
            {
                &&&
                process_perms.spec_index(p_ptr).view().owning_container == c_ptr
            }
        &&&
        forall|p_ptr:RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().owning_container]
            process_perms.dom().contains(p_ptr)
            ==>
            {
                &&&
                container_perms.dom().contains(process_perms.spec_index(p_ptr).view().owning_container)
                &&&
                container_perms.spec_index(process_perms.spec_index(p_ptr).view().owning_container).view().owned_processes.view().contains(p_ptr)
            }
    }

    pub proof fn per_container_process_tree_wf_proof()
        ensures 
            forall|container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>|
                per_container_process_tree_wf(container_perms, process_perms) <==> per_container_process_tree_wf_inner(container_perms, process_perms)
    {

    }

    pub closed spec fn per_container_process_tree_wf(container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>) -> bool{
        per_container_process_tree_wf_inner(container_perms, process_perms)
    } 

    pub open spec fn per_container_process_tree_wf_inner(container_perms: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>) -> bool
        recommends
            container_process_wf_inner(container_perms, process_perms),
    {
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().root_process]
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes]
            container_perms.dom().contains(c_ptr)
            ==>
            process_tree_wf(container_perms.spec_index(c_ptr).view().root_process, container_perms.spec_index(c_ptr).view().owned_processes@, process_perms)
    }
    
}
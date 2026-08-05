use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_process_wf(container_perms: ContainerLockedMap, process_perms: ProcessLockedMap) -> bool {
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
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes, process_perms.spec_index(p_ptr).view_rodata().view().owning_container]
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes.view().contains(p_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().owned_processes.view().contains(p_ptr)
            ==>
            {
                &&&
                process_perms.spec_index(p_ptr).view_rodata().view().owning_container == c_ptr
            }
        &&&
        forall|p_ptr:RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_rodata().view().owning_container]
            process_perms.dom().contains(p_ptr)
            ==>
            {
                &&&
                container_perms.dom().contains(process_perms.spec_index(p_ptr).view_rodata().view().owning_container)
                &&&
                container_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().owning_container).view().owned_processes.view().contains(p_ptr)
                &&&
                container_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().owning_container).view_rodata().view().depth == 
                    process_perms.spec_index(p_ptr).view_rodata().view().container_depth
            }
    }

    #[verifier::opaque]
    pub open spec fn per_container_process_tree_wf(container_perms: ContainerLockedMap, process_perms: ProcessLockedMap) -> bool
        recommends
            container_process_wf(container_perms, process_perms),
    {
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().root_process]
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes]
            container_perms.dom().contains(c_ptr)
            ==>
            process_tree_wf(container_perms.spec_index(c_ptr).view().root_process, container_perms.spec_index(c_ptr).view().owned_processes.view(), process_perms)
    }
    
}

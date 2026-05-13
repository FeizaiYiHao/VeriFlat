use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub proof fn container_process_allocator_quota_proof()
            ensures 
                forall|container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, 
                    process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>,
                    allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
                    allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
                    allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,|
                container_process_allocator_quota_wf(container_map, process_map, allocator_4k_map, allocator_2m_map, allocator_1g_map)
                <==> 
                {
                    &&&
                    container_process_allocator_quota_4k_wf_inner(container_map, process_map, allocator_4k_map)
                    &&&
                    container_process_allocator_quota_2m_wf_inner(container_map, process_map, allocator_2m_map)
                    &&&
                    container_process_allocator_quota_1g_wf_inner(container_map, process_map, allocator_1g_map)
                }
        {}

        pub closed spec fn container_process_allocator_quota_wf(
                container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, 
                process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>,
                allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
                allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
                allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        ) -> bool {
            &&&
            container_process_allocator_quota_4k_wf_inner(container_map, process_map, allocator_4k_map)
            &&&
            container_process_allocator_quota_2m_wf_inner(container_map, process_map, allocator_2m_map)
            &&&
            container_process_allocator_quota_1g_wf_inner(container_map, process_map, allocator_1g_map)
        }

    pub open spec fn container_process_allocator_quota_4k_wf_inner(
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, 
            process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>,
            allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool{
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                container_map.dom().contains(c_ptr) 
                ==>
                container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr:RwLockProcessPtr| {sum + process_map.spec_index(p_ptr).view().quota_4k})
                    == 
                    allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
        }
    pub open spec fn container_process_allocator_quota_2m_wf_inner(
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, 
            process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>,
            allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool{
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                container_map.dom().contains(c_ptr) 
                ==>
                container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr:RwLockProcessPtr| {sum + process_map.spec_index(p_ptr).view().quota_2m})
                    == 
                    allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
        }
    pub open spec fn container_process_allocator_quota_1g_wf_inner(
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, 
            process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>,
            allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool{
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                container_map.dom().contains(c_ptr) 
                ==>
                container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr:RwLockProcessPtr| {sum + process_map.spec_index(p_ptr).view().quota_1g})
                    == 
                    allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
        }
}
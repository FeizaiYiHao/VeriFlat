use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub open spec fn container_process_allocator_quota_wf(
                container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
                process_map: ProcessLockedMap,
                thread_map: ThreadLockedMap,
                allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
                allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
                allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        ) -> bool {
            &&&
            container_process_allocator_quota_4k_wf(container_map, process_map, thread_map, allocator_4k_map)
            &&&
            container_process_allocator_quota_2m_wf(container_map, process_map, thread_map, allocator_2m_map)
            &&&
            container_process_allocator_quota_1g_wf(container_map, process_map, thread_map, allocator_1g_map)
        }

    pub open spec fn process_effective_quota_4k_fold_sum(
            owned_processes: Set<RwLockProcessPtr>,
            process_map: ProcessLockedMap,
        ) -> int {
            owned_processes.fold(0, |sum: int, p_ptr:RwLockProcessPtr| {sum + process_effective_quota_4k(process_map.spec_index(p_ptr))})
        }

    pub open spec fn process_effective_quota_2m_fold_sum(
            owned_processes: Set<RwLockProcessPtr>,
            process_map: ProcessLockedMap,
        ) -> int {
            owned_processes.fold(0, |sum: int, p_ptr:RwLockProcessPtr| {sum + process_effective_quota_2m(process_map.spec_index(p_ptr))})
        }

    pub open spec fn process_effective_quota_1g_fold_sum(
            owned_processes: Set<RwLockProcessPtr>,
            process_map: ProcessLockedMap,
        ) -> int {
            owned_processes.fold(0, |sum: int, p_ptr:RwLockProcessPtr| {sum + process_effective_quota_1g(process_map.spec_index(p_ptr))})
        }

    #[verifier::opaque]
    pub open spec fn container_process_allocator_quota_4k_wf(
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
            process_map: ProcessLockedMap,
            thread_map: ThreadLockedMap,
            allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool
            recommends
            // container_allocator_wf
        {
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                container_map.dom().contains(c_ptr)
                ==>
                process_effective_quota_4k_fold_sum(container_map.spec_index(c_ptr).view().owned_processes.view(), process_map)
                    +
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr:RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                    +
                    container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr:RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    +
                    allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                    ==
                    allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
        }

    #[verifier::opaque]
    pub open spec fn container_process_allocator_quota_2m_wf(
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
            process_map: ProcessLockedMap,
            thread_map: ThreadLockedMap,
            allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool{
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                container_map.dom().contains(c_ptr)
                ==>
                process_effective_quota_2m_fold_sum(container_map.spec_index(c_ptr).view().owned_processes.view(), process_map)
                    +
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr:RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                    +
                    container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr:RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    +
                    allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                    ==
                    allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
        }

    #[verifier::opaque]
    pub open spec fn container_process_allocator_quota_1g_wf(
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
            process_map: ProcessLockedMap,
            thread_map: ThreadLockedMap,
            allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool{
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                container_map.dom().contains(c_ptr)
                ==>
                process_effective_quota_1g_fold_sum(container_map.spec_index(c_ptr).view().owned_processes.view(), process_map)
                    +
                    container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr:RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                    +
                    container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr:RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                    +
                    allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                    ==
                    allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
        }
}

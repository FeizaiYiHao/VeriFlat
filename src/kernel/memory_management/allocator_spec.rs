use vstd::prelude::*;
use crate::*;
verus! {
    #[verifier::opaque]
    pub open spec fn allocator_perms_wf(alloc_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool {
        &&&
        alloc_map.perms_wf()
        &&&
        forall|a_ptr:RwLockPageAllocatorPtr|
            #![auto]
            alloc_map.dom().contains(a_ptr)
            ==>
            alloc_map.spec_index(a_ptr).inv()
    }


    pub open spec fn allocator_free_page_ptrs_wf(allocator_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool{
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
            allocator_map.dom().contains(alloc_ptr) && allocator_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
            ==>
            page_ptr_valid(page_ptr)
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
            #![trigger allocator_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            allocator_map.dom().contains(alloc_ptr) && 
            cpu_id_valid(cpu_i) &&
            allocator_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
            ==>
            page_ptr_valid(page_ptr)  
    }

    // pub closed spec fn free_pages_4k_addr_wf(allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool{
    //     &&&
    //     forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
    //         #![trigger allocator_4k_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
    //         allocator_4k_map.dom().contains(alloc_ptr) && allocator_4k_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
    //         ==>
    //         page_ptr_valid(page_ptr)
    //     &&&
    //     forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
    //         #![trigger allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
    //         allocator_4k_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr) && 
    //             allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    //         ==>
    //         page_ptr_valid(page_ptr)  
    // }

    // pub closed spec fn free_pages_2m_addr_wf(allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool{
    //     &&&
    //     forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
    //         #![trigger allocator_2m_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
    //         allocator_2m_map.dom().contains(alloc_ptr) && allocator_2m_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
    //         ==>
    //         page_ptr_2m_valid(page_ptr)
    //     &&&
    //     forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
    //         #![trigger allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
    //         allocator_2m_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr) && 
    //             allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    //         ==>
    //         page_ptr_2m_valid(page_ptr)  
    // }

    // pub closed spec fn free_pages_1g_addr_wf(allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool{
    //     &&&
    //     forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
    //         #![trigger allocator_1g_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
    //         allocator_1g_map.dom().contains(alloc_ptr) && allocator_1g_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
    //         ==>
    //         page_ptr_2m_valid(page_ptr)
    //     &&&
    //     forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
    //         #![trigger allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
    //         allocator_1g_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr) && 
    //             allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    //         ==>
    //         page_ptr_2m_valid(page_ptr)  
    // }
}
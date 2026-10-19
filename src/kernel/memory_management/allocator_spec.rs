use vstd::prelude::*;
use crate::*;
verus! {
    #[verifier::opaque]
    pub open spec fn allocator_perms_wf<const SIZE: usize>(alloc_map: PageAllocatorUnLockedMap<SIZE>) -> bool {
        &&& alloc_map.perms_wf()
        &&& forall|a_ptr:RwLockPageAllocatorPtr| #![auto] alloc_map.dom().contains(a_ptr) ==> alloc_map.spec_index(a_ptr).inv()
    }

    pub proof fn allocator_perms_wf_at<const SIZE: usize>(alloc_map: PageAllocatorUnLockedMap<SIZE>, alloc_ptr: RwLockPageAllocatorPtr)
        requires
            allocator_perms_wf(alloc_map),
            alloc_map.dom().contains(alloc_ptr),
        ensures
            alloc_map.spec_index(alloc_ptr).inv(),
    { reveal(allocator_perms_wf); }

    pub proof fn allocator_perms_wf_map<const SIZE: usize>(alloc_map: PageAllocatorUnLockedMap<SIZE>)
        requires allocator_perms_wf(alloc_map)
        ensures alloc_map.perms_wf()
    { reveal(allocator_perms_wf); }

    #[verifier::opaque]
    pub open spec fn allocator_free_page_ptrs_wf<const SIZE: usize>(allocator_map: PageAllocatorUnLockedMap<SIZE>) -> bool {
        &&& forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_map.dom().contains(alloc_ptr), page_ptr_valid(page_ptr)]
            #![trigger allocator_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            allocator_map.dom().contains(alloc_ptr) && allocator_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr) ==> page_ptr_valid(page_ptr)
        &&& forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
            #![trigger allocator_map.dom().contains(alloc_ptr), index_valid(NUM_CPUS, cpu_i), page_ptr_valid(page_ptr)]
            #![trigger allocator_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            allocator_map.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) && allocator_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr) ==> page_ptr_valid(page_ptr)
    }

    /// A page in allocator `alloc_ptr`'s global pool has a valid page pointer.
    pub proof fn allocator_free_page_ptrs_wf_global_at<const SIZE: usize>(allocator_map: PageAllocatorUnLockedMap<SIZE>, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr)
        requires
            allocator_free_page_ptrs_wf(allocator_map),
            allocator_map.dom().contains(alloc_ptr),
        ensures allocator_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr) ==> page_ptr_valid(page_ptr),
    { reveal(allocator_free_page_ptrs_wf); }

    /// A page in allocator `alloc_ptr`'s CPU `cpu_i` cache has a valid page pointer.
    pub proof fn allocator_free_page_ptrs_wf_cache_at<const SIZE: usize>(allocator_map: PageAllocatorUnLockedMap<SIZE>, alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr)
        requires
            allocator_free_page_ptrs_wf(allocator_map),
            allocator_map.dom().contains(alloc_ptr),
            index_valid(NUM_CPUS, cpu_i),
        ensures allocator_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr) ==> page_ptr_valid(page_ptr),
    { reveal(allocator_free_page_ptrs_wf); }
}

use vstd::prelude::*;
use crate::*;
verus! {
/// The allocator lock map is well-formed and every allocator satisfies inv().
#[verifier::opaque]
pub open spec fn allocator_perms_wf<const SIZE: usize>(allc_mp: PageAllocatorUnLockedMap<SIZE>) -> bool {
    &&& allc_mp.perms_wf()
    &&& forall|a: RwLockPageAllocatorPtr|
        #![auto]
        allc_mp.dom().contains(a) ==> allc_mp.spec_index(a).inv()
}

pub proof fn allocator_perms_wf_at<const SIZE: usize>(allc_mp: PageAllocatorUnLockedMap<SIZE>, allc_ptr: RwLockPageAllocatorPtr)
    requires
        allocator_perms_wf(allc_mp),
        allc_mp.dom().contains(allc_ptr),
    ensures
        allc_mp.spec_index(allc_ptr).inv(),
{ reveal(allocator_perms_wf); }

pub proof fn allocator_perms_wf_map<const SIZE: usize>(allc_mp: PageAllocatorUnLockedMap<SIZE>)
    requires allocator_perms_wf(allc_mp)
    ensures allc_mp.perms_wf()
{ reveal(allocator_perms_wf); }

/// A page in an allocator's global pool or in one of its CPU caches has a valid page pointer.
#[verifier::opaque]
pub open spec fn allocator_free_page_ptrs_wf<const SIZE: usize>(allc_mp: PageAllocatorUnLockedMap<SIZE>) -> bool {
    &&& forall|a: RwLockPageAllocatorPtr, pg_ptr: PagePtr|
        #![trigger allc_mp.dom().contains(a), page_ptr_valid(pg_ptr)]
        #![trigger allc_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)]
        allc_mp.dom().contains(a) && allc_mp.spec_index(a).global_pool.view().view().contains(pg_ptr) ==> page_ptr_valid(pg_ptr)
    &&& forall|a: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr|
        #![trigger allc_mp.dom().contains(a), index_valid(NUM_CPUS, cpu_id), page_ptr_valid(pg_ptr)]
        #![trigger allc_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)]
        allc_mp.dom().contains(a)
            && index_valid(NUM_CPUS, cpu_id)
            && allc_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)
            ==>
            page_ptr_valid(pg_ptr)
}

/// A page in allocator `allc_ptr`'s global pool has a valid page pointer.
pub proof fn allocator_free_page_ptrs_wf_global_at<const SIZE: usize>(allc_mp: PageAllocatorUnLockedMap<SIZE>, allc_ptr: RwLockPageAllocatorPtr, pg_ptr: PagePtr)
    requires
        allocator_free_page_ptrs_wf(allc_mp),
        allc_mp.dom().contains(allc_ptr),
    ensures allc_mp.spec_index(allc_ptr).global_pool.view().view().contains(pg_ptr) ==> page_ptr_valid(pg_ptr),
{ reveal(allocator_free_page_ptrs_wf); }

/// A page in allocator `allc_ptr`'s CPU `cpu_id` cache has a valid page pointer.
pub proof fn allocator_free_page_ptrs_wf_cache_at<const SIZE: usize>(
    allc_mp: PageAllocatorUnLockedMap<SIZE>, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr,
)
    requires
        allocator_free_page_ptrs_wf(allc_mp),
        allc_mp.dom().contains(allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures allc_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr) ==> page_ptr_valid(pg_ptr),
{ reveal(allocator_free_page_ptrs_wf); }
}

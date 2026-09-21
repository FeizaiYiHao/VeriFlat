use vstd::prelude::*;
use crate::*;

verus! {
pub(crate) open spec fn allocator_cache_lock_id(cache_cpu: CpuId) -> LockId {
    LockId {
        container: LockOwnerId::NotApp,
        process: LockOwnerId::NotApp,
        major: ALLOCATOR_CACHE_MAJOR,
        minor: cache_cpu,
    }
}

#[verifier::opaque]
pub(crate) open spec fn allocator_caches_unlocked(alloc_map: PageAllocatorUnLockedMap, alloc_ptr: RwLockPageAllocatorPtr) -> bool {
    forall|c: CpuId|
        #![trigger alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(c)]
        index_valid(NUM_CPUS, c) ==> !alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(c).view().locked()
}

pub(crate) open spec fn allocator_cache_key_prefix_seq(alloc_ptr: RwLockPageAllocatorPtr, upper: CpuId) -> Seq<(RwLockPageAllocatorPtr, CpuId)> {
    Seq::new(upper as nat, |i: int| (alloc_ptr, i as CpuId))
}

pub(crate) open spec fn allocator_cache_key_prefix(alloc_ptr: RwLockPageAllocatorPtr, upper: CpuId) -> Set<(RwLockPageAllocatorPtr, CpuId)> {
    allocator_cache_key_prefix_seq(alloc_ptr, upper).to_set()
}
}

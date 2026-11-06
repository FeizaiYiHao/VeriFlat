use vstd::prelude::*;
use crate::*;

verus! {
/// A free 4K page on the global list sits, under its free-list node address, in the global pool of the allocator its state
/// names, and that allocator shares the page's container.
pub open spec fn allocator_global_pool_4k_pages_forward_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::GlobalList })
            ==> {
                let allc_ptr = pg_arr.spec_index(p_i).view().view().state->Free4k_allocator_ptr.view();
                &&& allc_4k_mp.dom().contains(allc_ptr)
                &&& allc_4k_mp.spec_index(allc_ptr).owning_container == pg_arr.spec_index(p_i).view().view().owning_container
                &&& allc_4k_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(p_i))
                &&& allc_4k_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr())
                &&& allc_4k_mp.spec_index(allc_ptr).global_pool.view().map().spec_index(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()) == page_index2page_ptr(p_i)
            }
}

/// A page in a 4K allocator's global pool is free on the global list of that allocator and shares its container.
pub open spec fn allocator_global_pool_4k_pages_backward_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    forall|a: RwLockPageAllocatorPtr, pg_ptr: PagePtr|
        #![trigger allc_4k_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)]
        #![trigger allc_4k_mp.dom().contains(a), page_ptr2page_index(pg_ptr)]
        allc_4k_mp.dom().contains(a)
            && allc_4k_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)
            ==>
            pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(a), state: FreePageAllocatorState::GlobalList })
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_4k_mp.spec_index(a).owning_container
}

/// Free 4K pages on the global list and the 4K allocators' global pools agree in both directions.
// Proof dependencies (confirmed for global-pool page removal): allocator_perms_wf, allocator_free_page_ptrs_wf.
#[verifier::opaque]
pub open spec fn allocator_global_pool_4k_pages_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_global_pool_4k_pages_forward_wf(allc_4k_mp, pg_arr)
    &&& allocator_global_pool_4k_pages_backward_wf(allc_4k_mp, pg_arr)
}

/// Free 4K pages in CPU caches and the 4K allocators' CPU caches agree in both directions.
#[verifier::opaque]
pub open spec fn allocator_cpu_cache_4k_pages_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    // A free 4K page in a CPU cache sits, under its free-list node address, in that CPU's cache of the allocator its state names.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state->Free4k_allocator_ptr]
        #![trigger pg_arr.spec_index(p_i).view().view().state->Free4k_state->PreCpuCache_cpu_id]
        #![trigger pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { .. } })
            ==> {
                let allc_ptr = pg_arr.spec_index(p_i).view().view().state->Free4k_allocator_ptr.view();
                let cpu_id = pg_arr.spec_index(p_i).view().view().state->Free4k_state->PreCpuCache_cpu_id;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allc_4k_mp.dom().contains(allc_ptr)
                &&& allc_4k_mp.spec_index(allc_ptr).owning_container == pg_arr.spec_index(p_i).view().view().owning_container
                &&& allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(p_i))
                &&& allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr())
                &&& allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()) == page_index2page_ptr(p_i)
            }
    // A page in a 4K allocator's CPU cache is free in that cache and shares the allocator's container.
    &&& forall|a: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state, allc_4k_mp.dom().contains(a), index_valid(NUM_CPUS, cpu_id)]
        allc_4k_mp.dom().contains(a)
            && index_valid(NUM_CPUS, cpu_id)
            && allc_4k_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)
            ==>
            pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(a), state: FreePageAllocatorState::PreCpuCache { cpu_id } })
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_4k_mp.spec_index(a).owning_container
}

/// Free 4K pages and the 4K allocators' global pools and CPU caches agree.
// Proof dependencies (confirmed for nonfree-page preservation): page_array_wf, allocator_free_page_ptrs_wf.
#[verifier::opaque]
pub open spec fn allocator_free_4k_pages_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_global_pool_4k_pages_wf(allc_4k_mp, pg_arr)
    &&& allocator_cpu_cache_4k_pages_wf(allc_4k_mp, pg_arr)
}

/// A free page `pg_idx` sits, under its free-list node address, in the global pool or CPU cache that its state names.
pub proof fn allocator_free_4k_pages_wf_at(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        allocator_free_4k_pages_wf(allc_4k_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let allc_ptr = page.state->Free4k_allocator_ptr.view();
            (page.state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                &&& allc_4k_mp.dom().contains(allc_ptr)
                &&& allc_4k_mp.spec_index(allc_ptr).owning_container == page.owning_container
                &&& allc_4k_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(pg_idx))
                &&& allc_4k_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(page.free_list_node_storage.addr())
                &&& allc_4k_mp.spec_index(allc_ptr).global_pool.view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(pg_idx)
            }
        }),
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let allc_ptr = page.state->Free4k_allocator_ptr.view();
            let cpu_id = page.state->Free4k_state->PreCpuCache_cpu_id;
            (page.state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { .. } }) ==> {
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allc_4k_mp.dom().contains(allc_ptr)
                &&& allc_4k_mp.spec_index(allc_ptr).owning_container == page.owning_container
                &&& allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(pg_idx))
                &&& allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page.free_list_node_storage.addr())
                &&& allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(pg_idx)
            }
        }),
{ reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); }

/// A page in allocator `allc_ptr`'s global pool is free on that global list and shares the allocator's container.
pub proof fn allocator_free_4k_pages_wf_global_at(
    allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr, pg_ptr: PagePtr,
)
    requires
        allocator_free_4k_pages_wf(allc_4k_mp, pg_arr),
        allc_4k_mp.dom().contains(allc_ptr),
    ensures
        allc_4k_mp.spec_index(allc_ptr).global_pool.view().view().contains(pg_ptr) ==> {
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_4k_mp.spec_index(allc_ptr).owning_container
        },
{ reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); }

/// A page in allocator `allc_ptr`'s CPU `cpu_id` cache is free in that cache and shares the allocator's container.
pub proof fn allocator_free_4k_pages_wf_cache_at(
    allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr,
)
    requires
        allocator_free_4k_pages_wf(allc_4k_mp, pg_arr),
        allc_4k_mp.dom().contains(allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr) ==> {
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_4k_mp.spec_index(allc_ptr).owning_container
        },
{ reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); }

/// Free 2M pages on the global list and the 2M allocators' global pools agree in both directions.
// Proof dependency (confirmed for cache-page removal): allocator_perms_wf.
#[verifier::opaque]
pub open spec fn allocator_global_pool_2m_pages_wf(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray) -> bool {
    // A free 2M page on the global list sits, under its free-list node address, in the global pool of the allocator its state names.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::GlobalList })
            ==> {
                let allc_ptr = pg_arr.spec_index(p_i).view().view().state->Free2m_allocator_ptr.view();
                &&& allc_2m_mp.dom().contains(allc_ptr)
                &&& allc_2m_mp.spec_index(allc_ptr).owning_container == pg_arr.spec_index(p_i).view().view().owning_container
                &&& allc_2m_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(p_i))
                &&& allc_2m_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr())
                &&& allc_2m_mp.spec_index(allc_ptr).global_pool.view().map().spec_index(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()) == page_index2page_ptr(p_i)
            }
    // A page in a 2M allocator's global pool is free on that global list and shares the allocator's container.
    &&& forall|a: RwLockPageAllocatorPtr, pg_ptr: PagePtr|
        #![trigger allc_2m_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)]
        allc_2m_mp.dom().contains(a)
            && allc_2m_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)
            ==>
            pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(a), state: FreePageAllocatorState::GlobalList })
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_2m_mp.spec_index(a).owning_container
}

/// Free 2M pages in CPU caches and the 2M allocators' CPU caches agree in both directions.
// Proof dependency (confirmed for CPU-cache pop): allocator_perms_wf.
#[verifier::opaque]
pub open spec fn allocator_cpu_cache_2m_pages_wf(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray) -> bool {
    // A free 2M page in a CPU cache sits, under its free-list node address, in that CPU's cache of the allocator its state names.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { .. } })
            ==> {
                let allc_ptr = pg_arr.spec_index(p_i).view().view().state->Free2m_allocator_ptr.view();
                let cpu_id = pg_arr.spec_index(p_i).view().view().state->Free2m_state->PreCpuCache_cpu_id;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allc_2m_mp.dom().contains(allc_ptr)
                &&& allc_2m_mp.spec_index(allc_ptr).owning_container == pg_arr.spec_index(p_i).view().view().owning_container
                &&& allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(p_i))
                &&& allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr())
                &&& allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()) == page_index2page_ptr(p_i)
            }
    // A page in a 2M allocator's CPU cache is free in that cache and shares the allocator's container.
    &&& forall|a: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr|
        #![trigger allc_2m_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)]
        allc_2m_mp.dom().contains(a)
            && index_valid(NUM_CPUS, cpu_id)
            && allc_2m_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)
            ==>
            pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(a), state: FreePageAllocatorState::PreCpuCache { cpu_id } })
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_2m_mp.spec_index(a).owning_container
}

/// Free 2M pages and the 2M allocators' global pools and CPU caches agree.
// Proof dependencies (confirmed for nonfree-page preservation): page_array_wf, allocator_free_page_ptrs_wf.
#[verifier::opaque]
pub open spec fn allocator_free_2m_pages_wf(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_global_pool_2m_pages_wf(allc_2m_mp, pg_arr)
    &&& allocator_cpu_cache_2m_pages_wf(allc_2m_mp, pg_arr)
}

/// A free 2M page `pg_idx` sits, under its free-list node address, in the global pool or CPU cache that its state names.
pub proof fn allocator_free_2m_pages_wf_at(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        allocator_free_2m_pages_wf(allc_2m_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let allc_ptr = page.state->Free2m_allocator_ptr.view();
            (page.state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                &&& allc_2m_mp.dom().contains(allc_ptr)
                &&& allc_2m_mp.spec_index(allc_ptr).owning_container == page.owning_container
                &&& allc_2m_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(pg_idx))
                &&& allc_2m_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(page.free_list_node_storage.addr())
                &&& allc_2m_mp.spec_index(allc_ptr).global_pool.view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(pg_idx)
            }
        }),
        ({
            let page = pg_arr.spec_index(pg_idx).view().view();
            let allc_ptr = page.state->Free2m_allocator_ptr.view();
            let cpu_id = page.state->Free2m_state->PreCpuCache_cpu_id;
            (page.state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { .. } }) ==> {
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allc_2m_mp.dom().contains(allc_ptr)
                &&& allc_2m_mp.spec_index(allc_ptr).owning_container == page.owning_container
                &&& allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(pg_idx))
                &&& allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page.free_list_node_storage.addr())
                &&& allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(pg_idx)
            }
        }),
{ reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); }

/// A page in allocator `allc_ptr`'s 2M global pool is free on that global list and shares the allocator's container.
pub proof fn allocator_free_2m_pages_wf_global_at(
    allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr, pg_ptr: PagePtr,
)
    requires
        allocator_free_2m_pages_wf(allc_2m_mp, pg_arr),
        allc_2m_mp.dom().contains(allc_ptr),
    ensures
        allc_2m_mp.spec_index(allc_ptr).global_pool.view().view().contains(pg_ptr) ==> {
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Free2m { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_2m_mp.spec_index(allc_ptr).owning_container
        },
{ reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); }

/// A page in allocator `allc_ptr`'s 2M CPU `cpu_id` cache is free in that cache and shares the allocator's container.
pub proof fn allocator_free_2m_pages_wf_cache_at(
    allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr,
)
    requires
        allocator_free_2m_pages_wf(allc_2m_mp, pg_arr),
        allc_2m_mp.dom().contains(allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr) ==> {
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Free2m { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_2m_mp.spec_index(allc_ptr).owning_container
        },
{ reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); }

/// Free 1G pages on the global list and the 1G allocators' global pools agree in both directions.
#[verifier::opaque]
pub open spec fn allocator_global_pool_1g_pages_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray) -> bool {
    // A free 1G page on the global list sits, under its free-list node address, in the global pool of the allocator its state names.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Free1g { allocator_ptr: _, state: FreePageAllocatorState::GlobalList })
            ==> {
                let allc_ptr = pg_arr.spec_index(p_i).view().view().state->Free1g_allocator_ptr.view();
                &&& allc_1g_mp.dom().contains(allc_ptr)
                &&& allc_1g_mp.spec_index(allc_ptr).owning_container == pg_arr.spec_index(p_i).view().view().owning_container
                &&& allc_1g_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(p_i))
                &&& allc_1g_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr())
                &&& allc_1g_mp.spec_index(allc_ptr).global_pool.view().map().spec_index(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()) == page_index2page_ptr(p_i)
            }
    // A page in a 1G allocator's global pool is free on that global list and shares the allocator's container.
    &&& forall|a: RwLockPageAllocatorPtr, pg_ptr: PagePtr|
        #![trigger allc_1g_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)]
        allc_1g_mp.dom().contains(a)
            && allc_1g_mp.spec_index(a).global_pool.view().view().contains(pg_ptr)
            ==>
            pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free1g { allocator_ptr: Ghost(a), state: FreePageAllocatorState::GlobalList })
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_1g_mp.spec_index(a).owning_container
}

/// Free 1G pages in CPU caches and the 1G allocators' CPU caches agree in both directions.
#[verifier::opaque]
pub open spec fn allocator_cpu_cache_1g_pages_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray) -> bool {
    // A free 1G page in a CPU cache sits, under its free-list node address, in that CPU's cache of the allocator its state names.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Free1g { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { .. } })
            ==> {
                let allc_ptr = pg_arr.spec_index(p_i).view().view().state->Free1g_allocator_ptr.view();
                let cpu_id = pg_arr.spec_index(p_i).view().view().state->Free1g_state->PreCpuCache_cpu_id;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allc_1g_mp.dom().contains(allc_ptr)
                &&& allc_1g_mp.spec_index(allc_ptr).owning_container == pg_arr.spec_index(p_i).view().view().owning_container
                &&& allc_1g_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(p_i))
                &&& allc_1g_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr())
                &&& allc_1g_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(pg_arr.spec_index(p_i).view().view().free_list_node_storage.addr()) == page_index2page_ptr(p_i)
            }
    // A page in a 1G allocator's CPU cache is free in that cache and shares the allocator's container.
    &&& forall|a: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr|
        #![trigger allc_1g_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)]
        allc_1g_mp.dom().contains(a)
            && index_valid(NUM_CPUS, cpu_id)
            && allc_1g_mp.spec_index(a).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)
            ==>
            pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free1g { allocator_ptr: Ghost(a), state: FreePageAllocatorState::PreCpuCache { cpu_id } })
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_1g_mp.spec_index(a).owning_container
}

/// Free 1G pages and the 1G allocators' global pools and CPU caches agree.
// Proof dependencies (confirmed for nonfree-page preservation): page_array_wf, allocator_free_page_ptrs_wf.
#[verifier::opaque]
pub open spec fn allocator_free_1g_pages_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_global_pool_1g_pages_wf(allc_1g_mp, pg_arr)
    &&& allocator_cpu_cache_1g_pages_wf(allc_1g_mp, pg_arr)
}

/// A page in allocator `allc_ptr`'s 1G global pool is free on that global list and shares the allocator's container.
pub proof fn allocator_free_1g_pages_wf_global_at(
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr, pg_ptr: PagePtr,
)
    requires
        allocator_free_1g_pages_wf(allc_1g_mp, pg_arr),
        allc_1g_mp.dom().contains(allc_ptr),
    ensures
        allc_1g_mp.spec_index(allc_ptr).global_pool.view().view().contains(pg_ptr) ==> {
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_1g_mp.spec_index(allc_ptr).owning_container
        },
{ reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); }

/// A page in allocator `allc_ptr`'s 1G CPU `cpu_id` cache is free in that cache and shares the allocator's container.
pub proof fn allocator_free_1g_pages_wf_cache_at(
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, pg_ptr: PagePtr,
)
    requires
        allocator_free_1g_pages_wf(allc_1g_mp, pg_arr),
        allc_1g_mp.dom().contains(allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        allc_1g_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr) ==> {
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            &&& pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == allc_1g_mp.spec_index(allc_ptr).owning_container
        },
{ reveal(allocator_free_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf); }

/// No CPU cache of a 1G allocator holds a page: 1G pages are allocated from and freed to the global pool only.
#[verifier::opaque]
pub open spec fn allocator_1g_cpu_caches_empty_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
    forall|a: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger allc_1g_mp.spec_index(a).cpu_caches.spec_index(c)]
        allc_1g_mp.dom().contains(a) && index_valid(NUM_CPUS, c)
            ==> allc_1g_mp.spec_index(a).cpu_caches.spec_index(c).view().view().view().len() == 0
}

/// CPU `cpu_id`'s cache of the 1G allocator `allc_ptr` holds no page.
pub proof fn allocator_1g_cpu_caches_empty_wf_at(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId)
    requires
        allocator_1g_cpu_caches_empty_wf(allc_1g_mp),
        allc_1g_mp.dom().contains(allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures allc_1g_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() == 0,
{ reveal(allocator_1g_cpu_caches_empty_wf); }
}

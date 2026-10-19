use vstd::prelude::*;
use crate::*;

verus! {
    // Proof dependencies (confirmed): allocator_4k_pages_wf,
    // allocator_2m_pages_wf, allocator_1g_pages_wf.
    pub open spec fn allocator_pages_wf(page_array: PageLockedArray, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        &&& allocator_4k_pages_wf(page_array, allocator_4k_map)
        &&& allocator_2m_pages_wf(page_array, allocator_2m_map)
        &&& allocator_1g_pages_wf(page_array, allocator_1g_map)
    }

    pub open spec fn allocator_4k_pages_forward_wf(page_array: PageLockedArray, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger allocator_4k_map.dom().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator})
                ==> allocator_4k_map.dom().contains(page_index2page_ptr(page_index))
    }

    pub open spec fn allocator_4k_pages_backward_wf(page_array: PageLockedArray, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
        forall|a_ptr:RwLockPageAllocatorPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(a_ptr))]
            #![trigger allocator_4k_map.dom().contains(a_ptr)]
            allocator_4k_map.dom().contains(a_ptr) ==> page_ptr_valid(a_ptr) && page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator}
    }

    #[verifier::opaque]
    pub open spec fn allocator_4k_pages_wf(page_array: PageLockedArray, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
        &&& allocator_4k_pages_forward_wf(page_array, allocator_4k_map)
        &&& allocator_4k_pages_backward_wf(page_array, allocator_4k_map)
    }

    pub open spec fn allocator_2m_pages_forward_wf(page_array: PageLockedArray, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger allocator_2m_map.dom().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator})
                ==> allocator_2m_map.dom().contains(page_index2page_ptr(page_index))
    }

    pub open spec fn allocator_2m_pages_backward_wf(page_array: PageLockedArray, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
        forall|a_ptr:RwLockPageAllocatorPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(a_ptr))]
            #![trigger allocator_2m_map.dom().contains(a_ptr)]
            allocator_2m_map.dom().contains(a_ptr) ==> page_ptr_valid(a_ptr) && page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator}
    }

    #[verifier::opaque]
    pub open spec fn allocator_2m_pages_wf(page_array: PageLockedArray, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
        &&& allocator_2m_pages_forward_wf(page_array, allocator_2m_map)
        &&& allocator_2m_pages_backward_wf(page_array, allocator_2m_map)
    }

    pub open spec fn allocator_1g_pages_forward_wf(page_array: PageLockedArray, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger allocator_1g_map.dom().contains(page_index2page_ptr(page_index))]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator})
                ==> allocator_1g_map.dom().contains(page_index2page_ptr(page_index))
    }

    pub open spec fn allocator_1g_pages_backward_wf(page_array: PageLockedArray, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        forall|a_ptr:RwLockPageAllocatorPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(a_ptr))]
            #![trigger allocator_1g_map.dom().contains(a_ptr)]
            allocator_1g_map.dom().contains(a_ptr) ==> page_ptr_valid(a_ptr) && page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator}
    }

    #[verifier::opaque]
    pub open spec fn allocator_1g_pages_wf(page_array: PageLockedArray, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        &&& allocator_1g_pages_forward_wf(page_array, allocator_1g_map)
        &&& allocator_1g_pages_backward_wf(page_array, allocator_1g_map)
    }

    pub proof fn allocator_4k_pages_wf_at(page_array: PageLockedArray, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, a_ptr: RwLockPageAllocatorPtr)
        requires allocator_4k_pages_wf(page_array, allocator_4k_map)
        ensures allocator_4k_map.dom().contains(a_ptr) ==> page_ptr_valid(a_ptr) && page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator},
    { reveal(allocator_4k_pages_wf); }

    pub proof fn allocator_2m_pages_wf_at(page_array: PageLockedArray, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, a_ptr: RwLockPageAllocatorPtr)
        requires allocator_2m_pages_wf(page_array, allocator_2m_map)
        ensures allocator_2m_map.dom().contains(a_ptr) ==> page_ptr_valid(a_ptr) && page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator},
    { reveal(allocator_2m_pages_wf); }

    pub proof fn allocator_1g_pages_wf_at(page_array: PageLockedArray, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, a_ptr: RwLockPageAllocatorPtr)
        requires allocator_1g_pages_wf(page_array, allocator_1g_map)
        ensures allocator_1g_map.dom().contains(a_ptr) ==> page_ptr_valid(a_ptr) && page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator},
    { reveal(allocator_1g_pages_wf); }

    pub open spec fn container_allocator_4k_forward_wf(container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
        forall|alloc_ptr:RwLockPageAllocatorPtr,|
            #![trigger allocator_4k_map.spec_index(alloc_ptr).owning_container]
            allocator_4k_map.dom().contains(alloc_ptr)
                ==> container_map.dom().contains(allocator_4k_map.spec_index(alloc_ptr).owning_container) && container_map.spec_index(allocator_4k_map.spec_index(alloc_ptr).owning_container).view_rodata().view().allocator_ptr_4k == alloc_ptr
    }

    pub open spec fn container_allocator_4k_backward_wf(container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
            container_map.dom().contains(c_ptr)
                ==> allocator_4k_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k)
                && allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).owning_container == c_ptr
                && allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
    }

    pub open spec fn container_allocator_2m_forward_wf(container_map: ContainerLockedMap, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
        forall|alloc_ptr:RwLockPageAllocatorPtr,|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).owning_container]
            allocator_2m_map.dom().contains(alloc_ptr)
                ==> container_map.dom().contains(allocator_2m_map.spec_index(alloc_ptr).owning_container) && container_map.spec_index(allocator_2m_map.spec_index(alloc_ptr).owning_container).view_rodata().view().allocator_ptr_2m == alloc_ptr
    }

    pub open spec fn container_allocator_2m_backward_wf(container_map: ContainerLockedMap, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
            container_map.dom().contains(c_ptr)
                ==> allocator_2m_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m)
                && allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).owning_container == c_ptr
                && allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
    }

    pub open spec fn container_allocator_1g_forward_wf(container_map: ContainerLockedMap, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        forall|alloc_ptr:RwLockPageAllocatorPtr,|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).owning_container]
            allocator_1g_map.dom().contains(alloc_ptr)
                ==> container_map.dom().contains(allocator_1g_map.spec_index(alloc_ptr).owning_container) && container_map.spec_index(allocator_1g_map.spec_index(alloc_ptr).owning_container).view_rodata().view().allocator_ptr_1g == alloc_ptr
    }

    pub open spec fn container_allocator_1g_backward_wf(container_map: ContainerLockedMap, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
            container_map.dom().contains(c_ptr)
                ==> allocator_1g_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g)
                && allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).owning_container == c_ptr
                && allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_wf(container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
        &&& container_allocator_4k_forward_wf(container_map, allocator_4k_map)
        &&& container_allocator_4k_backward_wf(container_map, allocator_4k_map)
        &&& container_allocator_2m_forward_wf(container_map, allocator_2m_map)
        &&& container_allocator_2m_backward_wf(container_map, allocator_2m_map)
        &&& container_allocator_1g_forward_wf(container_map, allocator_1g_map)
        &&& container_allocator_1g_backward_wf(container_map, allocator_1g_map)
    }

    /// Container `container_ptr`'s 4K, 2M, and 1G allocators exist, belong to it, and carry its depth.
    pub proof fn container_allocator_wf_at(container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
        allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, container_ptr: RwLockContainerPtr)
        requires
            container_allocator_wf(container_map, allocator_4k_map, allocator_2m_map, allocator_1g_map),
            container_map.dom().contains(container_ptr),
        ensures
            ({
                let ro = container_map.spec_index(container_ptr).view_rodata().view();
                &&& allocator_4k_map.dom().contains(ro.allocator_ptr_4k)
                &&& allocator_4k_map.spec_index(ro.allocator_ptr_4k).owning_container == container_ptr
                &&& allocator_4k_map.spec_index(ro.allocator_ptr_4k).quota.view().container_depth == ro.depth
                &&& allocator_2m_map.dom().contains(ro.allocator_ptr_2m)
                &&& allocator_2m_map.spec_index(ro.allocator_ptr_2m).owning_container == container_ptr
                &&& allocator_2m_map.spec_index(ro.allocator_ptr_2m).quota.view().container_depth == ro.depth
                &&& allocator_1g_map.dom().contains(ro.allocator_ptr_1g)
                &&& allocator_1g_map.spec_index(ro.allocator_ptr_1g).owning_container == container_ptr
                &&& allocator_1g_map.spec_index(ro.allocator_ptr_1g).quota.view().container_depth == ro.depth
            }),
    { reveal(container_allocator_wf); }

    pub open spec fn container_page_owner_forward_wf(container_map: ContainerLockedMap, page_array: PageLockedArray) -> bool {
        forall|c_ptr:RwLockContainerPtr, page_ptr: PagePtr|
            #![trigger container_map.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)
                ==> page_ptr_valid(page_ptr) && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr
    }

    pub open spec fn container_page_owner_backward_wf(container_map: ContainerLockedMap, page_array: PageLockedArray) -> bool {
        forall|p_i: PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().owning_container]
            index_valid(NUM_PAGES, p_i)
                ==> container_map.dom().contains(page_array.spec_index(p_i).view().view().owning_container)
                && container_map.spec_index(page_array.spec_index(p_i).view().view().owning_container).view().owned_pages.view().contains(page_index2page_ptr(p_i))
    }

    #[verifier::opaque]
    pub open spec fn container_page_owner_wf(container_map: ContainerLockedMap, page_array: PageLockedArray) -> bool {
        &&& container_page_owner_forward_wf(container_map, page_array)
        &&& container_page_owner_backward_wf(container_map, page_array)
    }

    pub proof fn container_page_owner_backward_at(container_map: ContainerLockedMap, page_array: PageLockedArray, page_index: PageIndex)
        requires
            container_page_owner_wf(container_map, page_array),
            index_valid(NUM_PAGES, page_index),
        ensures
            container_map.dom().contains(page_array.spec_index(page_index).view().view().owning_container),
            container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view().owned_pages.view().contains(page_index2page_ptr(page_index)),
    { reveal(container_page_owner_wf); }

    pub open spec fn container_allocator_global_free_4k_forward_wf(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray) -> bool {
        forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                let allocator_ptr_4k = page_array.spec_index(page_index).view().view().state->Free4k_allocator_ptr.view();
                &&& allocator_4k_map.dom().contains(allocator_ptr_4k)
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).owning_container == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool.view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool.view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool.view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
            }
    }

    pub open spec fn container_allocator_global_free_4k_backward_wf(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray) -> bool {
        forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            #![trigger allocator_4k_map.dom().contains(alloc_ptr), page_ptr2page_index(page_ptr)]
            allocator_4k_map.dom().contains(alloc_ptr) && allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
                ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::GlobalList }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_4k_map.spec_index(alloc_ptr).owning_container
    }

    // Proof dependencies (confirmed for global-pool page removal): allocator_perms_wf,
    // allocator_free_page_ptrs_wf. Entry facts are exposed through container_allocator_free_4k_page_wf.
    #[verifier::opaque]
    pub open spec fn container_allocator_global_free_4k_page_wf(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray) -> bool {
        &&& container_allocator_global_free_4k_forward_wf(allocator_4k_map, page_array)
        &&& container_allocator_global_free_4k_backward_wf(allocator_4k_map, page_array)
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_cpu_cache_free_4k_page_wf(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state->Free4k_allocator_ptr]
            #![trigger page_array.spec_index(page_index).view().view().state->Free4k_state->PreCpuCache_cpu_id]
            #![trigger page_array.spec_index(page_index).view().view().free_list_node_storage.addr()]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { cpu_id } }) ==> {
                let allocator_ptr_4k = page_array.spec_index(page_index).view().view().state->Free4k_allocator_ptr.view();
                let cpu_id = page_array.spec_index(page_index).view().view().state->Free4k_state->PreCpuCache_cpu_id;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allocator_4k_map.dom().contains(allocator_ptr_4k)
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).owning_container == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
            #![trigger page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state, allocator_4k_map.dom().contains(alloc_ptr), index_valid(NUM_CPUS, cpu_i)]
            allocator_4k_map.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) && allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
                ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i } }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_4k_map.spec_index(alloc_ptr).owning_container
    }

    // Proof dependencies (confirmed for nonfree-page preservation):
    // page_array_wf, allocator_free_page_ptrs_wf.
    #[verifier::opaque]
    pub open spec fn container_allocator_free_4k_page_wf(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray) -> bool {
        &&& container_allocator_global_free_4k_page_wf(allocator_4k_map, page_array)
        &&& container_allocator_cpu_cache_free_4k_page_wf(allocator_4k_map, page_array)
    }

    /// A free page `page_index` sits, under its free-list node address, in the global pool or CPU cache that its state names.
    pub proof fn container_allocator_free_4k_page_wf_at(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray, page_index: PageIndex)
        requires
            container_allocator_free_4k_page_wf(allocator_4k_map, page_array),
            index_valid(NUM_PAGES, page_index),
        ensures
            ({
                let page = page_array.spec_index(page_index).view().view();
                let allocator_ptr_4k = page.state->Free4k_allocator_ptr.view();
                (page.state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                    &&& allocator_4k_map.dom().contains(allocator_ptr_4k)
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).owning_container == page.owning_container
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool.view().view().contains(page_index2page_ptr(page_index))
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool.view().map().dom().contains(page.free_list_node_storage.addr())
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool.view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
                }
            }),
            ({
                let page = page_array.spec_index(page_index).view().view();
                let allocator_ptr_4k = page.state->Free4k_allocator_ptr.view();
                let cpu_id = page.state->Free4k_state->PreCpuCache_cpu_id;
                (page.state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { cpu_id } }) ==> {
                    &&& index_valid(NUM_CPUS, cpu_id)
                    &&& allocator_4k_map.dom().contains(allocator_ptr_4k)
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).owning_container == page.owning_container
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page.free_list_node_storage.addr())
                    &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
                }
            }),
    { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); }

    /// A page in allocator `alloc_ptr`'s global pool is free on that global list and shares the allocator's container.
    pub proof fn container_allocator_free_4k_page_wf_global_at(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr)
        requires
            container_allocator_free_4k_page_wf(allocator_4k_map, page_array),
            allocator_4k_map.dom().contains(alloc_ptr),
        ensures
            allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr) ==> {
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::GlobalList }
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_4k_map.spec_index(alloc_ptr).owning_container
            },
    { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); }

    /// A page in allocator `alloc_ptr`'s CPU `cpu_i` cache is free in that cache and shares the allocator's container.
    pub proof fn container_allocator_free_4k_page_wf_cache_at(allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, page_array: PageLockedArray, alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr)
        requires
            container_allocator_free_4k_page_wf(allocator_4k_map, page_array),
            allocator_4k_map.dom().contains(alloc_ptr),
            index_valid(NUM_CPUS, cpu_i),
        ensures
            allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr) ==> {
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i } }
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_4k_map.spec_index(alloc_ptr).owning_container
            },
    { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); }

    // Proof dependency (confirmed for cache-page removal): allocator_perms_wf.
    #[verifier::opaque]
    pub open spec fn container_allocator_global_free_2m_page_wf(allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, page_array: PageLockedArray) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                let allocator_ptr_2m = page_array.spec_index(page_index).view().view().state->Free2m_allocator_ptr.view();
                &&& allocator_2m_map.dom().contains(allocator_ptr_2m)
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).owning_container == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).global_pool.view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).global_pool.view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).global_pool.view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            allocator_2m_map.dom().contains(alloc_ptr) && allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
                ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free2m { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::GlobalList }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_2m_map.spec_index(alloc_ptr).owning_container
    }

    // Proof dependency (confirmed for CPU-cache pop): allocator_perms_wf.
    #[verifier::opaque]
    pub open spec fn container_allocator_cpu_cache_free_2m_page_wf(allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, page_array: PageLockedArray) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { cpu_id } }) ==> {
                let allocator_ptr_2m = page_array.spec_index(page_index).view().view().state->Free2m_allocator_ptr.view();
                let cpu_id = page_array.spec_index(page_index).view().view().state->Free2m_state->PreCpuCache_cpu_id;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allocator_2m_map.dom().contains(allocator_ptr_2m)
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).owning_container == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            allocator_2m_map.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) && allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
                ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free2m { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i } }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_2m_map.spec_index(alloc_ptr).owning_container
    }

    // Proof dependencies (confirmed for nonfree-page preservation):
    // page_array_wf, allocator_free_page_ptrs_wf.
    #[verifier::opaque]
    pub open spec fn container_allocator_free_2m_page_wf(allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, page_array: PageLockedArray) -> bool {
        &&& container_allocator_global_free_2m_page_wf(allocator_2m_map, page_array)
        &&& container_allocator_cpu_cache_free_2m_page_wf(allocator_2m_map, page_array)
    }

    /// A free 2m page `page_index` sits, under its free-list node address, in the global pool or CPU cache that its state names.
    pub proof fn container_allocator_free_2m_page_wf_at(allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, page_array: PageLockedArray, page_index: PageIndex)
        requires
            container_allocator_free_2m_page_wf(allocator_2m_map, page_array),
            index_valid(NUM_PAGES, page_index),
        ensures
            ({
                let page = page_array.spec_index(page_index).view().view();
                let allocator_ptr_2m = page.state->Free2m_allocator_ptr.view();
                (page.state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                    &&& allocator_2m_map.dom().contains(allocator_ptr_2m)
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).owning_container == page.owning_container
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).global_pool.view().view().contains(page_index2page_ptr(page_index))
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).global_pool.view().map().dom().contains(page.free_list_node_storage.addr())
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).global_pool.view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
                }
            }),
            ({
                let page = page_array.spec_index(page_index).view().view();
                let allocator_ptr_2m = page.state->Free2m_allocator_ptr.view();
                let cpu_id = page.state->Free2m_state->PreCpuCache_cpu_id;
                (page.state matches PageState::Free2m { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { cpu_id } }) ==> {
                    &&& index_valid(NUM_CPUS, cpu_id)
                    &&& allocator_2m_map.dom().contains(allocator_ptr_2m)
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).owning_container == page.owning_container
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page.free_list_node_storage.addr())
                    &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
                }
            }),
    { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); }

    /// A page in allocator `alloc_ptr`'s 2m global pool is free on that global list and shares the allocator's container.
    pub proof fn container_allocator_free_2m_page_wf_global_at(allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, page_array: PageLockedArray, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr)
        requires
            container_allocator_free_2m_page_wf(allocator_2m_map, page_array),
            allocator_2m_map.dom().contains(alloc_ptr),
        ensures
            allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr) ==> {
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free2m { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::GlobalList }
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_2m_map.spec_index(alloc_ptr).owning_container
            },
    { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); }

    /// A page in allocator `alloc_ptr`'s 2m CPU `cpu_i` cache is free in that cache and shares the allocator's container.
    pub proof fn container_allocator_free_2m_page_wf_cache_at(allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, page_array: PageLockedArray, alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr)
        requires
            container_allocator_free_2m_page_wf(allocator_2m_map, page_array),
            allocator_2m_map.dom().contains(alloc_ptr),
            index_valid(NUM_CPUS, cpu_i),
        ensures
            allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr) ==> {
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free2m { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i } }
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_2m_map.spec_index(alloc_ptr).owning_container
            },
    { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); }

    #[verifier::opaque]
    pub open spec fn container_allocator_global_free_1g_page_wf(allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, page_array: PageLockedArray) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Free1g { allocator_ptr: _, state: FreePageAllocatorState::GlobalList }) ==> {
                let allocator_ptr_1g = page_array.spec_index(page_index).view().view().state->Free1g_allocator_ptr.view();
                &&& allocator_1g_map.dom().contains(allocator_ptr_1g)
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).owning_container == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).global_pool.view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).global_pool.view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).global_pool.view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            allocator_1g_map.dom().contains(alloc_ptr) && allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
                ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free1g { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::GlobalList }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_1g_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_cpu_cache_free_1g_page_wf(allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, page_array: PageLockedArray) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Free1g { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { cpu_id } }) ==> {
                let allocator_ptr_1g = page_array.spec_index(page_index).view().view().state->Free1g_allocator_ptr.view();
                let cpu_id = page_array.spec_index(page_index).view().view().state->Free1g_state->PreCpuCache_cpu_id;
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allocator_1g_map.dom().contains(allocator_ptr_1g)
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).owning_container == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            allocator_1g_map.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) && allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
                ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free1g { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i } }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_1g_map.spec_index(alloc_ptr).owning_container
    }

    // Proof dependencies (confirmed for nonfree-page preservation):
    // page_array_wf, allocator_free_page_ptrs_wf.
    #[verifier::opaque]
    pub open spec fn container_allocator_free_1g_page_wf(allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, page_array: PageLockedArray) -> bool {
        &&& container_allocator_global_free_1g_page_wf(allocator_1g_map, page_array)
        &&& container_allocator_cpu_cache_free_1g_page_wf(allocator_1g_map, page_array)
    }

    /// A page in allocator `alloc_ptr`'s 1G global pool is free in that pool and shares the allocator's container.
    pub proof fn container_allocator_free_1g_page_wf_global_at(allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, page_array: PageLockedArray, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr)
        requires
            container_allocator_free_1g_page_wf(allocator_1g_map, page_array),
            allocator_1g_map.dom().contains(alloc_ptr),
        ensures
            allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr) ==> {
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free1g { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::GlobalList }
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_1g_map.spec_index(alloc_ptr).owning_container
            },
    { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); }

    /// A page in allocator `alloc_ptr`'s CPU `cpu_i` 1G cache is free in that cache and shares the allocator's container.
    pub proof fn container_allocator_free_1g_page_wf_cache_at(allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, page_array: PageLockedArray, alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr)
        requires
            container_allocator_free_1g_page_wf(allocator_1g_map, page_array),
            allocator_1g_map.dom().contains(alloc_ptr),
            index_valid(NUM_CPUS, cpu_i),
        ensures
            allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr) ==> {
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free1g { allocator_ptr: Ghost(alloc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i } }
                &&& page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_1g_map.spec_index(alloc_ptr).owning_container
            },
    { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); }
}

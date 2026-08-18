use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub open spec fn allocator_pages_wf(
            page_array: PageLockedArray, 
                    allocator_4k_map: PageAllocatorUnLockedMap, 
                    allocator_2m_map: PageAllocatorUnLockedMap, 
                    allocator_1g_map: PageAllocatorUnLockedMap) -> bool {
            &&&
            allocator_4k_pages_wf(page_array, allocator_4k_map)
            &&&
            allocator_2m_pages_wf(page_array, allocator_2m_map)
            &&&
            allocator_1g_pages_wf(page_array, allocator_1g_map)
        }

        #[verifier::opaque]
        pub open spec fn allocator_4k_pages_wf(
            page_array: PageLockedArray, 
            allocator_4k_map: PageAllocatorUnLockedMap
        ) -> bool{
            &&&
            forall|page_index:PageIndex|
                #![trigger page_array.spec_index(page_index)]
                #![trigger allocator_4k_map.dom().contains(page_index2page_ptr(page_index))]
                index_valid(NUM_PAGES, page_index)
                &&
                (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator})
                ==>
                allocator_4k_map.dom().contains(page_index2page_ptr(page_index))
            &&&
            forall|a_ptr:RwLockPageAllocatorPtr|
                #![trigger page_array.spec_index(page_ptr2page_index(a_ptr))]
                #![trigger allocator_4k_map.dom().contains(a_ptr)]
                allocator_4k_map.dom().contains(a_ptr)
                ==>
                page_ptr_valid(a_ptr)
                &&
                page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As4KAllocator}
        }

    #[verifier::opaque]
    pub open spec fn allocator_2m_pages_wf(
        page_array: PageLockedArray, 
        allocator_2m_map: PageAllocatorUnLockedMap
    ) -> bool{
        &&&
        forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index)]
        #![trigger allocator_2m_map.dom().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index)
        &&
        (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator})
        ==>
        allocator_2m_map.dom().contains(page_index2page_ptr(page_index))

        &&&
        forall|a_ptr:RwLockPageAllocatorPtr|
        #![trigger page_array.spec_index(page_ptr2page_index(a_ptr))]
        #![trigger allocator_2m_map.dom().contains(a_ptr)]
        allocator_2m_map.dom().contains(a_ptr)
        ==>
        page_ptr_valid(a_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As2MAllocator}

    }

    #[verifier::opaque]
    pub open spec fn allocator_1g_pages_wf(page_array: PageLockedArray, 
            allocator_1g_map: PageAllocatorUnLockedMap
            ) -> bool{
        &&&
        forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index)]
        #![trigger allocator_1g_map.dom().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index)
        &&
        (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator})
        ==>
        allocator_1g_map.dom().contains(page_index2page_ptr(page_index))

        &&&
        forall|a_ptr:RwLockPageAllocatorPtr|
        #![trigger page_array.spec_index(page_ptr2page_index(a_ptr))]
        #![trigger allocator_1g_map.dom().contains(a_ptr)]
        allocator_1g_map.dom().contains(a_ptr)
        ==>
        page_ptr_valid(a_ptr)
        &&
        page_array.spec_index(page_ptr2page_index(a_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::As1GAllocator}

    }

    #[verifier::opaque]
    pub open spec fn container_allocator_wf(container_map: ContainerLockedMap, 
            allocator_4k_map: PageAllocatorUnLockedMap, 
            allocator_2m_map: PageAllocatorUnLockedMap, 
            allocator_1g_map: PageAllocatorUnLockedMap
        ) -> bool {
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr,|
            #![trigger allocator_4k_map.spec_index(alloc_ptr).owning_container]
            allocator_4k_map.dom().contains(alloc_ptr) 
            ==>
            container_map.dom().contains(allocator_4k_map.spec_index(alloc_ptr).owning_container)
            &&
            container_map.spec_index(allocator_4k_map.spec_index(alloc_ptr).owning_container).view_rodata().view().allocator_ptr_4k == alloc_ptr
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
            container_map.dom().contains(c_ptr)
            ==>
            allocator_4k_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k)
            &&
            allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).owning_container == c_ptr
            &&
            allocator_4k_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr,|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).owning_container]
            allocator_2m_map.dom().contains(alloc_ptr) 
            ==>
            container_map.dom().contains(allocator_2m_map.spec_index(alloc_ptr).owning_container)
            &&
            container_map.spec_index(allocator_2m_map.spec_index(alloc_ptr).owning_container).view_rodata().view().allocator_ptr_2m == alloc_ptr
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
            container_map.dom().contains(c_ptr)
            ==>
            allocator_2m_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m)
            &&
            allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).owning_container == c_ptr
            &&
            allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr,|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).owning_container]
            allocator_1g_map.dom().contains(alloc_ptr) 
            ==>
            container_map.dom().contains(allocator_1g_map.spec_index(alloc_ptr).owning_container)
            &&
            container_map.spec_index(allocator_1g_map.spec_index(alloc_ptr).owning_container).view_rodata().view().allocator_ptr_1g == alloc_ptr
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
            container_map.dom().contains(c_ptr)
            ==>
            allocator_1g_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g)
            &&
            allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).owning_container == c_ptr
            &&
            allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
    }

    #[verifier::opaque]
    pub open spec fn container_page_owner_wf(container_map: ContainerLockedMap, 
            page_array: PageLockedArray
        ) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr, page_ptr: PagePtr|
            #![trigger container_map.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)
            ==>
            page_ptr_valid(page_ptr)
            &&
            page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr
        &&&
        forall|p_i: PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().owning_container]
            index_valid(NUM_PAGES, p_i)
            ==>
            container_map.dom().contains(page_array.spec_index(p_i).view().view().owning_container)
            &&
            container_map.spec_index(page_array.spec_index(p_i).view().view().owning_container).view().owned_pages.view().contains(page_index2page_ptr(p_i))
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_global_free_4k_page_wf(
        allocator_4k_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index)
            && (page_array.spec_index(page_index).view().view().state matches
                PageState::Free4k {
                    allocator_ptr: _,
                    state: FreePageAllocatorState::GlobalList,
                })
            ==> {
                let allocator_ptr_4k = page_array.spec_index(page_index).view()
                    .view().state->Free4k_allocator_ptr.view();

                &&& allocator_4k_map.dom().contains(allocator_ptr_4k)
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).owning_container
                    == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool
                    .view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool
                    .view().map().dom().contains(page_array.spec_index(page_index)
                        .view().view().free_list_node_storage.addr())
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).global_pool
                    .view().map().spec_index(page_array.spec_index(page_index)
                        .view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            #![trigger allocator_4k_map.spec_index(alloc_ptr).global_pool, page_ptr2page_index(page_ptr)]
            allocator_4k_map.dom().contains(alloc_ptr)
            && allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view()
                .contains(page_ptr)
            ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Free4k {
                        allocator_ptr: Ghost(alloc_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .owning_container
                    == allocator_4k_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_cpu_cache_free_4k_page_wf(
        allocator_4k_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state->Free4k_allocator_ptr]
            #![trigger page_array.spec_index(page_index).view().view().state->Free4k_state->PreCpuCache_cpu_id]
            #![trigger page_array.spec_index(page_index).view().view().free_list_node_storage.addr()]
            index_valid(NUM_PAGES, page_index)
            && (page_array.spec_index(page_index).view().view().state matches
                PageState::Free4k {
                    allocator_ptr: _,
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                })
            ==> {
                let allocator_ptr_4k = page_array.spec_index(page_index).view()
                    .view().state->Free4k_allocator_ptr.view();
                let cpu_id = page_array.spec_index(page_index).view().view().state
                    ->Free4k_state->PreCpuCache_cpu_id;

                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allocator_4k_map.dom().contains(allocator_ptr_4k)
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).owning_container
                    == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches
                    .spec_index(cpu_id).view().view().view()
                    .contains(page_index2page_ptr(page_index))
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches
                    .spec_index(cpu_id).view().view().map().dom().contains(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                &&& allocator_4k_map.spec_index(allocator_ptr_4k).cpu_caches
                    .spec_index(cpu_id).view().view().map().spec_index(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
            // #![trigger
            //     allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i),
            //     page_ptr2page_index(page_ptr)]
            #![trigger
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
                allocator_4k_map.spec_index(alloc_ptr),
                index_valid(NUM_CPUS, cpu_i)
                ]
            allocator_4k_map.dom().contains(alloc_ptr)
            && index_valid(NUM_CPUS, cpu_i)
            && allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i)
                .view().view().view().contains(page_ptr)
            ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Free4k {
                        allocator_ptr: Ghost(alloc_ptr),
                        state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i },
                    }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .owning_container
                    == allocator_4k_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_free_4k_page_wf(
        allocator_4k_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& container_allocator_global_free_4k_page_wf(
            allocator_4k_map, page_array)
        &&& container_allocator_cpu_cache_free_4k_page_wf(
            allocator_4k_map, page_array)
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_global_free_2m_page_wf(
        allocator_2m_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index)
            && (page_array.spec_index(page_index).view().view().state matches
                PageState::Free2m {
                    allocator_ptr: _,
                    state: FreePageAllocatorState::GlobalList,
                })
            ==> {
                let allocator_ptr_2m = page_array.spec_index(page_index).view()
                    .view().state->Free2m_allocator_ptr.view();

                &&& allocator_2m_map.dom().contains(allocator_ptr_2m)
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).owning_container
                    == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_2m_map.spec_index(allocator_ptr_2m)
                    .global_pool.view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_2m_map.spec_index(allocator_ptr_2m)
                    .global_pool.view().map().dom().contains(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                &&& allocator_2m_map.spec_index(allocator_ptr_2m)
                    .global_pool.view().map().spec_index(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            allocator_2m_map.dom().contains(alloc_ptr)
            && allocator_2m_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
            ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Free2m {
                        allocator_ptr: Ghost(alloc_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                    == allocator_2m_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_cpu_cache_free_2m_page_wf(
        allocator_2m_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index)
            && (page_array.spec_index(page_index).view().view().state matches
                PageState::Free2m {
                    allocator_ptr: _,
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                })
            ==> {
                let allocator_ptr_2m = page_array.spec_index(page_index).view()
                    .view().state->Free2m_allocator_ptr.view();
                let cpu_id = page_array.spec_index(page_index).view().view().state
                    ->Free2m_state->PreCpuCache_cpu_id;

                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allocator_2m_map.dom().contains(allocator_ptr_2m)
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).owning_container
                    == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches
                    .spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches
                    .spec_index(cpu_id).view().view().map().dom().contains(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                &&& allocator_2m_map.spec_index(allocator_ptr_2m).cpu_caches
                    .spec_index(cpu_id).view().view().map().spec_index(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            allocator_2m_map.dom().contains(alloc_ptr)
            && index_valid(NUM_CPUS, cpu_i)
            && allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i)
                .view().view().view().contains(page_ptr)
            ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Free2m {
                        allocator_ptr: Ghost(alloc_ptr),
                        state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i },
                    }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                    == allocator_2m_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_free_2m_page_wf(
        allocator_2m_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& container_allocator_global_free_2m_page_wf(
            allocator_2m_map, page_array)
        &&& container_allocator_cpu_cache_free_2m_page_wf(
            allocator_2m_map, page_array)
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_global_free_1g_page_wf(
        allocator_1g_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index)
            && (page_array.spec_index(page_index).view().view().state matches
                PageState::Free1g {
                    allocator_ptr: _,
                    state: FreePageAllocatorState::GlobalList,
                })
            ==> {
                let allocator_ptr_1g = page_array.spec_index(page_index).view()
                    .view().state->Free1g_allocator_ptr.view();

                &&& allocator_1g_map.dom().contains(allocator_ptr_1g)
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).owning_container
                    == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_1g_map.spec_index(allocator_ptr_1g)
                    .global_pool.view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_1g_map.spec_index(allocator_ptr_1g)
                    .global_pool.view().map().dom().contains(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                &&& allocator_1g_map.spec_index(allocator_ptr_1g)
                    .global_pool.view().map().spec_index(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
            allocator_1g_map.dom().contains(alloc_ptr)
            && allocator_1g_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
            ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Free1g {
                        allocator_ptr: Ghost(alloc_ptr),
                        state: FreePageAllocatorState::GlobalList,
                    }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                    == allocator_1g_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_cpu_cache_free_1g_page_wf(
        allocator_1g_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& forall|page_index: PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            index_valid(NUM_PAGES, page_index)
            && (page_array.spec_index(page_index).view().view().state matches
                PageState::Free1g {
                    allocator_ptr: _,
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                })
            ==> {
                let allocator_ptr_1g = page_array.spec_index(page_index).view()
                    .view().state->Free1g_allocator_ptr.view();
                let cpu_id = page_array.spec_index(page_index).view().view().state
                    ->Free1g_state->PreCpuCache_cpu_id;

                &&& index_valid(NUM_CPUS, cpu_id)
                &&& allocator_1g_map.dom().contains(allocator_ptr_1g)
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).owning_container
                    == page_array.spec_index(page_index).view().view().owning_container
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).cpu_caches
                    .spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).cpu_caches
                    .spec_index(cpu_id).view().view().map().dom().contains(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                &&& allocator_1g_map.spec_index(allocator_ptr_1g).cpu_caches
                    .spec_index(cpu_id).view().view().map().spec_index(
                        page_array.spec_index(page_index).view().view()
                            .free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
            }
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            allocator_1g_map.dom().contains(alloc_ptr)
            && index_valid(NUM_CPUS, cpu_i)
            && allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i)
                .view().view().view().contains(page_ptr)
            ==> page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Free1g {
                        allocator_ptr: Ghost(alloc_ptr),
                        state: FreePageAllocatorState::PreCpuCache { cpu_id: cpu_i },
                    }
                && page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                    == allocator_1g_map.spec_index(alloc_ptr).owning_container
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_free_1g_page_wf(
        allocator_1g_map: PageAllocatorUnLockedMap,
        page_array: PageLockedArray,
    ) -> bool {
        &&& container_allocator_global_free_1g_page_wf(
            allocator_1g_map, page_array)
        &&& container_allocator_cpu_cache_free_1g_page_wf(
            allocator_1g_map, page_array)
    }
}

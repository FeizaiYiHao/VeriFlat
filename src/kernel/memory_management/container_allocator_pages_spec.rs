use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub open spec fn allocator_pages_wf(
            page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>, 
                    allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>, 
                    allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>, 
                    allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>) -> bool {
            &&&
            allocator_4k_pages_wf(page_array, allocator_4k_map)
            &&&
            allocator_2m_pages_wf(page_array, allocator_2m_map)
            &&&
            allocator_1g_pages_wf(page_array, allocator_1g_map)
        }

        #[verifier::opaque]
        pub open spec fn allocator_4k_pages_wf(
            page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>, 
            allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
        ) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger allocator_4k_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
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
        page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>, 
        allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
    ) -> bool{
        &&&
        forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index)]
        #![trigger allocator_2m_map.dom().contains(page_index2page_ptr(page_index))]
        page_index_wf(page_index)
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
    pub open spec fn allocator_1g_pages_wf(page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>, 
            allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
            ) -> bool{
        &&&
        forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index)]
        #![trigger allocator_1g_map.dom().contains(page_index2page_ptr(page_index))]
        page_index_wf(page_index)
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
    pub open spec fn container_allocator_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, 
            allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>, 
            allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>, 
            allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>
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
    pub open spec fn container_page_owner_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, 
            page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>
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
            page_index_valid(p_i)
            ==>
            container_map.dom().contains(page_array.spec_index(p_i).view().view().owning_container)
            &&
            container_map.spec_index(page_array.spec_index(p_i).view().view().owning_container).view().owned_pages.view().contains(page_index2page_ptr(p_i))
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_free_4k_page_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,
            allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
            page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>
        ) -> bool
        // This predicate dereferences a page's owning_container into
        // `container_map` and that container's `allocator_ptr_4k` into
        // `allocator_4k_map`; it is only meaningful when those lookups land in
        // their maps. `container_page_owner_wf` gives owner ∈ container_map.dom();
        // `page_array_wf` gives each Free4k{PreCpuCache} page a valid cpu_id.
        // (The companion `container_allocator_wf`, which gives
        // c.allocator_ptr_4k ∈ allocator_4k_map.dom(), also belongs here but
        // can't be named — it requires the 2m/1g allocator maps that aren't
        // parameters of this predicate.)
        recommends
            container_page_owner_wf(container_map, page_array),
            page_array_wf(page_array),
    {
        &&&
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            page_index_wf(page_index)
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList }
                ==>
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .global_poll.view().view().contains(page_index2page_ptr(page_index))
                &&
                // The node stored at the page's free_list_node_storage address
                // holds this page's pointer as its value. (Key = node address,
                // value = page pointer — was swapped.) The key is live in the
                // map (dom membership), so the value-equality is meaningful.
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .global_poll.view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .global_poll.view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                &&
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .owning_container == page_array.spec_index(page_index).view().view().owning_container
            }
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
                ==>
                allocator_4k_map.dom().contains(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                &&
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                &&
                allocator_4k_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k)
                    .owning_container == page_array.spec_index(page_index).view().view().owning_container
            }
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_4k_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
            {
                allocator_4k_map.dom().contains(alloc_ptr) && allocator_4k_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
                ==>
                (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList })
                &&
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_4k_map.spec_index(alloc_ptr).owning_container
            }
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
            #![trigger allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            {
                // A page in a cpu cache is `Free4k{PreCpuCache}`. (The antecedent
                // is membership in the cache only — a page is in exactly one place,
                // never both a cache and the global pool, so the old
                // `global_poll.contains(page_ptr) &&` conjunct made this clause
                // vacuous. Guards mirror the global-poll-reverse clause above.)
                allocator_4k_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i) &&
                    allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
                ==>
                (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id: _cpu_id }})
                &&
                // The recorded cpu_id must equal the cache index cpu_i: a page in
                // cache[cpu_i] records PreCpuCache{cpu_i}. A `matches` pattern only
                // BINDS a fresh var (its binding doesn't even scope across `&&`),
                // so the equality is a separate conjunct using the field accessors
                // — without it a page in cache[5] could record PreCpuCache{3} and,
                // via the forward clause, sit in two caches at once.
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Free4k_state->PreCpuCache_cpu_id == cpu_i
                &&
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_4k_map.spec_index(alloc_ptr).owning_container
            }
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_free_2m_page_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,
            allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
            page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>
        ) -> bool
        // See `container_allocator_free_4k_page_wf` recommends note.
        recommends
            container_page_owner_wf(container_map, page_array),
            page_array_wf(page_array),
    {
        &&&
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            page_index_wf(page_index)
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::GlobalList }
                ==>
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .global_poll.view().view().contains(page_index2page_ptr(page_index))
                &&
                // Key = node address, value = page pointer (was swapped); key live.
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .global_poll.view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .global_poll.view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                &&
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .owning_container == page_array.spec_index(page_index).view().view().owning_container
            }
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
                ==>
                allocator_2m_map.dom().contains(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                &&
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                &&
                allocator_2m_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_2m)
                    .owning_container == page_array.spec_index(page_index).view().view().owning_container
            }
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
            {
                allocator_2m_map.dom().contains(alloc_ptr) && allocator_2m_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
                ==>
                (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::GlobalList })
                &&
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_2m_map.spec_index(alloc_ptr).owning_container
            }
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
            #![trigger allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            {
                // See 4k clause: cache membership only; no spurious global_poll conjunct.
                allocator_2m_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i) &&
                    allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
                ==>
                (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free2m { state: FreePageAllocatorState::PreCpuCache { cpu_id: _cpu_id }})
                &&
                // Recorded cpu_id == cache index cpu_i (see 4k clause).
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Free2m_state->PreCpuCache_cpu_id == cpu_i
                &&
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_2m_map.spec_index(alloc_ptr).owning_container
            }
    }

    #[verifier::opaque]
    pub open spec fn container_allocator_free_1g_page_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,
            allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
            page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>
        ) -> bool
        // See `container_allocator_free_4k_page_wf` recommends note.
        recommends
            container_page_owner_wf(container_map, page_array),
            page_array_wf(page_array),
    {
        &&&
        forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index).view().view().state]
            page_index_wf(page_index)
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::GlobalList }
                ==>
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .global_poll.view().view().contains(page_index2page_ptr(page_index))
                &&
                // Key = node address, value = page pointer (was swapped); key live.
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .global_poll.view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .global_poll.view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                &&
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .owning_container == page_array.spec_index(page_index).view().view().owning_container
            }
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
                ==>
                allocator_1g_map.dom().contains(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                &&
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                &&
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                &&
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .cpu_caches.spec_index(cpu_id).view().view().map().spec_index(page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                &&
                allocator_1g_map.spec_index(container_map.spec_index(page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_1g)
                    .owning_container == page_array.spec_index(page_index).view().view().owning_container
            }
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, page_ptr: PagePtr|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)]
            {
                allocator_1g_map.dom().contains(alloc_ptr) && allocator_1g_map.spec_index(alloc_ptr).global_poll.view().view().contains(page_ptr)
                ==>
                (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::GlobalList })
                &&
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_1g_map.spec_index(alloc_ptr).owning_container
            }
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i:CpuId, page_ptr: PagePtr|
            #![trigger allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
            {
                // See 4k clause: cache membership only; no spurious global_poll conjunct.
                allocator_1g_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i) &&
                    allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
                ==>
                (page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free1g { state: FreePageAllocatorState::PreCpuCache { cpu_id: _cpu_id }})
                &&
                // Recorded cpu_id == cache index cpu_i (see 4k clause).
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state->Free1g_state->PreCpuCache_cpu_id == cpu_i
                &&
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == allocator_1g_map.spec_index(alloc_ptr).owning_container
            }
    }
}

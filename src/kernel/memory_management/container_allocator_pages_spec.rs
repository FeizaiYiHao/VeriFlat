use vstd::prelude::*;
use crate::*;

verus! {
/// Each 4K allocator names an existing container that names it back.
pub open spec fn container_allocator_4k_forward_wf(ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
    forall|a: RwLockPageAllocatorPtr|
        #![trigger allc_4k_mp.spec_index(a).owning_container]
        allc_4k_mp.dom().contains(a)
            ==>
            ctn_mp.dom().contains(allc_4k_mp.spec_index(a).owning_container)
            && ctn_mp.spec_index(allc_4k_mp.spec_index(a).owning_container).view_rodata().view().allocator_ptr_4k == a
}

/// Each container's 4K allocator exists, names the container, and carries its depth.
pub open spec fn container_allocator_4k_backward_wf(ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k]
        ctn_mp.dom().contains(c) ==> {
            let ro = ctn_mp.spec_index(c).view_rodata().view();
            &&& allc_4k_mp.dom().contains(ro.allocator_ptr_4k)
            &&& allc_4k_mp.spec_index(ro.allocator_ptr_4k).owning_container == c
            &&& allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().container_depth == ro.depth
        }
}

/// Each 2M allocator names an existing container that names it back.
pub open spec fn container_allocator_2m_forward_wf(ctn_mp: ContainerLockedMap, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
    forall|a: RwLockPageAllocatorPtr|
        #![trigger allc_2m_mp.spec_index(a).owning_container]
        allc_2m_mp.dom().contains(a)
            ==>
            ctn_mp.dom().contains(allc_2m_mp.spec_index(a).owning_container)
            && ctn_mp.spec_index(allc_2m_mp.spec_index(a).owning_container).view_rodata().view().allocator_ptr_2m == a
}

/// Each container's 2M allocator exists, names the container, and carries its depth.
pub open spec fn container_allocator_2m_backward_wf(ctn_mp: ContainerLockedMap, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m]
        ctn_mp.dom().contains(c) ==> {
            let ro = ctn_mp.spec_index(c).view_rodata().view();
            &&& allc_2m_mp.dom().contains(ro.allocator_ptr_2m)
            &&& allc_2m_mp.spec_index(ro.allocator_ptr_2m).owning_container == c
            &&& allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().container_depth == ro.depth
        }
}

/// Each 1G allocator names an existing container that names it back.
pub open spec fn container_allocator_1g_forward_wf(ctn_mp: ContainerLockedMap, allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
    forall|a: RwLockPageAllocatorPtr|
        #![trigger allc_1g_mp.spec_index(a).owning_container]
        allc_1g_mp.dom().contains(a)
            ==>
            ctn_mp.dom().contains(allc_1g_mp.spec_index(a).owning_container)
            && ctn_mp.spec_index(allc_1g_mp.spec_index(a).owning_container).view_rodata().view().allocator_ptr_1g == a
}

/// Each container's 1G allocator exists, names the container, and carries its depth.
pub open spec fn container_allocator_1g_backward_wf(ctn_mp: ContainerLockedMap, allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g]
        ctn_mp.dom().contains(c) ==> {
            let ro = ctn_mp.spec_index(c).view_rodata().view();
            &&& allc_1g_mp.dom().contains(ro.allocator_ptr_1g)
            &&& allc_1g_mp.spec_index(ro.allocator_ptr_1g).owning_container == c
            &&& allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().container_depth == ro.depth
        }
}

/// Containers and their 4K, 2M, and 1G allocators name each other.
#[verifier::opaque]
pub open spec fn container_allocator_wf(
    ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>,
) -> bool {
    &&& container_allocator_4k_forward_wf(ctn_mp, allc_4k_mp)
    &&& container_allocator_4k_backward_wf(ctn_mp, allc_4k_mp)
    &&& container_allocator_2m_forward_wf(ctn_mp, allc_2m_mp)
    &&& container_allocator_2m_backward_wf(ctn_mp, allc_2m_mp)
    &&& container_allocator_1g_forward_wf(ctn_mp, allc_1g_mp)
    &&& container_allocator_1g_backward_wf(ctn_mp, allc_1g_mp)
}

/// Container `ctn_ptr`'s 4K, 2M, and 1G allocators exist, belong to it, and carry its depth.
pub proof fn container_allocator_wf_at(
    ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, ctn_ptr: RwLockContainerPtr,
)
    requires
        container_allocator_wf(ctn_mp, allc_4k_mp, allc_2m_mp, allc_1g_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ({
            let ro = ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            &&& allc_4k_mp.dom().contains(ro.allocator_ptr_4k)
            &&& allc_4k_mp.spec_index(ro.allocator_ptr_4k).owning_container == ctn_ptr
            &&& allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().container_depth == ro.depth
            &&& allc_2m_mp.dom().contains(ro.allocator_ptr_2m)
            &&& allc_2m_mp.spec_index(ro.allocator_ptr_2m).owning_container == ctn_ptr
            &&& allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().container_depth == ro.depth
            &&& allc_1g_mp.dom().contains(ro.allocator_ptr_1g)
            &&& allc_1g_mp.spec_index(ro.allocator_ptr_1g).owning_container == ctn_ptr
            &&& allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().container_depth == ro.depth
        }),
{ reveal(container_allocator_wf); }

/// Every page a container lists in its owned pages is a valid page owned by that container.
pub open spec fn container_owned_pages_forward_wf(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|c: RwLockContainerPtr, pg_ptr: PagePtr|
        #![trigger ctn_mp.spec_index(c).view().owned_pages.view().contains(pg_ptr)]
        ctn_mp.dom().contains(c)
            && ctn_mp.spec_index(c).view().owned_pages.view().contains(pg_ptr)
            ==>
            page_ptr_valid(pg_ptr)
            && pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == c
}

/// Every page's owning container exists and lists the page in its owned pages.
pub open spec fn container_owned_pages_backward_wf(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().owning_container]
        index_valid(NUM_PAGES, p_i)
            ==>
            ctn_mp.dom().contains(pg_arr.spec_index(p_i).view().view().owning_container)
            && ctn_mp.spec_index(pg_arr.spec_index(p_i).view().view().owning_container).view().owned_pages.view().contains(page_index2page_ptr(p_i))
}

/// Containers' owned pages and pages' owning containers agree in both directions.
#[verifier::opaque]
pub open spec fn container_owned_pages_wf(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& container_owned_pages_forward_wf(ctn_mp, pg_arr)
    &&& container_owned_pages_backward_wf(ctn_mp, pg_arr)
}

pub proof fn container_owned_pages_wf_backward_at(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        container_owned_pages_wf(ctn_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        ctn_mp.dom().contains(pg_arr.spec_index(pg_idx).view().view().owning_container),
        ctn_mp.spec_index(pg_arr.spec_index(pg_idx).view().view().owning_container).view().owned_pages.view().contains(page_index2page_ptr(pg_idx)),
{ reveal(container_owned_pages_wf); }
}

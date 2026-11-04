use vstd::prelude::*;
use crate::*;

verus! {
/// Every 4K, 2M, and 1G allocator sits on a page in the matching allocator state, and every such page holds one.
pub open spec fn allocator_pages_wf(
    allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray,
) -> bool {
    &&& allocator_4k_pages_wf(allc_4k_mp, pg_arr)
    &&& allocator_2m_pages_wf(allc_2m_mp, pg_arr)
    &&& allocator_1g_pages_wf(allc_1g_mp, pg_arr)
}

/// A page in state As4KAllocator holds a 4K allocator.
pub open spec fn allocator_4k_pages_forward_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        #![trigger allc_4k_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
            ==>
            allc_4k_mp.dom().contains(page_index2page_ptr(p_i))
}

/// Every 4K allocator sits on a valid page in state As4KAllocator.
pub open spec fn allocator_4k_pages_backward_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    forall|a: RwLockPageAllocatorPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(a))]
        #![trigger allc_4k_mp.dom().contains(a)]
        allc_4k_mp.dom().contains(a)
            ==>
            page_ptr_valid(a)
            && (pg_arr.spec_index(page_ptr2page_index(a)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
}

/// 4K allocators and As4KAllocator pages agree in both directions.
#[verifier::opaque]
pub open spec fn allocator_4k_pages_wf(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_4k_pages_forward_wf(allc_4k_mp, pg_arr)
    &&& allocator_4k_pages_backward_wf(allc_4k_mp, pg_arr)
}

pub proof fn allocator_4k_pages_wf_at(allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr)
    requires allocator_4k_pages_wf(allc_4k_mp, pg_arr)
    ensures
        allc_4k_mp.dom().contains(allc_ptr)
            ==> page_ptr_valid(allc_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(allc_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }),
{ reveal(allocator_4k_pages_wf); }

/// A page in state As2MAllocator holds a 2M allocator.
pub open spec fn allocator_2m_pages_forward_wf(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        #![trigger allc_2m_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
            ==>
            allc_2m_mp.dom().contains(page_index2page_ptr(p_i))
}

/// Every 2M allocator sits on a valid page in state As2MAllocator.
pub open spec fn allocator_2m_pages_backward_wf(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray) -> bool {
    forall|a: RwLockPageAllocatorPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(a))]
        #![trigger allc_2m_mp.dom().contains(a)]
        allc_2m_mp.dom().contains(a)
            ==>
            page_ptr_valid(a)
            && (pg_arr.spec_index(page_ptr2page_index(a)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
}

/// 2M allocators and As2MAllocator pages agree in both directions.
#[verifier::opaque]
pub open spec fn allocator_2m_pages_wf(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_2m_pages_forward_wf(allc_2m_mp, pg_arr)
    &&& allocator_2m_pages_backward_wf(allc_2m_mp, pg_arr)
}

pub proof fn allocator_2m_pages_wf_at(allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr)
    requires allocator_2m_pages_wf(allc_2m_mp, pg_arr)
    ensures
        allc_2m_mp.dom().contains(allc_ptr)
            ==> page_ptr_valid(allc_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(allc_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }),
{ reveal(allocator_2m_pages_wf); }

/// A page in state As1GAllocator holds a 1G allocator.
pub open spec fn allocator_1g_pages_forward_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        #![trigger allc_1g_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
            ==>
            allc_1g_mp.dom().contains(page_index2page_ptr(p_i))
}

/// Every 1G allocator sits on a valid page in state As1GAllocator.
pub open spec fn allocator_1g_pages_backward_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray) -> bool {
    forall|a: RwLockPageAllocatorPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(a))]
        #![trigger allc_1g_mp.dom().contains(a)]
        allc_1g_mp.dom().contains(a)
            ==>
            page_ptr_valid(a)
            && (pg_arr.spec_index(page_ptr2page_index(a)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
}

/// 1G allocators and As1GAllocator pages agree in both directions.
#[verifier::opaque]
pub open spec fn allocator_1g_pages_wf(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray) -> bool {
    &&& allocator_1g_pages_forward_wf(allc_1g_mp, pg_arr)
    &&& allocator_1g_pages_backward_wf(allc_1g_mp, pg_arr)
}

pub proof fn allocator_1g_pages_wf_at(allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, pg_arr: PageLockedArray, allc_ptr: RwLockPageAllocatorPtr)
    requires allocator_1g_pages_wf(allc_1g_mp, pg_arr)
    ensures
        allc_1g_mp.dom().contains(allc_ptr)
            ==> page_ptr_valid(allc_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(allc_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }),
{ reveal(allocator_1g_pages_wf); }
}

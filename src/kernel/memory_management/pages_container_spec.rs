use vstd::prelude::*;
use crate::*;

verus! {
/// Page -> container: a page in state AsContainer holds a container.
pub open spec fn container_pages_forward_wf(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger ctn_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
            ==>
            ctn_mp.dom().contains(page_index2page_ptr(p_i))
}

/// Container -> page: every container sits on a valid 2M page in state AsContainer.
pub open spec fn container_pages_backward_wf(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(c)).view().view().state]
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c)
            ==>
            page_ptr_2m_valid(c)
            && (pg_arr.spec_index(page_ptr2page_index(c)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
}

/// Containers and AsContainer pages agree in both directions.
#[verifier::opaque]
pub open spec fn container_pages_wf(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& container_pages_forward_wf(ctn_mp, pg_arr)
    &&& container_pages_backward_wf(ctn_mp, pg_arr)
}

pub proof fn container_pages_wf_container_at(ctn_mp: ContainerLockedMap, pg_arr: PageLockedArray, ctn_ptr: RwLockContainerPtr)
    requires
        container_pages_wf(ctn_mp, pg_arr),
    ensures
        ctn_mp.dom().contains(ctn_ptr)
            ==> page_ptr_2m_valid(ctn_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
{ reveal(container_pages_wf); }
}

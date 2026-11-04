use vstd::prelude::*;
use crate::*;

verus! {
/// CPU sets and AsCpuSet pages agree in both directions.
#[verifier::opaque]
pub open spec fn cpu_set_pages_wf(cpu_set_mp: CpuSetLockedMap, pg_arr: PageLockedArray) -> bool {
    // Page -> CPU set.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger cpu_set_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet })
            ==>
            cpu_set_mp.dom().contains(page_index2page_ptr(p_i))
    // CPU set -> page.
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_mp.dom().contains(cpu_set_ptr)]
        #![trigger pg_arr.spec_index(page_ptr2page_index(cpu_set_ptr)).view().view().state]
        cpu_set_mp.dom().contains(cpu_set_ptr)
            ==>
            page_ptr_valid(cpu_set_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(cpu_set_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet })
}

pub proof fn cpu_set_pages_wf_at(cpu_set_mp: CpuSetLockedMap, pg_arr: PageLockedArray, cpu_set_ptr: RwLockCpuSetPtr)
    requires cpu_set_pages_wf(cpu_set_mp, pg_arr)
    ensures
        cpu_set_mp.dom().contains(cpu_set_ptr)
            ==> page_ptr_valid(cpu_set_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(cpu_set_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }),
{ reveal(cpu_set_pages_wf); }
}

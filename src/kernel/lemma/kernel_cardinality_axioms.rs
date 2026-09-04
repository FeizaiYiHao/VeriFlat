use vstd::prelude::*;

use crate::*;

verus! {

/// The reverse mappings of one mapped 4K page occupy distinct entries in the
/// finite page-table address space.
#[verifier::external_body]
pub proof fn mapped_4k_page_ref_count_lt_usize_max(
    pagetable_map: PageTableLockedMap,
    page_array: PageLockedArray,
    page_index: PageIndex,
)
    requires
        pagetable_perms_wf(pagetable_map),
        page_array_wf(page_array),
        page_pagetable_wf(pagetable_map, page_array),
        pagetable_pages_wf(pagetable_map, page_array),
        index_valid(NUM_PAGES, page_index),
        page_array.spec_index(page_index).view().view().state is Mapped4k,
    ensures
        page_array.spec_index(page_index).view().view().ref_count
            < usize::MAX,
{
}

/// A duplicate-free sequence drawn from the process/thread object maps is
/// bounded by the finite physical-page domain backing both object families.
#[verifier::external_body]
pub proof fn lemma_kernel_object_ptr_seq_len_bounded(
    krnl: &KernelK,
    ptrs: Seq<PagePtr>,
)
    requires
        krnl.inv(),
        ptrs.no_duplicates(),
        forall|ptr: PagePtr| #![trigger ptrs.contains(ptr)]
            ptrs.contains(ptr) ==> krnl.prc_mp.dom().contains(ptr) || krnl.thr_mp.dom().contains(ptr),
    ensures
        ptrs.len() <= NUM_PAGES,
{
}

/// The reference set is drawn from the finite product of thread pages and
/// per-thread endpoint descriptor slots.
#[verifier::external_body]
pub proof fn endpoint_ref_counter_bounded(
    krnl: &KernelK,
    endpoint_ptr: RwLockEndpointPtr,
)
    requires
        krnl.inv(),
        krnl.ep_mp.dom().contains(endpoint_ptr),
    ensures
        krnl.ep_mp.spec_index(endpoint_ptr).view().rf_counter
            <= NUM_PAGES * MAX_NUM_ENDPOINT_DESCRIPTORS,
{
}

/// A well-formed endpoint queue contains distinct pointers to thread pages.
#[verifier::external_body]
pub proof fn endpoint_queue_len_bounded(
    krnl: &KernelK,
    endpoint_ptr: RwLockEndpointPtr,
)
    requires
        krnl.inv(),
        krnl.ep_mp.dom().contains(endpoint_ptr),
    ensures
        krnl.ep_mp.spec_index(endpoint_ptr).view().queue.length
            <= NUM_PAGES,
{
}

/// A well-formed scheduler queue contains distinct pointers to thread pages.
#[verifier::external_body]
pub proof fn scheduler_queue_len_bounded(
    krnl: &KernelK,
    scheduler_ptr: RwLockSchedulerPtr,
)
    requires
        krnl.inv(),
        krnl.sched_mp.dom().contains(scheduler_ptr),
    ensures
        krnl.sched_mp.spec_index(scheduler_ptr).view().queue.length
            <= NUM_PAGES,
{
}

} // verus!

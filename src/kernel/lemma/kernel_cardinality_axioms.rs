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

/// A duplicate-free sequence drawn from the thread map is bounded by the
/// finite physical-page domain backing thread objects.
#[verifier::external_body]
pub proof fn lemma_thread_ptr_seq_len_bounded(
    kernel: &KernelK,
    threads: Seq<RwLockThreadPtr>,
)
    requires
        kernel.inv(),
        threads.no_duplicates(),
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger threads.contains(thread_ptr)]
            threads.contains(thread_ptr)
                ==> kernel.thread_map.dom().contains(thread_ptr),
    ensures
        threads.len() <= NUM_PAGES,
{
}

/// The reference set is drawn from the finite product of thread pages and
/// per-thread endpoint descriptor slots.
#[verifier::external_body]
pub proof fn endpoint_ref_counter_bounded(
    kernel: &KernelK,
    endpoint_ptr: RwLockEndpointPtr,
)
    requires
        kernel.inv(),
        kernel.endpoint_map.dom().contains(endpoint_ptr),
    ensures
        kernel.endpoint_map.spec_index(endpoint_ptr).view().rf_counter
            <= NUM_PAGES * MAX_NUM_ENDPOINT_DESCRIPTORS,
{
}

/// A well-formed endpoint queue contains distinct pointers to thread pages.
#[verifier::external_body]
pub proof fn endpoint_queue_len_bounded(
    kernel: &KernelK,
    endpoint_ptr: RwLockEndpointPtr,
)
    requires
        kernel.inv(),
        kernel.endpoint_map.dom().contains(endpoint_ptr),
    ensures
        kernel.endpoint_map.spec_index(endpoint_ptr).view().queue.length
            <= NUM_PAGES,
{
}

/// A well-formed scheduler queue contains distinct pointers to thread pages.
#[verifier::external_body]
pub proof fn scheduler_queue_len_bounded(
    kernel: &KernelK,
    scheduler_ptr: RwLockSchedulerPtr,
)
    requires
        kernel.inv(),
        kernel.scheduler_map.dom().contains(scheduler_ptr),
    ensures
        kernel.scheduler_map.spec_index(scheduler_ptr).view().queue.length
            <= NUM_PAGES,
{
}

} // verus!

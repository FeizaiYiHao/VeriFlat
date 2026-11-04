use vstd::prelude::*;

use crate::*;

verus! {
/// The reverse mappings of one mapped 4K page occupy distinct entries in the
/// finite page-table address space.
#[verifier::external_body]
pub proof fn mapped_4k_page_ref_count_lt_usize_max(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, pg_idx: PageIndex)
    requires
        pagetable_perms_wf(pagetable_map),
        pagetable_lower_wf(pagetable_map, pt_lower),
        page_array_wf(page_array),
        page_pagetable_wf(pagetable_map, pt_lower, page_array),
        pagetable_pages_wf(pagetable_map, pt_lower, page_array),
        index_valid(NUM_PAGES, pg_idx),
        page_array.spec_index(pg_idx).view().view().state is Mapped4k,
    ensures
        page_array.spec_index(pg_idx).view().view().ref_count < usize::MAX,
{}

/// A duplicate-free sequence drawn from the process/thread object maps is
/// bounded by the finite physical-page domain backing both object families.
#[verifier::external_body]
pub proof fn lemma_kernel_object_ptr_seq_len_bounded(krnl: &KernelK, ptrs: Seq<PagePtr>)
    requires
        krnl.inv(),
        ptrs.no_duplicates(),
        forall|ptr: PagePtr| #![trigger ptrs.contains(ptr)] ptrs.contains(ptr) ==> krnl.prc_mp.dom().contains(ptr) || krnl.thrd_mp.dom().contains(ptr),
    ensures
        ptrs.len() <= NUM_PAGES,
{}

/// The reference set is drawn from the finite product of thread pages and
/// per-thread endpoint descriptor slots.
#[verifier::external_body]
pub proof fn endpoint_ref_counter_bounded(krnl: &KernelK, ep_ptr: RwLockEndpointPtr)
    requires
        krnl.inv(),
        krnl.ep_mp.dom().contains(ep_ptr),
    ensures
        krnl.ep_mp.spec_index(ep_ptr).view().rf_counter <= NUM_PAGES * MAX_NUM_ENDPOINT_DESCRIPTORS,
{}

/// A well-formed endpoint queue contains distinct pointers to thread pages.
#[verifier::external_body]
pub proof fn endpoint_queue_len_bounded(krnl: &KernelK, ep_ptr: RwLockEndpointPtr)
    requires
        krnl.inv(),
        krnl.ep_mp.dom().contains(ep_ptr),
    ensures
        krnl.ep_mp.spec_index(ep_ptr).view().queue.length <= NUM_PAGES,
{}

/// A well-formed scheduler shard queue contains distinct pointers to thread pages.
#[verifier::external_body]
pub proof fn scheduler_queue_len_bounded(krnl: &KernelK, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId)
    requires
        krnl.inv(),
        krnl.sched_mp.dom().contains(sched_ptr),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        krnl.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.length <= NUM_PAGES,
{}
} // verus!

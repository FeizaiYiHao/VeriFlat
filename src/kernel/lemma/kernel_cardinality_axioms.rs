use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::{lemma_int_range, lemma_len_subset, lemma_map_size, set_int_range};

use crate::*;

verus! {
/// CPU and IOMMU reverse mappings each occupy a finite product of physical root pages and aligned 48-bit addresses; their combined cardinality bounds the reference count.
#[verifier::external_body]
pub proof fn mapped_4k_page_ref_count_lt_usize_max(
    pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, pg_idx: PageIndex,
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap,
)
    requires
        pagetable_perms_wf(pagetable_map),
        pagetable_lower_wf(pagetable_map, pt_lower),
        page_array_wf(page_array),
        page_mappings_pagetable_wf(pagetable_map, pt_lower, page_array),
        pagetable_pages_wf(pagetable_map, pt_lower, page_array),
        iommu_table_perms_wf(iommu_table_map),
        iommu_table_pages_wf(iommu_table_map, page_array),
        page_iommu_table_wf(container_map, process_map, iommu_table_map, page_array),
        index_valid(NUM_PAGES, pg_idx),
        page_array.spec_index(pg_idx).view().view().state is Mapped4k,
    ensures
        page_array.spec_index(pg_idx).view().view().ref_count < usize::MAX,
{}

/// A valid user 4K address is 4K aligned.
pub broadcast proof fn va_4k_valid_implies_4k_aligned(va: VAddr)
    ensures #[trigger] spec_va_4k_valid(va) ==> va % 0x1000 == 0,
{ assert(spec_va_4k_valid(va) ==> va % 0x1000 == 0) by (bit_vector); }

/// A valid user 2M address is 2M aligned.
pub broadcast proof fn va_2m_valid_implies_2m_aligned(va: VAddr)
    ensures #[trigger] spec_va_2m_valid(va) ==> va % 0x200000 == 0,
{ assert(spec_va_2m_valid(va) ==> va % 0x200000 == 0) by (bit_vector); }

/// A set of BAR mappings that are all valid 4K or 2M keys injects into [0, 2^52 + 2^43) by page number (2M page numbers
/// shifted past the 4K ones), so it has fewer than `usize::MAX` elements.
pub proof fn valid_4k_or_2m_mappings_implies_len_lt_usize_max(s: Set<PciBarMapping>)
    requires
        forall|m: PciBarMapping| #[trigger] s.contains(m) ==> (m.1 is SZ4k && spec_va_4k_valid(m.0)) || (m.1 is SZ2m && spec_va_2m_valid(m.0)),
    ensures
        s.len() < usize::MAX,
{
    broadcast use {va_4k_valid_implies_4k_aligned, va_2m_valid_implies_2m_aligned, Set::lemma_map_contains};
    let g = |m: PciBarMapping| if m.1 is SZ4k { m.0 as int / 0x1000 } else { 0x10_0000_0000_0000 + m.0 as int / 0x200000 };
    let n = 0x10_0000_0000_0000int + 0x800_0000_0000int;
    lemma_map_size(s, s.map(g), g);
    lemma_int_range(0, n);
    lemma_len_subset(s.map(g), set_int_range(0, n));
}

/// A function's recorded BAR mappings are valid 4K or 2M keys, so they number fewer than `usize::MAX`.
pub proof fn pci_function_mapping_count_lt_usize_max(
    pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, bars: Seq<PciBarEntry>, pagetable_ptr: RwLockPageTableRoot, f: PciBdf,
)
    requires
        pagetable_perms_wf(pagetable_map),
        pagetable_lower_wf(pagetable_map, pt_lower),
        pagetable_pci_mappings_wf(bars, pagetable_map, pt_lower),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains(f),
    ensures
        pagetable_map.spec_index(pagetable_ptr).view().higher.pci.view()[f].len() < usize::MAX,
{
    reveal(pagetable_pci_mappings_wf);
    valid_4k_or_2m_mappings_implies_len_lt_usize_max(whole_pagetable(pagetable_map, pt_lower, pagetable_ptr).higher.pci.view()[f]);
}

/// A duplicate-free sequence drawn from the process/thread object maps is
/// bounded by the finite physical-page domain backing both object families.
#[verifier::external_body]
pub proof fn distinct_process_or_thread_ptrs_implies_seq_len_le_num_pages(krnl: &KernelK, ptrs: Seq<PagePtr>)
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

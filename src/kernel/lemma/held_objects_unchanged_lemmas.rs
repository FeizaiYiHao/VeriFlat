use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn held_pages_unchanged_except_for_changed_set(pre: PageLockedArray, post: PageLockedArray, lctx: &LocalContext, changed: Set<PageIndex>)
    requires
        pre.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        forall|index: PageIndex| #![trigger post.spec_index(index)] #![trigger pre.spec_index(index)] index_valid(NUM_PAGES, index) && !changed.contains(index) ==> post.spec_index(index) == pre.spec_index(index),
    ensures
        held_pages_unchanged_except(pre, post, lctx, changed),
{ reveal(LockedArray::typed_lock_map_aligned); }

pub broadcast proof fn held_containers_unchanged_transitive(pre: ContainerLockedMap, middle: ContainerLockedMap, post: ContainerLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_containers_unchanged(pre, middle, pre_lctx),
        #[trigger] held_containers_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_containers_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_processes_unchanged_transitive(pre: ProcessLockedMap, middle: ProcessLockedMap, post: ProcessLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_processes_unchanged(pre, middle, pre_lctx),
        #[trigger] held_processes_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_processes_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_threads_unchanged_transitive(pre: ThreadLockedMap, middle: ThreadLockedMap, post: ThreadLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_threads_unchanged(pre, middle, pre_lctx),
        #[trigger] held_threads_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_threads_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_threads_unchanged_except_transitive(pre: ThreadLockedMap, middle: ThreadLockedMap, post: ThreadLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext, exceptions: Set<RwLockThreadPtr>)
    requires
        #[trigger] held_threads_unchanged_except(pre, middle, pre_lctx, exceptions),
        #[trigger] held_threads_unchanged_except(middle, post, middle_lctx, exceptions),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_threads_unchanged_except(pre, post, pre_lctx, exceptions),
{}

pub broadcast proof fn held_endpoints_unchanged_transitive(pre: EndpointLockedMap, middle: EndpointLockedMap, post: EndpointLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_endpoints_unchanged(pre, middle, pre_lctx),
        #[trigger] held_endpoints_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_endpoints_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_schedulers_unchanged_transitive(pre: SchedulerUnLockedMap, middle: SchedulerUnLockedMap, post: SchedulerUnLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_schedulers_unchanged(pre, middle, pre_lctx),
        #[trigger] held_schedulers_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_schedulers_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_pcid_allocators_unchanged_transitive(pre: PcidAllocatorLockedMap, middle: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_pcid_allocators_unchanged(pre, middle, pre_lctx),
        #[trigger] held_pcid_allocators_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_pcid_allocators_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_pagetables_unchanged_transitive(pre: PageTableLockedMap, middle: PageTableLockedMap, post: PageTableLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_pagetables_unchanged(pre, middle, pre_lctx),
        #[trigger] held_pagetables_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
        middle_lctx.thread_id() == pre_lctx.thread_id(),
    ensures
        held_pagetables_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_pagetables_unchanged_except_transitive(pre: PageTableLockedMap, middle: PageTableLockedMap, post: PageTableLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext, exceptions: Set<RwLockPageTableRoot>)
    requires
        #[trigger] held_pagetables_unchanged_except(pre, middle, pre_lctx, exceptions),
        #[trigger] held_pagetables_unchanged_except(middle, post, middle_lctx, exceptions),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
        middle_lctx.thread_id() == pre_lctx.thread_id(),
    ensures
        held_pagetables_unchanged_except(pre, post, pre_lctx, exceptions),
{}

pub broadcast proof fn held_iommu_tables_unchanged_transitive(pre: IommuTableLockedMap, middle: IommuTableLockedMap, post: IommuTableLockedMap, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_iommu_tables_unchanged(pre, middle, pre_lctx),
        #[trigger] held_iommu_tables_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_iommu_tables_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_cpus_unchanged_transitive(pre: CpuLockedArray, middle: CpuLockedArray, post: CpuLockedArray, pre_lctx: &LocalContext, middle_lctx: &LocalContext)
    requires
        #[trigger] held_cpus_unchanged(pre, middle, pre_lctx),
        #[trigger] held_cpus_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_cpus_unchanged(pre, post, pre_lctx),
{}

pub broadcast proof fn held_pages_unchanged_except_transitive_for_held_middle(pre: PageLockedArray, middle: PageLockedArray, post: PageLockedArray, pre_lctx: &LocalContext, middle_lctx: &LocalContext, exceptions: Set<PageIndex>)
    requires
        #[trigger] held_pages_unchanged_except(pre, middle, pre_lctx, exceptions),
        #[trigger] held_pages_unchanged(middle, post, middle_lctx),
        pre_lctx.page_lock_map().dom().subset_of(middle_lctx.page_lock_map().dom()),
    ensures
        held_pages_unchanged_except(pre, post, pre_lctx, exceptions),
{}

pub broadcast group group_held_objects_unchanged_transitive {
    held_containers_unchanged_transitive,
    held_processes_unchanged_transitive,
    held_threads_unchanged_transitive,
    held_threads_unchanged_except_transitive,
    held_endpoints_unchanged_transitive,
    held_schedulers_unchanged_transitive,
    held_pcid_allocators_unchanged_transitive,
    held_pagetables_unchanged_transitive,
    held_pagetables_unchanged_except_transitive,
    held_iommu_tables_unchanged_transitive,
    held_pages_unchanged_except_transitive_for_held_middle,
    held_cpus_unchanged_transitive,
}

pub broadcast proof fn held_kernel_objects_unchanged_reflexive(k: &KernelK, lctx: &LocalContext)
    requires
        #[trigger] typed_lock_maps_aligned(k, lctx),
    ensures
        held_containers_unchanged(k.ctn_mp, k.ctn_mp, lctx),
        held_processes_unchanged(k.prc_mp, k.prc_mp, lctx),
        held_threads_unchanged(k.thr_mp, k.thr_mp, lctx),
        held_endpoints_unchanged(k.ep_mp, k.ep_mp, lctx),
        held_schedulers_unchanged(k.sched_mp, k.sched_mp, lctx),
        held_pcid_allocators_unchanged(k.pcid_allc_mp, k.pcid_allc_mp, lctx),
        held_cpu_sets_unchanged(k.cpu_set_mp, k.cpu_set_mp, lctx),
        held_pagetables_unchanged(k.pt_mp, k.pt_mp, lctx),
        held_iommu_tables_unchanged(k.it_mp, k.it_mp, lctx),
        held_pages_unchanged(k.pg_arr, k.pg_arr, lctx),
        held_cpus_unchanged(k.cpu_arr, k.cpu_arr, lctx),
{ reveal(LockedMap::typed_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned); }

pub proof fn held_pages_unchanged_except_for_entries_unchanged_except(pre: PageLockedArray, post: PageLockedArray, lctx: &LocalContext, changed: PageIndex)
    requires
        pre.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        post.entries_unchanged_except(&pre, changed),
    ensures
        held_pages_unchanged_except(pre, post, lctx, set![changed]),
{ reveal(LockedArray::typed_lock_map_aligned); }

pub proof fn held_threads_unchanged_except_for_unchanged_except(pre: ThreadLockedMap, post: ThreadLockedMap, lctx: &LocalContext, changed: RwLockThreadPtr)
    requires
        pre.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        post.unchanged_except(&pre, changed),
    ensures
        held_threads_unchanged_except(pre, post, lctx, set![changed]),
{ reveal(LockedMap::typed_lock_map_aligned); }

pub proof fn held_pagetables_unchanged_except_for_unchanged_except(pre: PageTableLockedMap, post: PageTableLockedMap, lctx: &LocalContext, changed: RwLockPageTableRoot)
    requires
        pre.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        post.unchanged_except(&pre, changed),
    ensures
        held_pagetables_unchanged_except(pre, post, lctx, set![changed]),
{ reveal(LockedMap::typed_lock_map_aligned); }
} // verus!

use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn held_containers_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger lctx.container_lock_map().dom().contains(c)]
        #![trigger pre.spec_index(c)]
        #![trigger post.spec_index(c)]
        lctx.container_lock_map().dom().contains(c) ==> {
            &&& post.dom().contains(c)
            &&& post.spec_index(c) == pre.spec_index(c)
        }
}

pub open spec fn held_processes_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger lctx.process_lock_map().dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        lctx.process_lock_map().dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p) == pre.spec_index(p)
        }
}

pub open spec fn containers_rodata_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger pre.spec_index(c).view_rodata()]
        #![trigger post.spec_index(c).view_rodata()]
        pre.dom().contains(c) && post.dom().contains(c)
            ==> pre.spec_index(c).view_rodata() == post.spec_index(c).view_rodata()
}

pub open spec fn processes_rodata_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger pre.spec_index(p).view_rodata()]
        #![trigger post.spec_index(p).view_rodata()]
        pre.dom().contains(p) && post.dom().contains(p)
            ==> pre.spec_index(p).view_rodata() == post.spec_index(p).view_rodata()
}

/// A held process pins its owning container across an interleaving boundary.
/// This is deliberately narrower than global container-map persistence.
pub open spec fn held_process_owning_containers_unchanged(
    pre_processes: ProcessLockedMap,
    post_processes: ProcessLockedMap,
    pre_containers: ContainerLockedMap,
    post_containers: ContainerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger lctx.process_lock_map().dom().contains(p)]
        #![trigger pre_processes.spec_index(p)]
        #![trigger post_processes.spec_index(p)]
        lctx.process_lock_map().dom().contains(p) ==> {
            let c = pre_processes.spec_index(p).view_rodata().view().owning_container;
            &&& post_processes.dom().contains(p)
            &&& post_containers.dom().contains(c)
            &&& post_containers.spec_index(c).view_rodata()
                == pre_containers.spec_index(c).view_rodata()
        }
}

pub open spec fn held_threads_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger lctx.thread_lock_map().dom().contains(t)]
        #![trigger pre.spec_index(t)]
        #![trigger post.spec_index(t)]
        lctx.thread_lock_map().dom().contains(t) ==> {
            &&& post.dom().contains(t)
            &&& post.spec_index(t) == pre.spec_index(t)
        }
}

pub open spec fn held_threads_unchanged_except(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    lctx: &LocalContext,
    exceptions: Set<RwLockThreadPtr>,
) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger lctx.thread_lock_map().dom().contains(t)]
        #![trigger pre.spec_index(t)]
        #![trigger post.spec_index(t)]
        lctx.thread_lock_map().dom().contains(t) && !exceptions.contains(t) ==> {
            &&& post.dom().contains(t)
            &&& post.spec_index(t) == pre.spec_index(t)
        }
}

pub open spec fn held_endpoints_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|e: RwLockEndpointPtr|
        #![trigger lctx.endpoint_lock_map().dom().contains(e)]
        #![trigger pre.spec_index(e)]
        #![trigger post.spec_index(e)]
        lctx.endpoint_lock_map().dom().contains(e) ==> {
            &&& post.dom().contains(e)
            &&& post.spec_index(e) == pre.spec_index(e)
        }
}

pub open spec fn held_schedulers_unchanged(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|s: RwLockSchedulerPtr|
        #![trigger lctx.scheduler_lock_map().dom().contains(s)]
        #![trigger pre.spec_index(s)]
        #![trigger post.spec_index(s)]
        lctx.scheduler_lock_map().dom().contains(s) ==> {
            &&& post.dom().contains(s)
            &&& post.spec_index(s) == pre.spec_index(s)
        }
}

pub open spec fn held_pcid_allocators_unchanged(
    pre: PcidAllocatorLockedMap,
    post: PcidAllocatorLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockPcidAllocatorPtr|
        #![trigger lctx.pcid_allocator_lock_map().dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        lctx.pcid_allocator_lock_map().dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p) == pre.spec_index(p)
        }
}

pub open spec fn held_pagetables_unchanged(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        lctx.pagetable_lock_map().dom().contains(pt) ==> {
            &&& post.dom().contains(pt)
            &&& post.spec_index(pt) == pre.spec_index(pt)
        }
}

pub open spec fn held_pagetables_unchanged_except(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    lctx: &LocalContext,
    exceptions: Set<RwLockPageTableRoot>,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        lctx.pagetable_lock_map().dom().contains(pt)
            && !exceptions.contains(pt)
        ==> {
            &&& post.dom().contains(pt)
            &&& post.spec_index(pt) == pre.spec_index(pt)
        }
}

pub open spec fn held_iommu_tables_unchanged(
    pre: IommuTableLockedMap,
    post: IommuTableLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger lctx.iommu_table_lock_map().dom().contains(pt)]
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        lctx.iommu_table_lock_map().dom().contains(pt) ==> {
            &&& post.dom().contains(pt)
            &&& post.spec_index(pt) == pre.spec_index(pt)
        }
}

pub open spec fn held_pages_unchanged(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
) -> bool {
    forall|i: PageIndex|
        #![trigger lctx.page_lock_map().dom().contains(i)]
        #![trigger pre.spec_index(i)]
        #![trigger post.spec_index(i)]
        lctx.page_lock_map().dom().contains(i) ==> {
            &&& index_valid(NUM_PAGES, i)
            &&& post.spec_index(i).view() == pre.spec_index(i).view()
        }
}

pub open spec fn held_pages_unchanged_except(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
    exceptions: Set<PageIndex>,
) -> bool {
    forall|i: PageIndex|
        #![trigger lctx.page_lock_map().dom().contains(i)]
        #![trigger pre.spec_index(i)]
        #![trigger post.spec_index(i)]
        lctx.page_lock_map().dom().contains(i) && !exceptions.contains(i) ==> {
            &&& index_valid(NUM_PAGES, i)
            &&& post.spec_index(i).view() == pre.spec_index(i).view()
        }
}

pub open spec fn held_cpus_unchanged(
    pre: CpuLockedArray,
    post: CpuLockedArray,
    lctx: &LocalContext,
) -> bool {
    forall|c: CpuId|
        #![trigger lctx.cpu_lock_map().dom().contains(c)]
        #![trigger pre.spec_index(c)]
        #![trigger post.spec_index(c)]
        lctx.cpu_lock_map().dom().contains(c) ==> {
            &&& index_valid(NUM_CPUS, c)
            &&& post.spec_index(c).view() == pre.spec_index(c).view()
        }
}

pub open spec fn held_allocator_objects_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    lctx: &LocalContext,
    page_size: PageSize,
) -> bool {
    let quota_lock_map = match page_size {
        PageSize::SZ4k => lctx.allocator_quota_4k_lock_map(),
        PageSize::SZ2m => lctx.allocator_quota_2m_lock_map(),
        PageSize::SZ1g => lctx.allocator_quota_1g_lock_map(),
    };
    let cache_lock_map = match page_size {
        PageSize::SZ4k => lctx.allocator_cache_4k_lock_map(),
        PageSize::SZ2m => lctx.allocator_cache_2m_lock_map(),
        PageSize::SZ1g => lctx.allocator_cache_1g_lock_map(),
    };
    let global_pool_lock_map = match page_size {
        PageSize::SZ4k => lctx.allocator_global_pool_4k_lock_map(),
        PageSize::SZ2m => lctx.allocator_global_pool_2m_lock_map(),
        PageSize::SZ1g => lctx.allocator_global_pool_1g_lock_map(),
    };
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger quota_lock_map.dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        quota_lock_map.dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p).quota == pre.spec_index(p).quota
        })
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger global_pool_lock_map.dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        global_pool_lock_map.dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p).global_pool == pre.spec_index(p).global_pool
        })
    &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger cache_lock_map.dom().contains((p, c))]
        #![trigger pre.spec_index(p).cpu_caches.spec_index(c)]
        #![trigger post.spec_index(p).cpu_caches.spec_index(c)]
        cache_lock_map.dom().contains((p, c)) ==> {
            &&& post.dom().contains(p)
            &&& index_valid(NUM_CPUS, c)
            &&& post.spec_index(p).cpu_caches.spec_index(c).view()
                == pre.spec_index(p).cpu_caches.spec_index(c).view()
        })
}

pub broadcast proof fn held_containers_unchanged_transitive(
    pre: ContainerLockedMap,
    middle: ContainerLockedMap,
    post: ContainerLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_containers_unchanged(pre, middle, pre_lctx),
        #[trigger] held_containers_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_containers_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_processes_unchanged_transitive(
    pre: ProcessLockedMap,
    middle: ProcessLockedMap,
    post: ProcessLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_processes_unchanged(pre, middle, pre_lctx),
        #[trigger] held_processes_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_processes_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_threads_unchanged_transitive(
    pre: ThreadLockedMap,
    middle: ThreadLockedMap,
    post: ThreadLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_threads_unchanged(pre, middle, pre_lctx),
        #[trigger] held_threads_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_threads_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_threads_unchanged_except_transitive(
    pre: ThreadLockedMap,
    middle: ThreadLockedMap,
    post: ThreadLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
    exceptions: Set<RwLockThreadPtr>,
)
    requires
        #[trigger] held_threads_unchanged_except(
            pre, middle, pre_lctx, exceptions,
        ),
        #[trigger] held_threads_unchanged_except(
            middle, post, middle_lctx, exceptions,
        ),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_threads_unchanged_except(
            pre, post, pre_lctx, exceptions,
        ),
{
}

pub broadcast proof fn held_endpoints_unchanged_transitive(
    pre: EndpointLockedMap,
    middle: EndpointLockedMap,
    post: EndpointLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_endpoints_unchanged(pre, middle, pre_lctx),
        #[trigger] held_endpoints_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_endpoints_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_schedulers_unchanged_transitive(
    pre: SchedulerLockedMap,
    middle: SchedulerLockedMap,
    post: SchedulerLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_schedulers_unchanged(pre, middle, pre_lctx),
        #[trigger] held_schedulers_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_schedulers_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_pcid_allocators_unchanged_transitive(
    pre: PcidAllocatorLockedMap,
    middle: PcidAllocatorLockedMap,
    post: PcidAllocatorLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_pcid_allocators_unchanged(pre, middle, pre_lctx),
        #[trigger] held_pcid_allocators_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_pcid_allocators_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_pagetables_unchanged_transitive(
    pre: PageTableLockedMap,
    middle: PageTableLockedMap,
    post: PageTableLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_pagetables_unchanged(pre, middle, pre_lctx),
        #[trigger] held_pagetables_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_pagetables_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_pagetables_unchanged_except_transitive(
    pre: PageTableLockedMap,
    middle: PageTableLockedMap,
    post: PageTableLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
    exceptions: Set<RwLockPageTableRoot>,
)
    requires
        #[trigger] held_pagetables_unchanged_except(
            pre, middle, pre_lctx, exceptions,
        ),
        #[trigger] held_pagetables_unchanged_except(
            middle, post, middle_lctx, exceptions,
        ),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_pagetables_unchanged_except(
            pre, post, pre_lctx, exceptions,
        ),
{
}

pub broadcast proof fn held_iommu_tables_unchanged_transitive(
    pre: IommuTableLockedMap,
    middle: IommuTableLockedMap,
    post: IommuTableLockedMap,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_iommu_tables_unchanged(pre, middle, pre_lctx),
        #[trigger] held_iommu_tables_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_iommu_tables_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_cpus_unchanged_transitive(
    pre: CpuLockedArray,
    middle: CpuLockedArray,
    post: CpuLockedArray,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
)
    requires
        #[trigger] held_cpus_unchanged(pre, middle, pre_lctx),
        #[trigger] held_cpus_unchanged(middle, post, middle_lctx),
        typed_lock_maps_unchanged(pre_lctx, middle_lctx),
    ensures
        held_cpus_unchanged(pre, post, pre_lctx),
{
}

pub broadcast proof fn held_pages_unchanged_except_transitive_for_held_middle(
    pre: PageLockedArray,
    middle: PageLockedArray,
    post: PageLockedArray,
    pre_lctx: &LocalContext,
    middle_lctx: &LocalContext,
    exceptions: Set<PageIndex>,
)
    requires
        #[trigger] held_pages_unchanged_except(
            pre, middle, pre_lctx, exceptions,
        ),
        #[trigger] held_pages_unchanged(
            middle, post, middle_lctx,
        ),
        pre_lctx.page_lock_map().dom().subset_of(
            middle_lctx.page_lock_map().dom(),
        ),
    ensures
        held_pages_unchanged_except(
            pre, post, pre_lctx, exceptions,
        ),
{
}

pub broadcast group group_held_objects_unchanged_transitive {
    held_kernel_objects_unchanged_reflexive,
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

pub broadcast proof fn held_kernel_objects_unchanged_reflexive(
    k: &KernelK,
    lctx: &LocalContext,
)
    requires
        #[trigger] typed_lock_maps_aligned(k, lctx),
    ensures
        held_containers_unchanged(k.ctn_mp, k.ctn_mp, lctx),
        held_processes_unchanged(k.prc_mp, k.prc_mp, lctx),
        held_threads_unchanged(k.thr_mp, k.thr_mp, lctx),
        held_endpoints_unchanged(k.ep_mp, k.ep_mp, lctx),
        held_schedulers_unchanged(k.sched_mp, k.sched_mp, lctx),
        held_pcid_allocators_unchanged(k.pcid_allc_mp, k.pcid_allc_mp, lctx),
        held_pagetables_unchanged(k.pt_mp, k.pt_mp, lctx),
        held_iommu_tables_unchanged(k.it_mp, k.it_mp, lctx),
        held_pages_unchanged(k.pg_arr, k.pg_arr, lctx),
        held_cpus_unchanged(k.cpu_arr, k.cpu_arr, lctx),
{
    reveal(LockedMap::typed_lock_map_aligned);
    reveal(LockedArray::typed_lock_map_aligned);
}

pub proof fn held_pages_unchanged_except_for_entries_unchanged_except(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
    changed: PageIndex,
)
    requires
        pre.typed_lock_map_aligned(
            lctx.page_lock_map(), lctx.thread_id(),
        ),
        post.entries_unchanged_except(&pre, changed),
    ensures
        held_pages_unchanged_except(
            pre, post, lctx, set![changed],
        ),
{
    reveal(LockedArray::typed_lock_map_aligned);
}

pub proof fn held_threads_unchanged_except_for_unchanged_except(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    lctx: &LocalContext,
    changed: RwLockThreadPtr,
)
    requires
        pre.typed_lock_map_aligned(
            lctx.thread_lock_map(), lctx.thread_id(),
        ),
        post.unchanged_except(&pre, changed),
    ensures
        held_threads_unchanged_except(
            pre, post, lctx, set![changed],
        ),
{
    reveal(LockedMap::typed_lock_map_aligned);
}

pub proof fn held_pagetables_unchanged_except_for_unchanged_except(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    lctx: &LocalContext,
    changed: RwLockPageTableRoot,
)
    requires
        pre.typed_lock_map_aligned(
            lctx.pagetable_lock_map(), lctx.thread_id(),
        ),
        post.unchanged_except(&pre, changed),
    ensures
        held_pagetables_unchanged_except(
            pre, post, lctx, set![changed],
        ),
{
    reveal(LockedMap::typed_lock_map_aligned);
}

}

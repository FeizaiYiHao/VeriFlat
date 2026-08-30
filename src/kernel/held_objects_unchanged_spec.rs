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
        lctx.container_lock_map().dom().contains(c) ==> {
            &&& pre.dom().contains(c)
            &&& post.dom().contains(c)
            &&& post.lock_id_by_key(c) == pre.lock_id_by_key(c)
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
        lctx.process_lock_map().dom().contains(p) ==> {
            &&& pre.dom().contains(p)
            &&& post.dom().contains(p)
            &&& post.lock_id_by_key(p) == pre.lock_id_by_key(p)
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
        lctx.process_lock_map().dom().contains(p) ==> {
            let c = pre_processes.spec_index(p).view_rodata().view().owning_container;
            &&& pre_processes.dom().contains(p)
            &&& post_processes.dom().contains(p)
            &&& pre_containers.dom().contains(c)
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
        lctx.thread_lock_map().dom().contains(t) ==> {
            &&& pre.dom().contains(t)
            &&& post.dom().contains(t)
            &&& post.lock_id_by_key(t) == pre.lock_id_by_key(t)
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
        lctx.endpoint_lock_map().dom().contains(e) ==> {
            &&& pre.dom().contains(e)
            &&& post.dom().contains(e)
            &&& post.lock_id_by_key(e) == pre.lock_id_by_key(e)
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
        lctx.scheduler_lock_map().dom().contains(s) ==> {
            &&& pre.dom().contains(s)
            &&& post.dom().contains(s)
            &&& post.lock_id_by_key(s) == pre.lock_id_by_key(s)
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
        lctx.pcid_allocator_lock_map().dom().contains(p) ==> {
            &&& pre.dom().contains(p)
            &&& post.dom().contains(p)
            &&& post.lock_id_by_key(p) == pre.lock_id_by_key(p)
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
        lctx.pagetable_lock_map().dom().contains(pt) ==> {
            &&& pre.dom().contains(pt)
            &&& post.dom().contains(pt)
            &&& post.lock_id_by_key(pt) == pre.lock_id_by_key(pt)
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
        lctx.iommu_table_lock_map().dom().contains(pt) ==> {
            &&& pre.dom().contains(pt)
            &&& post.dom().contains(pt)
            &&& post.lock_id_by_key(pt) == pre.lock_id_by_key(pt)
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
        lctx.page_lock_map().dom().contains(i) ==> {
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
        lctx.cpu_lock_map().dom().contains(c) ==> {
            &&& index_valid(NUM_CPUS, c)
            &&& post.spec_index(c).view() == pre.spec_index(c).view()
        }
}

pub open spec fn held_allocator_objects_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    quota_lock_map: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
    global_pool_lock_map: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
    cache_lock_map: Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>,
) -> bool {
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger quota_lock_map.dom().contains(p)]
        quota_lock_map.dom().contains(p) ==> {
            &&& pre.dom().contains(p)
            &&& post.dom().contains(p)
            &&& post.spec_index(p).quota == pre.spec_index(p).quota
        })
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger global_pool_lock_map.dom().contains(p)]
        global_pool_lock_map.dom().contains(p) ==> {
            &&& pre.dom().contains(p)
            &&& post.dom().contains(p)
            &&& post.spec_index(p).global_pool == pre.spec_index(p).global_pool
        })
    &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger cache_lock_map.dom().contains((p, c))]
        cache_lock_map.dom().contains((p, c)) ==> {
            &&& pre.dom().contains(p)
            &&& post.dom().contains(p)
            &&& index_valid(NUM_CPUS, c)
            &&& post.spec_index(p).cpu_caches.spec_index(c).view()
                == pre.spec_index(p).cpu_caches.spec_index(c).view()
        })
}

}

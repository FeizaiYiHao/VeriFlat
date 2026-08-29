use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn held_containers_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger pre.spec_index(c)]
        #![trigger post.spec_index(c)]
        {
            let pre_held = pre.dom().contains(c)
                && pre.spec_index(c).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(c)
                && post.spec_index(c).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(c) == pre.lock_id_by_key(c)
            &&& pre_held ==> post.spec_index(c) == pre.spec_index(c)
        }
}

pub open spec fn held_processes_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        {
            let pre_held = pre.dom().contains(p)
                && pre.spec_index(p).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(p)
                && post.spec_index(p).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(p) == pre.lock_id_by_key(p)
            &&& pre_held ==> post.spec_index(p) == pre.spec_index(p)
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
        #![trigger pre_processes.spec_index(p)]
        #![trigger post_processes.spec_index(p)]
        pre_processes.dom().contains(p)
            && pre_processes.spec_index(p).locked_by_thread(lctx.thread_id())
        ==> {
            let c = pre_processes.spec_index(p).view_rodata().view().owning_container;
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
        #![trigger pre.spec_index(t)]
        #![trigger post.spec_index(t)]
        {
            let pre_held = pre.dom().contains(t)
                && pre.spec_index(t).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(t)
                && post.spec_index(t).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(t) == pre.lock_id_by_key(t)
            &&& pre_held ==> post.spec_index(t) == pre.spec_index(t)
        }
}

pub open spec fn held_endpoints_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|e: RwLockEndpointPtr|
        #![trigger pre.spec_index(e)]
        #![trigger post.spec_index(e)]
        {
            let pre_held = pre.dom().contains(e)
                && pre.spec_index(e).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(e)
                && post.spec_index(e).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(e) == pre.lock_id_by_key(e)
            &&& pre_held ==> post.spec_index(e) == pre.spec_index(e)
        }
}

pub open spec fn held_schedulers_unchanged(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|s: RwLockSchedulerPtr|
        #![trigger pre.spec_index(s)]
        #![trigger post.spec_index(s)]
        {
            let pre_held = pre.dom().contains(s)
                && pre.spec_index(s).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(s)
                && post.spec_index(s).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(s) == pre.lock_id_by_key(s)
            &&& pre_held ==> post.spec_index(s) == pre.spec_index(s)
        }
}

pub open spec fn held_pcid_allocators_unchanged(
    pre: PcidAllocatorLockedMap,
    post: PcidAllocatorLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockPcidAllocatorPtr|
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        {
            let pre_held = pre.dom().contains(p)
                && pre.spec_index(p).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(p)
                && post.spec_index(p).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(p) == pre.lock_id_by_key(p)
            &&& pre_held ==> post.spec_index(p) == pre.spec_index(p)
        }
}

pub open spec fn held_pagetables_unchanged(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        {
            let pre_held = pre.dom().contains(pt)
                && pre.spec_index(pt).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(pt)
                && post.spec_index(pt).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(pt) == pre.lock_id_by_key(pt)
            &&& pre_held ==> post.spec_index(pt) == pre.spec_index(pt)
        }
}

pub open spec fn held_iommu_tables_unchanged(
    pre: IommuTableLockedMap,
    post: IommuTableLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        {
            let pre_held = pre.dom().contains(pt)
                && pre.spec_index(pt).locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(pt)
                && post.spec_index(pt).locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.lock_id_by_key(pt) == pre.lock_id_by_key(pt)
            &&& pre_held ==> post.spec_index(pt) == pre.spec_index(pt)
        }
}

pub open spec fn held_pages_unchanged(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
) -> bool {
    forall|i: PageIndex|
        #![trigger pre.spec_index(i)]
        #![trigger post.spec_index(i)]
        {
            let pre_held = index_valid(NUM_PAGES, i)
                && pre.spec_index(i).view().locked_by_thread(lctx.thread_id());
            let post_held = index_valid(NUM_PAGES, i)
                && post.spec_index(i).view().locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.spec_index(i).view() == pre.spec_index(i).view()
        }
}

pub open spec fn held_cpus_unchanged(
    pre: CpuLockedArray,
    post: CpuLockedArray,
    lctx: &LocalContext,
) -> bool {
    forall|c: CpuId|
        #![trigger pre.spec_index(c)]
        #![trigger post.spec_index(c)]
        {
            let pre_held = index_valid(NUM_CPUS, c)
                && pre.spec_index(c).view().locked_by_thread(lctx.thread_id());
            let post_held = index_valid(NUM_CPUS, c)
                && post.spec_index(c).view().locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.spec_index(c).view() == pre.spec_index(c).view()
        }
}

pub open spec fn held_allocator_objects_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    lctx: &LocalContext,
) -> bool {
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        {
            let pre_held = pre.dom().contains(p)
                && pre.spec_index(p).quota.locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(p)
                && post.spec_index(p).quota.locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.spec_index(p).quota == pre.spec_index(p).quota
        })
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        {
            let pre_held = pre.dom().contains(p)
                && pre.spec_index(p).global_pool.locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(p)
                && post.spec_index(p).global_pool.locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.spec_index(p).global_pool == pre.spec_index(p).global_pool
        })
    &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger pre.spec_index(p).cpu_caches.spec_index(c)]
        #![trigger post.spec_index(p).cpu_caches.spec_index(c)]
        {
            let pre_held = pre.dom().contains(p)
                && index_valid(NUM_CPUS, c)
                && pre.spec_index(p).cpu_caches.spec_index(c).view()
                    .locked_by_thread(lctx.thread_id());
            let post_held = post.dom().contains(p)
                && index_valid(NUM_CPUS, c)
                && post.spec_index(p).cpu_caches.spec_index(c).view()
                    .locked_by_thread(lctx.thread_id());
            &&& pre_held == post_held
            &&& pre_held ==> post.spec_index(p).cpu_caches.spec_index(c).view()
                == pre.spec_index(p).cpu_caches.spec_index(c).view()
        })
}

pub proof fn endpoint_objects_unlocked_except_preserved_for_held_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    lctx: &LocalContext,
    exceptions: Set<RwLockEndpointPtr>,
)
    requires
        endpoint_objects_unlocked_except(
            pre, lctx.thread_id(), exceptions,
        ),
        held_endpoints_unchanged(pre, post, lctx),
    ensures
        endpoint_objects_unlocked_except(
            post, lctx.thread_id(), exceptions,
        ),
{
}

}

use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn no_new_allocator_locks_by_thread(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    thread_id: LockThreadId,
) -> bool {
    &&& forall|p: RwLockPageAllocatorPtr|
        #![trigger post.spec_index(p).quota.locked_by_thread(thread_id)]
        post.dom().contains(p) && post.spec_index(p).quota.locked_by_thread(thread_id)
        ==> pre.dom().contains(p)
            && pre.spec_index(p).quota.locked_by_thread(thread_id)
    &&& forall|p: RwLockPageAllocatorPtr|
        #![trigger post.spec_index(p).global_pool.locked_by_thread(thread_id)]
        post.dom().contains(p)
            && post.spec_index(p).global_pool.locked_by_thread(thread_id)
        ==> pre.dom().contains(p)
            && pre.spec_index(p).global_pool.locked_by_thread(thread_id)
    &&& forall|p: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger post.spec_index(p).cpu_caches.spec_index(c).view()
            .locked_by_thread(thread_id)]
        post.dom().contains(p)
            && cpu_id_valid(c)
            && post.spec_index(p).cpu_caches.spec_index(c).view()
                .locked_by_thread(thread_id)
        ==> pre.dom().contains(p)
            && pre.spec_index(p).cpu_caches.spec_index(c).view()
                .locked_by_thread(thread_id)
}

/// Interleaving cannot acquire a read or write lock on behalf of this thread.
/// This is a direct physical-lock relation; it does not recover negative lock
/// facts through the LocalContext held-lock ledger.
pub open spec fn no_new_nonpage_locks_by_thread(
    pre: &KernelK,
    post: &KernelK,
    thread_id: LockThreadId,
) -> bool {
    &&& forall|c: CpuId|
        #![trigger post.cpu_array.spec_index(c).view().locked_by_thread(thread_id)]
        cpu_id_valid(c)
            && post.cpu_array.spec_index(c).view().locked_by_thread(thread_id)
        ==> pre.cpu_array.spec_index(c).view().locked_by_thread(thread_id)
    &&& forall|c: RwLockContainerPtr|
        #![trigger post.container_map.spec_index(c).locked_by_thread(thread_id)]
        post.container_map.dom().contains(c)
            && post.container_map.spec_index(c).locked_by_thread(thread_id)
        ==> pre.container_map.dom().contains(c)
            && pre.container_map.spec_index(c).locked_by_thread(thread_id)
    &&& forall|p: RwLockProcessPtr|
        #![trigger post.process_map.spec_index(p).locked_by_thread(thread_id)]
        post.process_map.dom().contains(p)
            && post.process_map.spec_index(p).locked_by_thread(thread_id)
        ==> pre.process_map.dom().contains(p)
            && pre.process_map.spec_index(p).locked_by_thread(thread_id)
    &&& forall|t: RwLockThreadPtr|
        #![trigger post.thread_map.spec_index(t).locked_by_thread(thread_id)]
        post.thread_map.dom().contains(t)
            && post.thread_map.spec_index(t).locked_by_thread(thread_id)
        ==> pre.thread_map.dom().contains(t)
            && pre.thread_map.spec_index(t).locked_by_thread(thread_id)
    &&& forall|e: RwLockEndpointPtr|
        #![trigger post.endpoint_map.spec_index(e).locked_by_thread(thread_id)]
        post.endpoint_map.dom().contains(e)
            && post.endpoint_map.spec_index(e).locked_by_thread(thread_id)
        ==> pre.endpoint_map.dom().contains(e)
            && pre.endpoint_map.spec_index(e).locked_by_thread(thread_id)
    &&& forall|s: RwLockSchedulerPtr|
        #![trigger post.scheduler_map.spec_index(s).locked_by_thread(thread_id)]
        post.scheduler_map.dom().contains(s)
            && post.scheduler_map.spec_index(s).locked_by_thread(thread_id)
        ==> pre.scheduler_map.dom().contains(s)
            && pre.scheduler_map.spec_index(s).locked_by_thread(thread_id)
    &&& forall|p: RwLockPcidAllocatorPtr|
        #![trigger post.pcid_allocator_map.spec_index(p).locked_by_thread(thread_id)]
        post.pcid_allocator_map.dom().contains(p)
            && post.pcid_allocator_map.spec_index(p).locked_by_thread(thread_id)
        ==> pre.pcid_allocator_map.dom().contains(p)
            && pre.pcid_allocator_map.spec_index(p).locked_by_thread(thread_id)
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger post.pagetable_map.spec_index(pt).locked_by_thread(thread_id)]
        post.pagetable_map.dom().contains(pt)
            && post.pagetable_map.spec_index(pt).locked_by_thread(thread_id)
        ==> pre.pagetable_map.dom().contains(pt)
            && pre.pagetable_map.spec_index(pt).locked_by_thread(thread_id)
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger post.iommu_table_map.spec_index(pt).locked_by_thread(thread_id)]
        post.iommu_table_map.dom().contains(pt)
            && post.iommu_table_map.spec_index(pt).locked_by_thread(thread_id)
        ==> pre.iommu_table_map.dom().contains(pt)
            && pre.iommu_table_map.spec_index(pt).locked_by_thread(thread_id)
    &&& no_new_allocator_locks_by_thread(
        pre.allocator_4k_map, post.allocator_4k_map, thread_id)
    &&& no_new_allocator_locks_by_thread(
        pre.allocator_2m_map, post.allocator_2m_map, thread_id)
    &&& no_new_allocator_locks_by_thread(
        pre.allocator_1g_map, post.allocator_1g_map, thread_id)
}

#[verifier::opaque]
pub open spec fn no_new_locks_by_thread(
    pre: &KernelK,
    post: &KernelK,
    thread_id: LockThreadId,
) -> bool {
    &&& no_new_nonpage_locks_by_thread(pre, post, thread_id)
    &&& forall|i: PageIndex|
        #![trigger post.page_array.spec_index(i).view().locked_by_thread(thread_id)]
        page_index_valid(i)
            && post.page_array.spec_index(i).view().locked_by_thread(thread_id)
        ==> pre.page_array.spec_index(i).view().locked_by_thread(thread_id)
}

/// Per-type framing predicates for objects read- or write-held by the supplied local
/// context.  The real object state is the anchor; these predicates do not
/// inspect or duplicate the LocalContext held-lock ledger.
pub open spec fn held_containers_unchanged_except(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockContainerPtr>,
) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger pre.spec_index(c).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(c).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(c)
            && pre.spec_index(c).locked_by_thread(lctx.thread_id())
            && !except.contains(c)
        ==> post.dom().contains(c)
            && post.spec_index(c) == pre.spec_index(c)
            && post.spec_index(c).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_processes_unchanged_except(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockProcessPtr>,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger pre.spec_index(p).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(p).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p)
            && pre.spec_index(p).locked_by_thread(lctx.thread_id())
            && !except.contains(p)
        ==> post.dom().contains(p)
            && post.spec_index(p) == pre.spec_index(p)
            && post.spec_index(p).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_threads_unchanged_except(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockThreadPtr>,
) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger pre.spec_index(t).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(t).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(t)
            && pre.spec_index(t).locked_by_thread(lctx.thread_id())
            && !except.contains(t)
        ==> post.dom().contains(t)
            && post.spec_index(t) == pre.spec_index(t)
            && post.spec_index(t).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_endpoints_unchanged_except(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockEndpointPtr>,
) -> bool {
    forall|e: RwLockEndpointPtr|
        #![trigger pre.spec_index(e).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(e).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(e)
            && pre.spec_index(e).locked_by_thread(lctx.thread_id())
            && !except.contains(e)
        ==> post.dom().contains(e)
            && post.spec_index(e) == pre.spec_index(e)
            && post.spec_index(e).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_schedulers_unchanged_except(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockSchedulerPtr>,
) -> bool {
    forall|s: RwLockSchedulerPtr|
        #![trigger pre.spec_index(s).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(s).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(s)
            && pre.spec_index(s).locked_by_thread(lctx.thread_id())
            && !except.contains(s)
        ==> post.dom().contains(s)
            && post.spec_index(s) == pre.spec_index(s)
            && post.spec_index(s).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_pcid_allocators_unchanged_except(
    pre: PcidAllocatorLockedMap,
    post: PcidAllocatorLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockPcidAllocatorPtr>,
) -> bool {
    forall|p: RwLockPcidAllocatorPtr|
        #![trigger pre.spec_index(p).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(p).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p)
            && pre.spec_index(p).locked_by_thread(lctx.thread_id())
            && !except.contains(p)
        ==> post.dom().contains(p)
            && post.spec_index(p) == pre.spec_index(p)
            && post.spec_index(p).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_pagetables_unchanged_except(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockPageTableRoot>,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(pt).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(pt)
            && pre.spec_index(pt).locked_by_thread(lctx.thread_id())
            && !except.contains(pt)
        ==> post.dom().contains(pt)
            && post.spec_index(pt) == pre.spec_index(pt)
            && post.spec_index(pt).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_iommu_tables_unchanged_except(
    pre: IommuTableLockedMap,
    post: IommuTableLockedMap,
    lctx: &LocalContext,
    except: Set<RwLockPageTableRoot>,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(pt).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(pt)
            && pre.spec_index(pt).locked_by_thread(lctx.thread_id())
            && !except.contains(pt)
        ==> post.dom().contains(pt)
            && post.spec_index(pt) == pre.spec_index(pt)
            && post.spec_index(pt).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_pages_unchanged_except(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
    except: Set<PageIndex>,
) -> bool {
    forall|i: PageIndex|
        #![trigger pre.spec_index(i).view().locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(i).view().locked_by_thread(lctx.thread_id())]
        page_index_wf(i)
            && pre.spec_index(i).view().locked_by_thread(lctx.thread_id())
            && !except.contains(i)
        ==> post.spec_index(i).view() == pre.spec_index(i).view()
            && post.spec_index(i).view().locked_by_thread(lctx.thread_id())
}

pub open spec fn held_cpus_unchanged_except(
    pre: CpuLockedArray,
    post: CpuLockedArray,
    lctx: &LocalContext,
    except: Set<CpuId>,
) -> bool {
    forall|c: CpuId|
        #![trigger pre.spec_index(c).view().locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(c).view().locked_by_thread(lctx.thread_id())]
        cpu_id_valid(c)
            && pre.spec_index(c).view().locked_by_thread(lctx.thread_id())
            && !except.contains(c)
        ==> post.spec_index(c).view() == pre.spec_index(c).view()
            && post.spec_index(c).view().locked_by_thread(lctx.thread_id())
}

pub open spec fn held_containers_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger pre.spec_index(c).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(c).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(c) && pre.spec_index(c).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(c)
            && post.spec_index(c) == pre.spec_index(c)
            && post.spec_index(c).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_processes_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger pre.spec_index(p).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(p).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p) && pre.spec_index(p).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(p)
            && post.spec_index(p) == pre.spec_index(p)
            && post.spec_index(p).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_threads_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger pre.spec_index(t).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(t).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(t) && pre.spec_index(t).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(t)
            && post.spec_index(t) == pre.spec_index(t)
            && post.spec_index(t).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_endpoints_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|e: RwLockEndpointPtr|
        #![trigger pre.spec_index(e).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(e).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(e) && pre.spec_index(e).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(e)
            && post.spec_index(e) == pre.spec_index(e)
            && post.spec_index(e).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_schedulers_unchanged(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|s: RwLockSchedulerPtr|
        #![trigger pre.spec_index(s).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(s).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(s) && pre.spec_index(s).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(s)
            && post.spec_index(s) == pre.spec_index(s)
            && post.spec_index(s).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_pcid_allocators_unchanged(
    pre: PcidAllocatorLockedMap,
    post: PcidAllocatorLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockPcidAllocatorPtr|
        #![trigger pre.spec_index(p).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(p).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p) && pre.spec_index(p).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(p)
            && post.spec_index(p) == pre.spec_index(p)
            && post.spec_index(p).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_pagetables_unchanged(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(pt).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(pt) && pre.spec_index(pt).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(pt)
            && post.spec_index(pt) == pre.spec_index(pt)
            && post.spec_index(pt).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_iommu_tables_unchanged(
    pre: IommuTableLockedMap,
    post: IommuTableLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt).locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(pt).locked_by_thread(lctx.thread_id())]
        pre.dom().contains(pt) && pre.spec_index(pt).locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(pt)
            && post.spec_index(pt) == pre.spec_index(pt)
            && post.spec_index(pt).locked_by_thread(lctx.thread_id())
}

pub open spec fn held_pages_unchanged(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
) -> bool {
    forall|i: PageIndex|
        #![trigger pre.spec_index(i).view().locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(i).view().locked_by_thread(lctx.thread_id())]
        page_index_wf(i) && pre.spec_index(i).view().locked_by_thread(lctx.thread_id())
        ==> post.spec_index(i).view() == pre.spec_index(i).view()
            && post.spec_index(i).view().locked_by_thread(lctx.thread_id())
}

pub open spec fn held_cpus_unchanged(
    pre: CpuLockedArray,
    post: CpuLockedArray,
    lctx: &LocalContext,
) -> bool {
    forall|c: CpuId|
        #![trigger pre.spec_index(c).view().locked_by_thread(lctx.thread_id())]
        #![trigger post.spec_index(c).view().locked_by_thread(lctx.thread_id())]
        cpu_id_valid(c) && pre.spec_index(c).view().locked_by_thread(lctx.thread_id())
        ==> post.spec_index(c).view() == pre.spec_index(c).view()
            && post.spec_index(c).view().locked_by_thread(lctx.thread_id())
}

pub open spec fn held_allocator_objects_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    lctx: &LocalContext,
) -> bool {
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(p).quota.locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p) && pre.spec_index(p).quota.locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(p)
            && post.spec_index(p).quota == pre.spec_index(p).quota
            && post.spec_index(p).quota.locked_by_thread(lctx.thread_id()))
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(p).global_pool.locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p) && pre.spec_index(p).global_pool.locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(p)
            && post.spec_index(p).global_pool == pre.spec_index(p).global_pool
            && post.spec_index(p).global_pool.locked_by_thread(lctx.thread_id()))
    &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger pre.spec_index(p).cpu_caches.spec_index(c).view()
            .locked_by_thread(lctx.thread_id())]
        pre.dom().contains(p)
            && cpu_id_valid(c)
            && pre.spec_index(p).cpu_caches.spec_index(c).view()
                .locked_by_thread(lctx.thread_id())
        ==> post.dom().contains(p)
            && post.spec_index(p).cpu_caches.spec_index(c).view()
                == pre.spec_index(p).cpu_caches.spec_index(c).view()
            && post.spec_index(p).cpu_caches.spec_index(c).view()
                .locked_by_thread(lctx.thread_id()))
}

}

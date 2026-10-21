use vstd::prelude::*;
use crate::*;

verus! {
pub open spec fn held_containers_unchanged(pre: ContainerLockedMap, post: ContainerLockedMap, lctx: &LocalContext) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger lctx.container_lock_map().dom().contains(c)]
        #![trigger pre.spec_index(c)]
        #![trigger post.spec_index(c)]
        lctx.container_lock_map().dom().contains(c) ==> {
            &&& post.dom().contains(c)
            &&& post.spec_index(c) == pre.spec_index(c)
        }
}

pub open spec fn held_processes_unchanged(pre: ProcessLockedMap, post: ProcessLockedMap, lctx: &LocalContext) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger lctx.process_lock_map().dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        lctx.process_lock_map().dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p) == pre.spec_index(p)
        }
}

pub open spec fn containers_rodata_unchanged(pre: ContainerLockedMap, post: ContainerLockedMap) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger pre.spec_index(c).view_rodata()]
        #![trigger post.spec_index(c).view_rodata()]
        pre.dom().contains(c) && post.dom().contains(c) ==> pre.spec_index(c).view_rodata() == post.spec_index(c).view_rodata()
}

pub open spec fn processes_rodata_unchanged(pre: ProcessLockedMap, post: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger pre.spec_index(p).view_rodata()]
        #![trigger post.spec_index(p).view_rodata()]
        pre.dom().contains(p) && post.dom().contains(p) ==> pre.spec_index(p).view_rodata() == post.spec_index(p).view_rodata()
}

pub open spec fn held_threads_unchanged(pre: ThreadLockedMap, post: ThreadLockedMap, lctx: &LocalContext) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger lctx.thread_lock_map().dom().contains(t)]
        #![trigger pre.spec_index(t)]
        #![trigger post.spec_index(t)]
        lctx.thread_lock_map().dom().contains(t) ==> {
            &&& post.dom().contains(t)
            &&& post.spec_index(t) == pre.spec_index(t)
        }
}

pub open spec fn held_threads_unchanged_except(pre: ThreadLockedMap, post: ThreadLockedMap, lctx: &LocalContext, exceptions: Set<RwLockThreadPtr>) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger lctx.thread_lock_map().dom().contains(t)]
        #![trigger pre.spec_index(t)]
        #![trigger post.spec_index(t)]
        lctx.thread_lock_map().dom().contains(t) && !exceptions.contains(t) ==> {
            &&& post.dom().contains(t)
            &&& post.spec_index(t) == pre.spec_index(t)
        }
}

pub open spec fn held_endpoints_unchanged(pre: EndpointLockedMap, post: EndpointLockedMap, lctx: &LocalContext) -> bool {
    forall|e: RwLockEndpointPtr|
        #![trigger lctx.endpoint_lock_map().dom().contains(e)]
        #![trigger pre.spec_index(e)]
        #![trigger post.spec_index(e)]
        lctx.endpoint_lock_map().dom().contains(e) ==> {
            &&& post.dom().contains(e)
            &&& post.spec_index(e) == pre.spec_index(e)
        }
}

pub open spec fn held_schedulers_unchanged(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, lctx: &LocalContext) -> bool {
    forall|s: RwLockSchedulerPtr, c: CpuId|
        #![trigger lctx.scheduler_lock_map().dom().contains((s, c))]
        #![trigger pre.spec_index(s).shards.spec_index(c)]
        #![trigger post.spec_index(s).shards.spec_index(c)]
        lctx.scheduler_lock_map().dom().contains((s, c)) ==> {
            &&& post.dom().contains(s)
            &&& post.spec_index(s).shards.spec_index(c) == pre.spec_index(s).shards.spec_index(c)
        }
}

pub open spec fn held_pcid_allocators_unchanged(pre: PcidAllocatorLockedMap, post: PcidAllocatorLockedMap, lctx: &LocalContext) -> bool {
    forall|p: RwLockPcidAllocatorPtr|
        #![trigger lctx.pcid_allocator_lock_map().dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        lctx.pcid_allocator_lock_map().dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p) == pre.spec_index(p)
        }
}

pub open spec fn held_cpu_sets_unchanged(pre: CpuSetLockedMap, post: CpuSetLockedMap, lctx: &LocalContext) -> bool {
    forall|p: RwLockCpuSetPtr|
        #![trigger lctx.cpu_set_lock_map().dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        lctx.cpu_set_lock_map().dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p) == pre.spec_index(p)
        }
}

/// A write-held page table keeps its whole big-lock entry; a read-held one keeps its payload, this thread's read
/// hold and reader token, and its kill mark, while other readers may come and go.
pub open spec fn held_pagetables_unchanged(pre: PageTableLockedMap, post: PageTableLockedMap, lctx: &LocalContext) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        lctx.pagetable_lock_map().dom().contains(pt) ==> {
            &&& post.dom().contains(pt)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pt, TypedLockMode::Write) ==> post.spec_index(pt) == pre.spec_index(pt)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pt, TypedLockMode::Read) ==> {
                &&& post.spec_index(pt).view() == pre.spec_index(pt).view()
                &&& post.spec_index(pt).rlocked_by_thread(lctx.thread_id())
                &&& post.spec_index(pt).being_killed() == pre.spec_index(pt).being_killed()
                &&& post.spec_index(pt).locking_thread()->Read_reader_map.spec_index(lctx.thread_id()) == pre.spec_index(pt).locking_thread()->Read_reader_map.spec_index(lctx.thread_id())
            }
        }
}

pub open spec fn held_pagetables_unchanged_except(pre: PageTableLockedMap, post: PageTableLockedMap, lctx: &LocalContext, exceptions: Set<RwLockPageTableRoot>) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        lctx.pagetable_lock_map().dom().contains(pt) && !exceptions.contains(pt) ==> {
            &&& post.dom().contains(pt)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pt, TypedLockMode::Write) ==> post.spec_index(pt) == pre.spec_index(pt)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pt, TypedLockMode::Read) ==> {
                &&& post.spec_index(pt).view() == pre.spec_index(pt).view()
                &&& post.spec_index(pt).rlocked_by_thread(lctx.thread_id())
                &&& post.spec_index(pt).being_killed() == pre.spec_index(pt).being_killed()
                &&& post.spec_index(pt).locking_thread()->Read_reader_map.spec_index(lctx.thread_id()) == pre.spec_index(pt).locking_thread()->Read_reader_map.spec_index(lctx.thread_id())
            }
        }
}

/// Each held 2M window `(pt, w)` keeps its window record (L2 page and entry, lock owner, linked L1 page, stale CPUs),
/// every 4K leaf inside the window, and the 2M leaf at `w`.
pub open spec fn held_pagetable_windows_unchanged(pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, lctx: &LocalContext) -> bool {
    forall|pt: RwLockPageTableRoot, w: WindowVa|
        #![trigger lctx.pagetable_window_lock_map().dom().contains((pt, w))]
        lctx.pagetable_window_lock_map().dom().contains((pt, w)) ==> {
            let pre = pagetable_c(pre_pt, pre_lower, pt);
            let post = pagetable_c(post_pt, post_lower, pt);
            &&& post.window_view(w) == pre.window_view(w)
            &&& forall|v: VAddr|
                #![trigger pagetable_c(post_pt, post_lower, pt).mapping_4k().dom().contains(v)]
                #![trigger pagetable_c(pre_pt, pre_lower, pt).mapping_4k().dom().contains(v)]
                spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                    &&& pagetable_c(post_pt, post_lower, pt).mapping_4k().dom().contains(v) == pagetable_c(pre_pt, pre_lower, pt).mapping_4k().dom().contains(v)
                    &&& pagetable_c(pre_pt, pre_lower, pt).mapping_4k().dom().contains(v)
                        ==> pagetable_c(post_pt, post_lower, pt).mapping_4k().spec_index(v) == pagetable_c(pre_pt, pre_lower, pt).mapping_4k().spec_index(v)
                }
            &&& post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
        }
}

/// The 4K leaf `v` inside the held window `(pt, w)` is unchanged.
pub proof fn held_pagetable_window_mapping_4k_unchanged_at(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, lctx: &LocalContext, pt: RwLockPageTableRoot, w: WindowVa, v: VAddr,
)
    requires
        held_pagetable_windows_unchanged(pre_pt, pre_lower, post_pt, post_lower, lctx),
        lctx.pagetable_window_lock_map().dom().contains((pt, w)),
        spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va),
    ensures
        pagetable_c(post_pt, post_lower, pt).mapping_4k().dom().contains(v) == pagetable_c(pre_pt, pre_lower, pt).mapping_4k().dom().contains(v),
        pagetable_c(pre_pt, pre_lower, pt).mapping_4k().dom().contains(v) ==> pagetable_c(post_pt, post_lower, pt).mapping_4k().spec_index(v) == pagetable_c(pre_pt, pre_lower, pt).mapping_4k().spec_index(v),
{}

pub open spec fn held_iommu_tables_unchanged(pre: IommuTableLockedMap, post: IommuTableLockedMap, lctx: &LocalContext) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger lctx.iommu_table_lock_map().dom().contains(pt)]
        #![trigger pre.spec_index(pt)]
        #![trigger post.spec_index(pt)]
        lctx.iommu_table_lock_map().dom().contains(pt) ==> {
            &&& post.dom().contains(pt)
            &&& post.spec_index(pt) == pre.spec_index(pt)
        }
}

/// Holding the one root-table lock pins the whole table.
pub open spec fn held_iommu_root_table_unchanged(pre: IommuRootTableLock, post: IommuRootTableLock, lctx: &LocalContext) -> bool {
    forall|table_base: PAddr| #![trigger lctx.iommu_root_table_lock_map().dom().contains(table_base)] lctx.iommu_root_table_lock_map().dom().contains(table_base) ==> post == pre
}

pub open spec fn held_pages_unchanged(pre: PageLockedArray, post: PageLockedArray, lctx: &LocalContext) -> bool {
    forall|i: PageIndex|
        #![trigger lctx.page_lock_map().dom().contains(i)]
        lctx.page_lock_map().dom().contains(i) ==> {
            &&& index_valid(NUM_PAGES, i)
            &&& post.spec_index(i).view() == pre.spec_index(i).view()
        }
}

pub open spec fn held_pages_unchanged_except(pre: PageLockedArray, post: PageLockedArray, lctx: &LocalContext, exceptions: Set<PageIndex>) -> bool {
    forall|i: PageIndex|
        #![trigger lctx.page_lock_map().dom().contains(i)]
        #![trigger pre.spec_index(i)]
        #![trigger post.spec_index(i)]
        lctx.page_lock_map().dom().contains(i) && !exceptions.contains(i) ==> {
            &&& index_valid(NUM_PAGES, i)
            &&& post.spec_index(i).view() == pre.spec_index(i).view()
        }
}

pub open spec fn held_cpus_unchanged(pre: CpuLockedArray, post: CpuLockedArray, lctx: &LocalContext) -> bool {
    forall|c: CpuId|
        #![trigger lctx.cpu_lock_map().dom().contains(c)]
        #![trigger pre.spec_index(c)]
        #![trigger post.spec_index(c)]
        lctx.cpu_lock_map().dom().contains(c) ==> {
            &&& index_valid(NUM_CPUS, c)
            &&& post.spec_index(c).view() == pre.spec_index(c).view()
        }
}

pub open spec fn held_allocator_objects_unchanged<const SIZE: usize>(pre: PageAllocatorUnLockedMap<SIZE>, post: PageAllocatorUnLockedMap<SIZE>, lctx: &LocalContext, page_size: PageSize) -> bool {
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
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        quota_lock_map.dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p).quota == pre.spec_index(p).quota
        })
    &&& (forall|p: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        global_pool_lock_map.dom().contains(p) ==> {
            &&& post.dom().contains(p)
            &&& post.spec_index(p).global_pool == pre.spec_index(p).global_pool
        })
    &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
        #![trigger pre.spec_index(p).cpu_caches.spec_index(c)]
        #![trigger post.spec_index(p).cpu_caches.spec_index(c)]
        cache_lock_map.dom().contains((p, c)) ==> {
            &&& post.dom().contains(p)
            &&& index_valid(NUM_CPUS, c)
            &&& post.spec_index(p).cpu_caches.spec_index(c).view() == pre.spec_index(p).cpu_caches.spec_index(c).view()
        })
}
}

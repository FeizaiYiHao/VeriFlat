use vstd::prelude::*;
use crate::*;

verus! {
/// Lock-map framing used by the step-boundary wrappers for every map a section
/// restores. `relocked` names the one entry (if any) the section re-acquired.
impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> LockedMap<usize, T, ROT, GhostT, HAS_KILL_STATE> {
    /// `old`, except that `relocked` may differ in lock owner or token while
    /// keeping its lock mode and payload (`RwLock::relocked_from`).
    pub open spec fn unchanged_except_relock(&self, old: &Self, relocked: Option<usize>) -> bool {
        match relocked {
            Some(key) => self.unchanged_except(old, key) && self.spec_index(key).relocked_from(&old.spec_index(key)),
            None => self == old,
        }
    }

    /// `old`, except that `relocked` may differ in any way other than lock mode.
    pub open spec fn unchanged_except_same_lock_mode(&self, old: &Self, relocked: Option<usize>) -> bool {
        match relocked {
            Some(key) => self.unchanged_except(old, key) && self.spec_index(key).lock_state_u() == old.spec_index(key).lock_state_u(),
            None => self == old,
        }
    }
}

/// Everything the modeled interleaving at a kernel-step boundary preserves about
/// the kernel state and this thread's `LocalContext`: the invariant, the lock
/// phase flip to `Acquire`, every held object and its lock id, the TLB facts for
/// held page tables, and the read-only data of every container and process.
/// `LocalContext` is thread-local, so its identity and exact held-lock set stay put.
/// `KernelK::kernel_step_boundary_raw` guarantees it; the `kernel_step_boundary_*`
/// wrappers re-export it unchanged.
pub open spec fn kernel_step_boundary_preserved(pre: &KernelK, post: &KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext) -> bool {
    &&& post_lctx.cpu_id() == pre_lctx.cpu_id()
    &&& index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> {
        &&& post.cpu_arr.spec_index(pre_lctx.cpu_id()).view().view().view().current_cr3 == pre.cpu_arr.spec_index(pre_lctx.cpu_id()).view().view().view().current_cr3
        &&& post.cpu_arr.spec_index(pre_lctx.cpu_id()).view().view().view().current_pcid == pre.cpu_arr.spec_index(pre_lctx.cpu_id()).view().view().view().current_pcid
        &&& post.cpu_published[pre_lctx.cpu_id() as int].view() == pre.cpu_published[pre_lctx.cpu_id() as int].view()
    }
    &&& post.inv()
    &&& post_lctx.kernel_view_locking_state() is Acquire
    &&& post_lctx.thread_id() == pre_lctx.thread_id()
    &&& typed_lock_maps_unchanged(pre_lctx, post_lctx)
    &&& forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pt, post.pt_mp.spec_index(pt).view())]
            pre_lctx.pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(pre.cpu_tlb, pre.cpu_arr, pre.pcid_needflush, pt, pre.pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pt, post.pt_mp.spec_index(pt).view())
    &&& forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
            #![trigger pre_lctx.pagetable_lock_map().dom().contains(pagetable_ptr), post.cpu_tlb.spec_index((cpu_id, pcid))]
            pre_lctx.pagetable_lock_map().dom().contains(pagetable_ptr)
            && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
            ==> {
                let before = pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                let after = post.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                    || single_cpu_single_pcid_tlb_subset_of_present_pagetable(pre.cpu_tlb.spec_index((cpu_id, pcid)), pre.pt_mp.spec_index(pagetable_ptr).view())
                    || (pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                        && pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                        && (!post.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || post.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(post.cpu_tlb.spec_index((cpu_id, pcid)), post.pt_mp.spec_index(pagetable_ptr).view())
            }
    &&& forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger pre_lctx.pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
            pre_lctx.pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
            ==> post.pcid_needflush.spec_index(cpu_id, pcid) == pre.pcid_needflush.spec_index(cpu_id, pcid)
    &&& pre_lctx.holds_no_allocator_locks(PageSize::SZ4k) ==> post_lctx.holds_no_allocator_locks(PageSize::SZ4k)
    &&& pre_lctx.holds_no_allocator_locks(PageSize::SZ2m) ==> post_lctx.holds_no_allocator_locks(PageSize::SZ2m)
    &&& pre_lctx.holds_no_allocator_locks(PageSize::SZ1g) ==> post_lctx.holds_no_allocator_locks(PageSize::SZ1g)
    &&& forall|major: LockMajorId|
            #![trigger pre_lctx.held_lock_majors_lt(major)]
            pre_lctx.held_lock_majors_lt(major) ==> post_lctx.held_lock_majors_lt(major)
    // Direct typed-map framing for owner objects.
    &&& forall|cpu_id: CpuId|
            #![trigger pre_lctx.cpu_lock_map().dom().contains(cpu_id)]
            pre_lctx.cpu_lock_map().dom().contains(cpu_id)
            ==> post.cpu_arr.spec_index(cpu_id).view() == pre.cpu_arr.spec_index(cpu_id).view()
    &&& forall|container_ptr: RwLockContainerPtr|
            #![trigger pre_lctx.container_lock_map().dom().contains(container_ptr)]
            pre_lctx.container_lock_map().dom().contains(container_ptr)
            ==> {
                &&& post.ctn_mp.dom().contains(container_ptr)
                &&& post.ctn_mp.lock_id_by_key(container_ptr) == pre.ctn_mp.lock_id_by_key(container_ptr)
                &&& post.ctn_mp.spec_index(container_ptr) == pre.ctn_mp.spec_index(container_ptr)
            }
    &&& forall|process_ptr: RwLockProcessPtr|
            #![trigger pre_lctx.process_lock_map().dom().contains(process_ptr)]
            pre_lctx.process_lock_map().dom().contains(process_ptr)
            ==> {
                &&& post.prc_mp.dom().contains(process_ptr)
                &&& post.prc_mp.lock_id_by_key(process_ptr) == pre.prc_mp.lock_id_by_key(process_ptr)
                &&& post.prc_mp.spec_index(process_ptr) == pre.prc_mp.spec_index(process_ptr)
            }
    &&& forall|thread_ptr: RwLockThreadPtr|
            #![trigger pre_lctx.thread_lock_map().dom().contains(thread_ptr)]
            pre_lctx.thread_lock_map().dom().contains(thread_ptr)
            ==> {
                &&& post.thr_mp.dom().contains(thread_ptr)
                &&& post.thr_mp.lock_id_by_key(thread_ptr) == pre.thr_mp.lock_id_by_key(thread_ptr)
                &&& post.thr_mp.spec_index(thread_ptr) == pre.thr_mp.spec_index(thread_ptr)
            }
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
            #![trigger pre_lctx.pagetable_lock_map().dom().contains(pagetable_ptr)]
            pre_lctx.pagetable_lock_map().dom().contains(pagetable_ptr)
            ==> {
                &&& post.pt_mp.dom().contains(pagetable_ptr)
                &&& post.pt_mp.lock_id_by_key(pagetable_ptr) == pre.pt_mp.lock_id_by_key(pagetable_ptr)
                &&& post.pt_mp.spec_index(pagetable_ptr) == pre.pt_mp.spec_index(pagetable_ptr)
            }
    &&& typed_lock_maps_aligned(post, post_lctx)
    &&& post.dflt_pt == pre.dflt_pt
    &&& containers_rodata_unchanged(pre.ctn_mp, post.ctn_mp)
    &&& processes_rodata_unchanged(pre.prc_mp, post.prc_mp)
    &&& held_containers_unchanged(pre.ctn_mp, post.ctn_mp, pre_lctx)
    &&& held_processes_unchanged(pre.prc_mp, post.prc_mp, pre_lctx)
    &&& held_threads_unchanged(pre.thr_mp, post.thr_mp, pre_lctx)
    &&& held_endpoints_unchanged(pre.ep_mp, post.ep_mp, pre_lctx)
    &&& held_schedulers_unchanged(pre.sched_mp, post.sched_mp, pre_lctx)
    &&& held_pcid_allocators_unchanged(pre.pcid_allc_mp, post.pcid_allc_mp, pre_lctx)
    &&& held_cpu_sets_unchanged(pre.cpu_set_mp, post.cpu_set_mp, pre_lctx)
    &&& held_pagetables_unchanged(pre.pt_mp, post.pt_mp, pre_lctx)
    &&& held_iommu_tables_unchanged(pre.it_mp, post.it_mp, pre_lctx)
    &&& held_pages_unchanged(pre.pg_arr, post.pg_arr, pre_lctx)
    &&& held_cpus_unchanged(pre.cpu_arr, post.cpu_arr, pre_lctx)
    &&& held_allocator_objects_unchanged(pre.allc_4k_mp, post.allc_4k_mp, pre_lctx, PageSize::SZ4k)
    &&& held_allocator_objects_unchanged(pre.allc_2m_mp, post.allc_2m_mp, pre_lctx, PageSize::SZ2m)
    &&& held_allocator_objects_unchanged(pre.allc_1g_mp, post.allc_1g_mp, pre_lctx, PageSize::SZ1g)
}

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

pub open spec fn held_cpu_sets_unchanged(
    pre: CpuSetLockedMap,
    post: CpuSetLockedMap,
    lctx: &LocalContext,
) -> bool {
    forall|p: RwLockCpuSetPtr|
        #![trigger lctx.cpu_set_lock_map().dom().contains(p)]
        #![trigger pre.spec_index(p)]
        #![trigger post.spec_index(p)]
        lctx.cpu_set_lock_map().dom().contains(p) ==> {
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

pub proof fn held_pages_unchanged_except_for_changed_set(
    pre: PageLockedArray,
    post: PageLockedArray,
    lctx: &LocalContext,
    changed: Set<PageIndex>,
)
    requires
        pre.typed_lock_map_aligned(
            lctx.page_lock_map(), lctx.thread_id(),
        ),
        forall|index: PageIndex|
            #![trigger post.spec_index(index)]
            #![trigger pre.spec_index(index)]
            index_valid(NUM_PAGES, index) && !changed.contains(index)
            ==> post.spec_index(index) == pre.spec_index(index),
    ensures
        held_pages_unchanged_except(pre, post, lctx, changed),
{
    reveal(LockedArray::typed_lock_map_aligned);
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
        held_cpu_sets_unchanged(k.cpu_set_mp, k.cpu_set_mp, lctx),
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

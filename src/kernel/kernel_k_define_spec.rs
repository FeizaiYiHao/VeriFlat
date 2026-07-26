use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {

    pub const KERNEL_DEFAULT_PCID:Pcid = 0;

    pub type PageTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>;
    pub type IommuTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<IOMMU_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>;
    pub type PageLockedArray = LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>;
    pub type CpuLockedArray = LockedArray<Cpu, (), (), (), NUM_CPUS, CPU_HAS_KILL_STATE>;
    pub type ContainerLockedMap = LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>;
    pub type SchedulerLockedMap = LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>;
    pub type EndpointLockedMap = LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>;
    pub type PageAllocatorUnLockedMap = UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>;
    pub type ProcessLockedMap = LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>;
    pub type ThreadLockedMap = LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>;

    pub struct KernelK{
        pub pagetable_map: PageTableLockedMap,
        pub iommutable_map: IommuTableLockedMap,
        pub page_array: PageLockedArray,
        pub cpu_array: CpuLockedArray,
        pub container_map: ContainerLockedMap,
        pub scheduler_map: SchedulerLockedMap,
        pub process_map: ProcessLockedMap,
        pub thread_map: ThreadLockedMap,
        pub endpoint_map: EndpointLockedMap,
        pub allocator_4k_map: PageAllocatorUnLockedMap,
        pub allocator_2m_map: PageAllocatorUnLockedMap,
        pub allocator_1g_map: PageAllocatorUnLockedMap,
        pub cpu_tlb: CpuTLB,

        pub root_container: RwLockContainerPtr, // Never dies

        // pub number_containers: RwLock<NumContainers, (), (), NO_KILL_STATE>,

        // pub container_to_pagetable_map: Ghost<Map<RwLockContainerPtr, Set<RwLockPageTableRoot>>>,

        pub default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>, // Read only
    }

    impl KernelK{
        /// all spec functions under this are open
        pub open spec fn subsystems_inv(&self) -> bool {
            &&&
            self.default_pagetable_wf()
            &&&
            pagetable_perms_wf(self.pagetable_map)
            &&&
            page_array_wf(self.page_array)
            &&&
            cpu_array_wf(self.cpu_array, self.default_pagetable.view())
            &&&
            self.cpu_tlb.inv()
            &&&
            container_perms_wf(self.container_map)
            &&&
            process_perms_wf(self.process_map)
            &&&
            thread_perms_wf(self.thread_map)
            &&&
            scheduler_perms_wf(self.scheduler_map)
            &&&
            allocator_perms_wf(self.allocator_4k_map)
            &&&
            allocator_perms_wf(self.allocator_2m_map)
            &&&
            allocator_perms_wf(self.allocator_1g_map)
        }

        pub open spec fn memory_management_inv(&self) -> bool {
            &&&
            allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)
            &&&
            container_page_owner_wf(self.container_map, self.page_array)
            &&&
            hugepage_2m_wf(self.page_array)
            &&&
            hugepage_1g_wf(self.page_array)
            &&&
            page_pagetable_wf(self.pagetable_map, self.page_array)
            &&&
            container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)
            &&&
            container_pages_wf(self.page_array, self.container_map)
            &&&
            process_pages_wf(self.page_array, self.process_map)
            &&&
            pagetable_pages_wf(self.pagetable_map, self.page_array)     
            &&&
            thread_pages_wf(self.thread_map, self.page_array)
            &&&
            process_staged_pages_wf(self.process_map, self.page_array)
            &&&
            endpoint_pages_wf(self.endpoint_map, self.page_array)
            &&&
            process_pagetable_match(self.process_map, self.pagetable_map)
            &&&
            self.allocator_free_pages_wf()
            &&&
            container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map) 
            &&&
            container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)
            &&&
            container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)
            &&&
            container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)
            &&&
            container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)
        }

        pub open spec fn process_management_inv(&self) -> bool {
            &&&
            container_tree_wf(self.root_container, self.container_map)    
            &&&
            container_process_wf(self.container_map, self.process_map)
            &&&
            per_container_process_tree_wf(self.container_map, self.process_map)
            &&&
            container_endpoint_wf(self.container_map, self.endpoint_map)
            &&&
            container_cpu_wf(self.container_map, self.cpu_array)
            &&&
            thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)
            &&&
            thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)
            &&&
            container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)
            &&&
            container_scheduler_wf(self.container_map, self.scheduler_map)
            &&&
            container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)
            &&&
            container_thread_wf(self.container_map, self.thread_map)
            &&&
            process_cpu_wf(self.process_map, self.cpu_array)
            &&&
            process_thread_wf(self.process_map, self.thread_map)
            &&&
            thread_cpu_wf(self.thread_map, self.cpu_array)
        }
        /// All spec functions under this are closed
        pub open spec fn inv(&self) -> bool {
            &&&
            self.subsystems_inv()
            &&&
            self.memory_management_inv()
            &&&
            self.process_management_inv()
            // TLB spec
            &&&
            cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)
            &&&
            tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)
        }

        #[verifier::opaque]
        pub open spec fn default_pagetable_wf(&self) -> bool {
            &&&
            self.default_pagetable.view().inv()
            &&&
            self.default_pagetable.view().pcid_or_ioid() == KERNEL_DEFAULT_PCID
            &&&
            self.default_pagetable.view().is_empty()
        }

        pub open spec fn allocator_free_pages_wf(&self) -> bool{
            &&&
            allocator_free_page_ptrs_wf(self.allocator_4k_map)
            &&&
            allocator_free_page_ptrs_wf(self.allocator_2m_map)
            &&&
            allocator_free_page_ptrs_wf(self.allocator_1g_map)
        }

        // pub open spec fn allocator_cpu_cache_clean(&self) -> bool{
        //     &&&
        //     forall|alloc_ptr: RwLockPageAllocatorPtr|
        //         #![trigger self.allocator_4k_map.spec_index(alloc_ptr).local_quota_clean()]
        //         self.allocator_4k_map.dom().contains(alloc_ptr)
        //         ==>
        //         self.allocator_4k_map.spec_index(alloc_ptr).local_quota_clean()
        //     &&&
        //     forall|alloc_ptr: RwLockPageAllocatorPtr|
        //         #![trigger self.allocator_2m_map.spec_index(alloc_ptr).local_quota_clean()]
        //         self.allocator_2m_map.dom().contains(alloc_ptr)
        //         ==>
        //         self.allocator_2m_map.spec_index(alloc_ptr).local_quota_clean()
        //     &&&
        //     forall|alloc_ptr: RwLockPageAllocatorPtr|
        //         #![trigger self.allocator_1g_map.spec_index(alloc_ptr).local_quota_clean()]
        //         self.allocator_1g_map.dom().contains(alloc_ptr)
        //         ==>
        //         self.allocator_1g_map.spec_index(alloc_ptr).local_quota_clean()
        // }

        // ============================================================
        //   Lock-map / kernel-state agreement
        // ============================================================
        //
        // For each `KernelObjId` recorded in `lctx.lock_map`, the
        // corresponding kernel object is currently locked, exists in its
        // map/array, and its lock-id matches what `lctx.lock_map` says.
        // Bidirectional: any locked object held by this thread must be
        // recorded in `lctx.lock_map`. This is the "no stealth locks" rule.

        /// Bidirectional agreement: kernel locks and `lctx.lock_map` are
        /// exact mirrors of each other ("no stealth locks", and every lock-map
        /// entry is a real held lock with matching id). Used as a precondition
        /// for the kernel-view linearization point.
        ///
        /// ANDs the per-object-kind bidirectional opaque pieces defined above
        /// the impl block. A consumer re-establishing this after touching one
        /// map reveals only that map's piece (e.g. `page_locked_match_lctx`),
        /// not all ~20 quantifiers.
        pub open spec fn locked_objects_match_lctx(&self, lctx: &LocalContext) -> bool {
            &&& container_locked_match_lctx(self.container_map, lctx)
            &&& process_locked_match_lctx(self.process_map, lctx)
            &&& thread_locked_match_lctx(self.thread_map, lctx)
            &&& endpoint_locked_match_lctx(self.endpoint_map, lctx)
            &&& scheduler_locked_match_lctx(self.scheduler_map, lctx)
            &&& pagetable_locked_match_lctx(self.pagetable_map, lctx)
            &&& page_locked_match_lctx(self.page_array, lctx)
            &&& cpu_locked_match_lctx(self.cpu_array, lctx)
            &&& allocator_locked_match_lctx(self.allocator_4k_map, PageSize::SZ4k, lctx)
            &&& allocator_locked_match_lctx(self.allocator_2m_map, PageSize::SZ2m, lctx)
            &&& allocator_locked_match_lctx(self.allocator_1g_map, PageSize::SZ1g, lctx)
        }

        /// Trusted kernel-view step boundary.
        ///
        /// Models "end the current kernel-view atomic section and begin a
        /// new one." Between sections, the rest of the world may run
        /// arbitrary atomic sections:
        ///   - all our held objects (those recorded in `lctx.lock_map`) keep
        ///     their state across the boundary — `view`, `view_kernel_ghost`,
        ///     `view_user_ghost`, `view_rodata`, `locking_thread`,
        ///     `being_killed` are preserved per held lock instance;
        ///   - everything else may change arbitrarily, including map
        ///     domains (except for the fixed-size arrays `cpu_array` and
        ///     `page_array`);
        ///   - `lctx.lock_map` itself is unchanged (we still hold what we
        ///     held);
        ///   - the kernel invariant `inv()` is re-established by trust;
        ///   - kernel-view phase flips back to `Acquire`, ready for the
        ///     next atomic section.
        ///
        /// Snapshot discipline: the boundary requires
        /// `kernel_k_to_kernel_u(*old(self)) == old(steps).snap_shot`,
        /// i.e. since the last refresh point (syscall entry, end of last
        /// user-step, or end of last boundary) this thread hasn't changed
        /// the user-view projection. Any U-mutation outside a
        /// begin/end_user_view_step pair leaves the snapshot stale and is
        /// caught here. After interleaving, the boundary refreshes
        /// `snap_shot` to the new projection.
        ///
        /// Preconditions:
        ///   - `inv()` holds (we entered the boundary in a wf state),
        ///   - `kernel_view_locking_state is Release` (the current section
        ///     is done),
        ///   - `locked_objects_match_lctx(lctx)` (no stealth locks, every
        ///     `lctx.lock_map` entry corresponds to a real held lock),
        ///   - `kernel_k_to_kernel_u(*self) == steps.snap_shot` (no
        ///     unrecorded U-mutation since the last refresh point).
        #[verifier::external_body]
        pub proof fn kernel_step_boundary(
            tracked &mut self,
            tracked lctx: &mut LocalContext,
            tracked steps: &mut KernelSteps,
        )
            requires
                old(self).inv(),
                old(lctx).kernel_view_locking_state() is Release,
                old(self).locked_objects_match_lctx(old(lctx)),
                kernel_k_to_kernel_u(*old(self)) == old(steps).snap_shot,
            ensures
                final(self).inv(),
                // LocalContext: phase flips to Acquire; everything else preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                // lock_map fully preserved (held objects' lock states unchanged).
                final(lctx).lock_map() == old(lctx).lock_map(),
                final(lctx).kernel_view_locking_state() is Acquire,
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                // KernelSteps: ledger of recorded steps unchanged; snapshot
                // refreshed to the new (post-interleaving) projection.
                final(steps).steps == old(steps).steps,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                // Kernel still in agreement with lctx.
                final(self).locked_objects_match_lctx(final(lctx)),
                // Read-only data unchanged at the kernel level.
                final(self).root_container == old(self).root_container,
                final(self).default_pagetable == old(self).default_pagetable,
                // Per-subsystem preservation: rodata of surviving objects +
                // full state of every held object.
                boundary_containers_preserved(old(self), final(self), old(lctx)),
                boundary_processes_preserved(old(self), final(self), old(lctx)),
                boundary_threads_preserved(old(self), final(self), old(lctx)),
                boundary_endpoints_preserved(old(self), final(self), old(lctx)),
                boundary_schedulers_preserved(old(self), final(self), old(lctx)),
                boundary_pagetables_preserved(old(self), final(self), old(lctx)),
                boundary_pages_preserved(old(self), final(self), old(lctx)),
                boundary_cpus_preserved(old(self), final(self), old(lctx)),
                boundary_allocators_preserved(old(self), final(self), old(lctx)),
        {
            unimplemented!()
        }
    }

    #[verifier::opaque]
    pub open spec fn container_locked_match_lctx(
        container_map: ContainerLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        // forward
        &&& (forall|c: RwLockContainerPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Container(c))]
            lctx.lock_map().dom().contains(KernelObjId::Container(c))
            ==>
            container_map.dom().contains(c)
            && container_map[c].locked_by(lctx)
            && container_map[c].locking_thread() is Write
            && container_map[c].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Container(c)])
        // reverse
        &&& (forall|c: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c)]
            container_map.dom().contains(c) && container_map[c].locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Container(c)))
    }

    #[verifier::opaque]
    pub open spec fn process_locked_match_lctx(process_map: ProcessLockedMap, lctx: &LocalContext) -> bool {
        &&& (forall|p: RwLockProcessPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Process(p))]
            lctx.lock_map().dom().contains(KernelObjId::Process(p))
            ==>
            process_map.dom().contains(p)
            && process_map[p].locked_by(lctx)
            && process_map[p].locking_thread() is Write
            && process_map[p].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Process(p)])
        &&& (forall|p: RwLockProcessPtr|
            #![trigger process_map.dom().contains(p)]
            process_map.dom().contains(p) && process_map[p].locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Process(p)))
    }

    #[verifier::opaque]
    pub open spec fn thread_locked_match_lctx(thread_map: ThreadLockedMap, lctx: &LocalContext) -> bool {
        &&& (forall|t: RwLockThreadPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Thread(t))]
            lctx.lock_map().dom().contains(KernelObjId::Thread(t))
            ==>
            thread_map.dom().contains(t)
            && thread_map[t].locked_by(lctx)
            && thread_map[t].locking_thread() is Write
            && thread_map[t].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Thread(t)])
        &&& (forall|t: RwLockThreadPtr|
            #![trigger thread_map.dom().contains(t)]
            thread_map.dom().contains(t) && thread_map[t].locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Thread(t)))
    }

    #[verifier::opaque]
    pub open spec fn endpoint_locked_match_lctx(
        endpoint_map: EndpointLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))]
            lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))
            ==>
            endpoint_map.dom().contains(e)
            && endpoint_map[e].locked_by(lctx)
            && endpoint_map[e].locking_thread() is Write
            && endpoint_map[e].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Endpoint(e)])
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger endpoint_map.dom().contains(e)]
            endpoint_map.dom().contains(e) && endpoint_map[e].locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Endpoint(e)))
    }

    #[verifier::opaque]
    pub open spec fn scheduler_locked_match_lctx(
        scheduler_map: SchedulerLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))]
            lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
            ==>
            scheduler_map.dom().contains(s)
            && scheduler_map[s].locked_by(lctx)
            && scheduler_map[s].locking_thread() is Write
            && scheduler_map[s].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Scheduler(s)])
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger scheduler_map.dom().contains(s)]
            scheduler_map.dom().contains(s) && scheduler_map[s].locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Scheduler(s)))
    }

    #[verifier::opaque]
    pub open spec fn pagetable_locked_match_lctx(
        pagetable_map: PageTableLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))]
            lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))
            ==>
            pagetable_map.dom().contains(pt)
            && pagetable_map[pt].locked_by(lctx)
            && pagetable_map[pt].locking_thread() is Write
            && pagetable_map[pt].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::PageTable(pt)])
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt)]
            pagetable_map.dom().contains(pt) && pagetable_map[pt].locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::PageTable(pt)))
    }

    #[verifier::opaque]
    pub open spec fn page_locked_match_lctx(
        page_array: PageLockedArray,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|i: PageIndex|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Page(i))]
            #![trigger page_array[i]]
            lctx.lock_map().dom().contains(KernelObjId::Page(i))
            ==>
            page_index_wf(i)
            && page_array[i]@.locked_by(lctx)
            && page_array[i]@.locking_thread() is Write
            && page_array[i]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Page(i)]
            && page_array[i]@.locking_thread()->Write_lock_id.container == LockOwnerId::None
            && page_array[i]@.locking_thread()->Write_lock_id.process == LockOwnerId::None
            && page_array[i]@.locking_thread()->Write_lock_id.minor == i
            && {
                let mj = page_array[i]@.locking_thread()->Write_lock_id.major;
                ||| mj == FREE_PAGE_LOCK_MAJOR
                ||| mj == MAPPED_PAGE_LOCK_MAJOR
                ||| mj == MERGED_PAGE_LOCK_MAJOR
                ||| mj == ALLOCATED_PAGE_MAJOR
            })
        &&& (forall|i: PageIndex|
            #![trigger page_array[i]@.locked_by(lctx)]
            #![trigger page_array[i]]
            page_index_wf(i) && page_array[i]@.locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Page(i)))
    }

    #[verifier::opaque]
    pub open spec fn cpu_locked_match_lctx(
        cpu_array: CpuLockedArray,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|c: CpuId|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Cpu(c))]
            #![trigger cpu_array[c]]
            lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
            ==>
            cpu_id_valid(c)
            && cpu_array[c]@.locked_by(lctx)
            && cpu_array[c]@.locking_thread() is Write
            && cpu_array[c]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Cpu(c)])
        &&& (forall|c: CpuId|
            #![trigger cpu_array[c]@.locked_by(lctx)]
            #![trigger cpu_array[c]]
            cpu_id_valid(c) && cpu_array[c]@.locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Cpu(c)))
    }

    /// Bidirectional agreement for one allocator map, tagged by its `PageSize`.
    #[verifier::opaque]
    pub open spec fn allocator_locked_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        sz: PageSize,
        lctx: &LocalContext,
    ) -> bool {
        // forward: quota / cache / global_pool
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))]
            #![trigger alloc_map.spec_index(p)]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.locked_by(lctx)
            && alloc_map[p].quota.locking_thread() is Write
            && alloc_map[p].quota.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorQuota(sz, p)])
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))]
            #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c]@.locked_by(lctx)
            && alloc_map[p].cpu_caches[c]@.locking_thread() is Write
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorCache(sz, p, c)]
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.container == LockOwnerId::NotApp
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.process == LockOwnerId::NotApp
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.minor == c
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.major == ALLOCATOR_CACHE_MAJOR)
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))]
            #![trigger alloc_map.spec_index(p)]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_pool.locked_by(lctx)
            && alloc_map[p].global_pool.locking_thread() is Write
            && alloc_map[p].global_pool.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorGlobalPoll(sz, p)])
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.dom().contains(p)]
            #![trigger alloc_map.spec_index(p)]
            alloc_map.dom().contains(p)
            ==>
            {
                &&& alloc_map[p].quota.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
                &&& alloc_map[p].global_pool.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
                &&& forall|c: CpuId|
                    #![trigger alloc_map[p].cpu_caches[c]@.locked_by(lctx)]
                    #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
                    cpu_id_valid(c) && alloc_map[p].cpu_caches[c]@.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
            })
    }

    // ================================================================
    // Boundary preservation predicates, grouped by kernel subsystem.
    // Each relates the pre-boundary kernel `pre` to the post-boundary
    // kernel `post`: rodata of surviving objects is immutable, and any
    // object held in `lctx.lock_map` (or write-locked by `lctx`) is
    // preserved in its entirety.
    // ================================================================

    pub open spec fn boundary_containers_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.container_map.dom().contains(c)]
            #![trigger post.container_map.dom().contains(c)]
            pre.container_map.dom().contains(c) && post.container_map.dom().contains(c)
            ==> post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata()
        &&& forall|c: RwLockContainerPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Container(c))]
            #![trigger pre.container_map.spec_index(c).locked_by(lctx)]
            #![trigger pre.container_map.dom().contains(c)]
            #![trigger post.container_map.dom().contains(c)]
            (lctx.lock_map().dom().contains(KernelObjId::Container(c))
                || (pre.container_map.dom().contains(c) && pre.container_map.spec_index(c).locked_by(lctx)))
            ==> post.container_map.dom().contains(c) && post.container_map[c] == pre.container_map[c]
    }

    pub open spec fn boundary_processes_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        &&& forall|p: RwLockProcessPtr|
            #![trigger pre.process_map.dom().contains(p)]
            #![trigger post.process_map.dom().contains(p)]
            pre.process_map.dom().contains(p) && post.process_map.dom().contains(p)
            ==> post.process_map.spec_index(p).view_rodata() == pre.process_map.spec_index(p).view_rodata()
        &&& forall|p: RwLockProcessPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Process(p))]
            #![trigger pre.process_map.spec_index(p).locked_by(lctx)]
            #![trigger pre.process_map.dom().contains(p)]
            #![trigger post.process_map.dom().contains(p)]
            (lctx.lock_map().dom().contains(KernelObjId::Process(p))
                || (pre.process_map.dom().contains(p) && pre.process_map.spec_index(p).locked_by(lctx)))
            ==> post.process_map.dom().contains(p) && post.process_map[p] == pre.process_map[p]
    }

    pub open spec fn boundary_threads_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|t: RwLockThreadPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Thread(t))]
            #![trigger pre.thread_map.spec_index(t).locked_by(lctx)]
            #![trigger pre.thread_map.dom().contains(t)]
            #![trigger post.thread_map.dom().contains(t)]
            (lctx.lock_map().dom().contains(KernelObjId::Thread(t))
                || (pre.thread_map.dom().contains(t) && pre.thread_map.spec_index(t).locked_by(lctx)))
            ==> post.thread_map.dom().contains(t) && post.thread_map[t] == pre.thread_map[t]
    }

    pub open spec fn boundary_endpoints_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|e: RwLockEndpointPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))]
            #![trigger pre.endpoint_map.spec_index(e).locked_by(lctx)]
            #![trigger pre.endpoint_map.dom().contains(e)]
            #![trigger post.endpoint_map.dom().contains(e)]
            (lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))
                || (pre.endpoint_map.dom().contains(e) && pre.endpoint_map.spec_index(e).locked_by(lctx)))
            ==> post.endpoint_map.dom().contains(e) && post.endpoint_map[e] == pre.endpoint_map[e]
    }

    pub open spec fn boundary_schedulers_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|s: RwLockSchedulerPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))]
            #![trigger pre.scheduler_map.spec_index(s).locked_by(lctx)]
            #![trigger pre.scheduler_map.dom().contains(s)]
            #![trigger post.scheduler_map.dom().contains(s)]
            #![trigger post.scheduler_map.spec_index(s)]
            (lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                || (pre.scheduler_map.dom().contains(s) && pre.scheduler_map.spec_index(s).locked_by(lctx)))
            ==> post.scheduler_map.dom().contains(s) && post.scheduler_map[s] == pre.scheduler_map[s]
    }

    pub open spec fn boundary_pagetables_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|pt: RwLockPageTableRoot|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))]
            #![trigger pre.pagetable_map.spec_index(pt).locked_by(lctx)]
            #![trigger pre.pagetable_map.dom().contains(pt)]
            #![trigger post.pagetable_map.dom().contains(pt)]
            (lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))
                || (pre.pagetable_map.dom().contains(pt) && pre.pagetable_map.spec_index(pt).locked_by(lctx)))
            ==> post.pagetable_map.dom().contains(pt) && post.pagetable_map[pt] == pre.pagetable_map[pt]
    }

    pub open spec fn boundary_pages_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|i: PageIndex|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Page(i))]
            #![trigger pre.page_array[i]@.locked_by(lctx)]
            (page_index_wf(i) && lctx.lock_map().dom().contains(KernelObjId::Page(i)))
                || (page_index_wf(i) && pre.page_array[i]@.locked_by(lctx))
            ==> post.page_array[i]@ == pre.page_array[i]@
    }

    pub open spec fn boundary_cpus_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|c: CpuId|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Cpu(c))]
            #![trigger pre.cpu_array[c]@.locked_by(lctx)]
            #![trigger post.cpu_array[c]@]
            (cpu_id_valid(c) && lctx.lock_map().dom().contains(KernelObjId::Cpu(c)))
                || (cpu_id_valid(c) && pre.cpu_array[c]@.locked_by(lctx))
            ==> post.cpu_array[c]@ == pre.cpu_array[c]@
    }

    pub open spec fn boundary_allocators_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        &&& forall|sz: PageSize, p: RwLockPageAllocatorPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
            ==> {
                let old_m = match sz {
                    PageSize::SZ4k => pre.allocator_4k_map,
                    PageSize::SZ2m => pre.allocator_2m_map,
                    PageSize::SZ1g => pre.allocator_1g_map,
                };
                let new_m = match sz {
                    PageSize::SZ4k => post.allocator_4k_map,
                    PageSize::SZ2m => post.allocator_2m_map,
                    PageSize::SZ1g => post.allocator_1g_map,
                };
                new_m.dom().contains(p) && new_m[p].quota == old_m[p].quota
            }
        &&& forall|sz: PageSize, p: RwLockPageAllocatorPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
            ==> {
                let old_m = match sz {
                    PageSize::SZ4k => pre.allocator_4k_map,
                    PageSize::SZ2m => pre.allocator_2m_map,
                    PageSize::SZ1g => pre.allocator_1g_map,
                };
                let new_m = match sz {
                    PageSize::SZ4k => post.allocator_4k_map,
                    PageSize::SZ2m => post.allocator_2m_map,
                    PageSize::SZ1g => post.allocator_1g_map,
                };
                new_m.dom().contains(p) && new_m[p].global_pool == old_m[p].global_pool
            }
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger pre.allocator_4k_map.spec_index(p).global_pool.locked_by(lctx)]
            pre.allocator_4k_map.dom().contains(p) && pre.allocator_4k_map.spec_index(p).global_pool.locked_by(lctx)
            ==> post.allocator_4k_map.dom().contains(p)
                && post.allocator_4k_map.spec_index(p).global_pool == pre.allocator_4k_map.spec_index(p).global_pool
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger pre.allocator_2m_map.spec_index(p).global_pool.locked_by(lctx)]
            pre.allocator_2m_map.dom().contains(p) && pre.allocator_2m_map.spec_index(p).global_pool.locked_by(lctx)
            ==> post.allocator_2m_map.dom().contains(p)
                && post.allocator_2m_map.spec_index(p).global_pool == pre.allocator_2m_map.spec_index(p).global_pool
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger pre.allocator_1g_map.spec_index(p).global_pool.locked_by(lctx)]
            pre.allocator_1g_map.dom().contains(p) && pre.allocator_1g_map.spec_index(p).global_pool.locked_by(lctx)
            ==> post.allocator_1g_map.dom().contains(p)
                && post.allocator_1g_map.spec_index(p).global_pool == pre.allocator_1g_map.spec_index(p).global_pool
        &&& forall|sz: PageSize, p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
            ==> {
                let old_m = match sz {
                    PageSize::SZ4k => pre.allocator_4k_map,
                    PageSize::SZ2m => pre.allocator_2m_map,
                    PageSize::SZ1g => pre.allocator_1g_map,
                };
                let new_m = match sz {
                    PageSize::SZ4k => post.allocator_4k_map,
                    PageSize::SZ2m => post.allocator_2m_map,
                    PageSize::SZ1g => post.allocator_1g_map,
                };
                new_m.dom().contains(p) && cpu_id_valid(c) && new_m[p].cpu_caches[c]@ == old_m[p].cpu_caches[c]@
            }
        &&& forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger pre.allocator_4k_map.spec_index(p).cpu_caches[c]@.locked_by(lctx)]
            pre.allocator_4k_map.dom().contains(p) && cpu_id_valid(c)
                && pre.allocator_4k_map.spec_index(p).cpu_caches[c]@.locked_by(lctx)
            ==> post.allocator_4k_map.dom().contains(p)
                && post.allocator_4k_map.spec_index(p).cpu_caches[c]@ == pre.allocator_4k_map.spec_index(p).cpu_caches[c]@
        &&& forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger pre.allocator_2m_map.spec_index(p).cpu_caches[c]@.locked_by(lctx)]
            pre.allocator_2m_map.dom().contains(p) && cpu_id_valid(c)
                && pre.allocator_2m_map.spec_index(p).cpu_caches[c]@.locked_by(lctx)
            ==> post.allocator_2m_map.dom().contains(p)
                && post.allocator_2m_map.spec_index(p).cpu_caches[c]@ == pre.allocator_2m_map.spec_index(p).cpu_caches[c]@
        &&& forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger pre.allocator_1g_map.spec_index(p).cpu_caches[c]@.locked_by(lctx)]
            pre.allocator_1g_map.dom().contains(p) && cpu_id_valid(c)
                && pre.allocator_1g_map.spec_index(p).cpu_caches[c]@.locked_by(lctx)
            ==> post.allocator_1g_map.dom().contains(p)
                && post.allocator_1g_map.spec_index(p).cpu_caches[c]@ == pre.allocator_1g_map.spec_index(p).cpu_caches[c]@
    }

}
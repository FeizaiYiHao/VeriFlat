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
        // For each key recorded in the corresponding per-KernelK-layout map
        // in `lctx`, the kernel object is currently locked, exists in its
        // map/array, and its lock-id matches the recorded dynamic id.
        // Bidirectional: any locked object held by this thread must be
        // recorded in its corresponding LocalContext map. This is the "no
        // stealth locks" rule.

        /// Bidirectional agreement: kernel locks and the per-type maps in
        /// `lctx` are exact mirrors ("no stealth locks", and every lock-map
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

        /// Change the dynamic lock id recorded for a still-held object after a
        /// Release-phase payload transition. The lock permission's token and
        /// the RwLock's write-token remain unchanged.
        pub proof fn update_lock_id_preserving_locked_match(
            &self,
            tracked lctx: &mut LocalContext,
            obj_id: KernelObjId,
            new_lock_id: LockId,
        )
            requires
                old(lctx).kernel_view_locking_state() is Release,
                old(lctx).lock_map_contains(obj_id),
                self.locked_objects_match_lctx(old(lctx)),
            ensures
                final(lctx).lock_maps_inserted(old(lctx), obj_id, new_lock_id),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                self.locked_objects_match_lctx(final(lctx)),
        {
            lctx.update_lock_id(obj_id, new_lock_id);
            reveal(KernelK::locked_objects_match_lctx);
            reveal(container_locked_match_lctx);
            reveal(process_locked_match_lctx);
            reveal(thread_locked_match_lctx);
            reveal(endpoint_locked_match_lctx);
            reveal(scheduler_locked_match_lctx);
            reveal(pagetable_locked_match_lctx);
            reveal(page_locked_match_lctx);
            reveal(cpu_locked_match_lctx);
            reveal(allocator_locked_match_lctx);
        }

        /// Trusted kernel-view step boundary.
        ///
        /// Models "end the current kernel-view atomic section and begin a
        /// new one." Between sections, the rest of the world may run
        /// arbitrary atomic sections:
        ///   - all our held objects (those recorded in the LocalContext maps) keep
        ///     their state across the boundary — `view`, `view_kernel_ghost`,
        ///     `view_user_ghost`, `view_rodata`, `locking_thread`,
        ///     `being_killed` are preserved per held lock instance;
        ///   - everything else may change arbitrarily, including map
        ///     domains (except for the fixed-size arrays `cpu_array` and
        ///     `page_array`);
        ///   - the LocalContext maps themselves are unchanged (we still hold what we
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
        ///     LocalContext entry corresponds to a real held lock),
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
                lock_id_aligned(old(self), old(lctx)),
                kernel_k_to_kernel_u(*old(self)) == old(steps).snap_shot,
            ensures
                final(self).inv(),
                // LocalContext: phase flips to Acquire; everything else preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                // Per-type maps fully preserved (held objects' lock states unchanged).
                final(lctx).lock_maps_equal(old(lctx)),
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

    // ---- Lock-id alignment specs ----
    // These check that the corresponding per-type map values equal the current, dynamic lock id of
    // the corresponding object. They are checked before every boundary.

    #[verifier::opaque]
    pub open spec fn container_lock_id_aligned(
        container_map: ContainerLockedMap,
        lctx: &LocalContext,
    ) -> bool
        recommends container_locked_match_lctx(container_map, lctx)
    {
        forall|c: RwLockContainerPtr|
            #![trigger lctx.container_lock_map()[c]]
            #![trigger lctx.container_lock_map().dom().contains(c)]
            #![trigger container_map.lock_id_by_key(c)]
            lctx.container_lock_map().dom().contains(c)
            ==>
            container_map.dom().contains(c)
            && container_map.lock_id_by_key(c) == lctx.container_lock_map()[c]
    }

    #[verifier::opaque]
    pub open spec fn process_lock_id_aligned(
        process_map: ProcessLockedMap,
        lctx: &LocalContext,
    ) -> bool
        recommends process_locked_match_lctx(process_map, lctx)
    {
        forall|p: RwLockProcessPtr|
            #![trigger lctx.process_lock_map()[p]]
            #![trigger lctx.process_lock_map().dom().contains(p)]
            #![trigger process_map.lock_id_by_key(p)]
            lctx.process_lock_map().dom().contains(p)
            ==>
            process_map.dom().contains(p)
            && process_map.lock_id_by_key(p) == lctx.process_lock_map()[p]
    }

    #[verifier::opaque]
    pub open spec fn thread_lock_id_aligned(
        thread_map: ThreadLockedMap,
        lctx: &LocalContext,
    ) -> bool
        recommends thread_locked_match_lctx(thread_map, lctx)
    {
        forall|t: RwLockThreadPtr|
            #![trigger lctx.thread_lock_map()[t]]
            #![trigger lctx.thread_lock_map().dom().contains(t)]
            #![trigger thread_map.lock_id_by_key(t)]
            lctx.thread_lock_map().dom().contains(t)
            ==>
            thread_map.dom().contains(t)
            && thread_map.lock_id_by_key(t) == lctx.thread_lock_map()[t]
    }

    #[verifier::opaque]
    pub open spec fn endpoint_lock_id_aligned(
        endpoint_map: EndpointLockedMap,
        lctx: &LocalContext,
    ) -> bool
        recommends endpoint_locked_match_lctx(endpoint_map, lctx)
    {
        forall|e: RwLockEndpointPtr|
            #![trigger lctx.endpoint_lock_map()[e]]
            #![trigger lctx.endpoint_lock_map().dom().contains(e)]
            lctx.endpoint_lock_map().dom().contains(e)
            ==>
            endpoint_map.dom().contains(e)
            && LockId{
                container: LockOwnerId::none(),
                process: LockOwnerId::none(),
                major: ENDPOINT_LOCK_MAJOR,
                minor: e,
            } == lctx.endpoint_lock_map()[e]
    }

    #[verifier::opaque]
    pub open spec fn pagetable_lock_id_aligned(
        pagetable_map: PageTableLockedMap,
        lctx: &LocalContext,
    ) -> bool
        recommends pagetable_locked_match_lctx(pagetable_map, lctx)
    {
        forall|pt: RwLockPageTableRoot|
            #![trigger lctx.pagetable_lock_map()[pt]]
            #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
            #![trigger pt.to_lock_id()]
            lctx.pagetable_lock_map().dom().contains(pt)
            ==>
            pagetable_map.dom().contains(pt)
            && pt.to_lock_id() == lctx.pagetable_lock_map()[pt]
    }

    #[verifier::opaque]
    pub open spec fn page_lock_id_aligned(
        page_array: PageLockedArray,
        lctx: &LocalContext,
    ) -> bool
        recommends page_locked_match_lctx(page_array, lctx)
    {
        forall|i: PageIndex|
            #![trigger lctx.page_lock_map()[i]]
            #![trigger lctx.page_lock_map().dom().contains(i)]
            #![trigger page_array.lock_id_by_index(i)]
            lctx.page_lock_map().dom().contains(i)
            ==>
            page_index_wf(i)
            && page_array.lock_id_by_index(i) == lctx.page_lock_map()[i]
    }

    #[verifier::opaque]
    pub open spec fn scheduler_lock_id_aligned(
        scheduler_map: SchedulerLockedMap,
        lctx: &LocalContext,
    ) -> bool
        recommends scheduler_locked_match_lctx(scheduler_map, lctx)
    {
        forall|s: RwLockSchedulerPtr|
            #![trigger lctx.scheduler_lock_map()[s]]
            #![trigger lctx.scheduler_lock_map().dom().contains(s)]
            #![trigger scheduler_map.lock_id_by_key(s)]
            lctx.scheduler_lock_map().dom().contains(s)
            ==>
            scheduler_map.dom().contains(s)
            && scheduler_map.lock_id_by_key(s) == lctx.scheduler_lock_map()[s]
    }

    #[verifier::opaque]
    pub open spec fn cpu_lock_id_aligned(
        cpu_array: CpuLockedArray,
        lctx: &LocalContext,
    ) -> bool
        recommends cpu_locked_match_lctx(cpu_array, lctx)
    {
        forall|c: CpuId|
            #![trigger lctx.cpu_lock_map()[c]]
            #![trigger lctx.cpu_lock_map().dom().contains(c)]
            #![trigger cpu_array.spec_index(c).lock_id()]
            lctx.cpu_lock_map().dom().contains(c)
            ==>
            cpu_id_valid(c)
            && cpu_array.spec_index(c).lock_id() == lctx.cpu_lock_map()[c]
    }

    #[verifier::opaque]
    pub open spec fn allocator_lock_id_aligned(
        alloc_map: PageAllocatorUnLockedMap,
        sz: PageSize,
        lctx: &LocalContext,
    ) -> bool
        recommends allocator_locked_match_lctx(alloc_map, sz, lctx)
    {
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.allocator_lock_map(sz)[AllocatorLockObjId::Quota(p)]]
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))]
            #![trigger alloc_map[p].quota.lock_id()]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.lock_id() == lctx.allocator_lock_map(sz)[AllocatorLockObjId::Quota(p)])
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lctx.allocator_lock_map(sz)[AllocatorLockObjId::Cache(p, c)]]
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))]
            #![trigger alloc_map[p].cpu_caches[c].lock_id()]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c].lock_id() == lctx.allocator_lock_map(sz)[AllocatorLockObjId::Cache(p, c)])
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.allocator_lock_map(sz)[AllocatorLockObjId::GlobalPool(p)]]
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))]
            #![trigger alloc_map[p].global_pool.lock_id()]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_pool.lock_id() == lctx.allocator_lock_map(sz)[AllocatorLockObjId::GlobalPool(p)])
    }

    /// Dynamic ordering ids agree with their currently locked objects before
    /// a boundary.  Pages are the only object family whose ordering id changes
    /// with payload state in the implemented transitions; static families are
    /// preserved by their acquire/release contracts.
    pub open spec fn lock_id_aligned(k: &KernelK, lctx: &LocalContext) -> bool {
        page_lock_id_aligned(k.page_array, lctx)
    }

    /// The currently implemented dynamic-id relation concerns pages only.
    /// This is the inexpensive entry bridge for payload-mutation wrappers
    /// reached while no page slot is held.
    pub proof fn no_held_pages_imply_lock_id_aligned(
        k: &KernelK,
        lctx: &LocalContext,
    )
        requires
            lctx.page_lock_map().dom() == Set::empty(),
        ensures
            lock_id_aligned(k, lctx),
    {
        reveal(lock_id_aligned);
        reveal(page_lock_id_aligned);
    }

    /// Preserve page lock-id alignment when a Release-phase transition changes
    /// one held page's dynamic id and refreshes exactly that lock-map entry.
    pub proof fn page_lock_id_aligned_after_refresh(
        old_pages: PageLockedArray,
        new_pages: PageLockedArray,
        old_lctx: &LocalContext,
        new_lctx: &LocalContext,
        page_index: PageIndex,
        new_lock_id: LockId,
    )
        requires
            page_index_wf(page_index),
            page_lock_id_aligned(old_pages, old_lctx),
            new_pages.unchanged_except(&old_pages, page_index),
            new_pages.lock_id_by_index(page_index) == new_lock_id,
            new_lctx.page_lock_map() =~= old_lctx.page_lock_map().insert(
                page_index, new_lock_id),
        ensures
            page_lock_id_aligned(new_pages, new_lctx),
    {
        reveal(page_lock_id_aligned);
        assert forall|i: PageIndex|
            #![trigger new_lctx.page_lock_map()[i]]
            new_lctx.page_lock_map().dom().contains(i)
            ==> page_index_wf(i)
                && new_pages.lock_id_by_index(i)
                    == new_lctx.page_lock_map()[i] by {
            if new_lctx.page_lock_map().dom().contains(i) {
                if i == page_index {
                    assert(new_lctx.page_lock_map()[i] == new_lock_id);
                } else {
                    assert(old_lctx.page_lock_map().dom().contains(i));
                    assert(new_lctx.page_lock_map()[i]
                        == old_lctx.page_lock_map()[i]);
                    assert(new_pages[i] === old_pages[i]);
                    assert(new_pages.lock_id_by_index(i) == old_pages.lock_id_by_index(i));
                }
            }
        }
    }

    /// A kernel-object mutation that does not touch the page array or the
    /// page portion of the local lock context preserves dynamic page-id
    /// alignment.  This is the common frame used by non-page lock wrappers.
    pub proof fn page_lock_id_aligned_preserved(
        old_pages: PageLockedArray,
        new_pages: PageLockedArray,
        old_lctx: &LocalContext,
        new_lctx: &LocalContext,
    )
        requires
            page_lock_id_aligned(old_pages, old_lctx),
            new_pages == old_pages,
            new_lctx.page_lock_map() == old_lctx.page_lock_map(),
        ensures
            page_lock_id_aligned(new_pages, new_lctx),
    {
        reveal(page_lock_id_aligned);
    }

    /// Releasing a page lock removes exactly one local-context entry while
    /// preserving every page payload and therefore every remaining dynamic
    /// page lock id.
    pub proof fn page_lock_id_aligned_after_remove(
        old_pages: PageLockedArray,
        new_pages: PageLockedArray,
        old_lctx: &LocalContext,
        new_lctx: &LocalContext,
        page_index: PageIndex,
    )
        requires
            page_index_wf(page_index),
            page_lock_id_aligned(old_pages, old_lctx),
            new_pages.unchanged_except(&old_pages, page_index),
            new_pages.lock_id_by_index(page_index)
                == old_pages.lock_id_by_index(page_index),
            new_lctx.page_lock_map() =~= old_lctx.page_lock_map().remove(page_index),
        ensures
            page_lock_id_aligned(new_pages, new_lctx),
    {
        reveal(page_lock_id_aligned);
        assert forall|i: PageIndex|
            #![trigger new_lctx.page_lock_map()[i]]
            new_lctx.page_lock_map().dom().contains(i)
            ==> page_index_wf(i)
                && new_pages.lock_id_by_index(i)
                    == new_lctx.page_lock_map()[i] by {
            if new_lctx.page_lock_map().dom().contains(i) {
                assert(old_lctx.page_lock_map().dom().contains(i));
                assert(i != page_index);
                assert(new_lctx.page_lock_map()[i]
                    == old_lctx.page_lock_map()[i]);
                assert(new_pages[i] === old_pages[i]);
                assert(new_pages.lock_id_by_index(i)
                    == old_pages.lock_id_by_index(i));
            }
        }
    }

    /// A boundary keeps the lock map intact and preserves every held page.
    /// Thus it also preserves the page portion of lock-id alignment, even
    /// though unheld page slots may be changed by interleaved threads.
    pub proof fn page_lock_id_aligned_after_boundary(
        old_pages: PageLockedArray,
        new_pages: PageLockedArray,
        old_lctx: &LocalContext,
        new_lctx: &LocalContext,
    )
        requires
            page_lock_id_aligned(old_pages, old_lctx),
            new_lctx.page_lock_map() == old_lctx.page_lock_map(),
            forall|i: PageIndex|
                #![auto]
                old_lctx.page_lock_map().dom().contains(i)
                ==> page_index_wf(i) && new_pages[i]@ == old_pages[i]@,
        ensures
            page_lock_id_aligned(new_pages, new_lctx),
    {
        reveal(page_lock_id_aligned);
        assert forall|i: PageIndex|
            #![trigger new_lctx.page_lock_map()[i]]
            new_lctx.page_lock_map().dom().contains(i)
            ==> page_index_wf(i)
                && new_pages.lock_id_by_index(i)
                    == new_lctx.page_lock_map()[i] by {
            if new_lctx.page_lock_map().dom().contains(i) {
                assert(new_lctx.page_lock_map().dom() == old_lctx.page_lock_map().dom());
                assert(old_lctx.page_lock_map().dom().contains(i));
                assert(page_index_wf(i));
                assert(new_pages[i]@ == old_pages[i]@);
                assert(new_pages.lock_id_by_index(i) == old_pages.lock_id_by_index(i));
                assert(new_lctx.page_lock_map()[i]
                    == old_lctx.page_lock_map()[i]);
            }
        }
    }

    /// Instantiate a boundary's quantified page frame for one held page.
    pub proof fn held_page_aligned_after_boundary(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        page_index: PageIndex,
    )
        requires
            page_index_wf(page_index),
            pre_lctx.page_lock_map().dom().contains(page_index),
            page_lock_id_aligned(pre.page_array, pre_lctx),
            post_lctx.page_lock_map() == pre_lctx.page_lock_map(),
            boundary_pages_preserved(pre, post, pre_lctx),
            post.locked_objects_match_lctx(post_lctx),
        ensures
            post.page_array[page_index]@ == pre.page_array[page_index]@,
            post_lctx.page_lock_map().dom().contains(page_index),
            post_lctx.page_lock_map()[page_index]
                == post.page_array.lock_id_by_index(page_index),
            post.page_array[page_index]@.locked_by(post_lctx),
    {
        reveal(boundary_pages_preserved);
        reveal(page_lock_id_aligned);
        reveal(KernelK::locked_objects_match_lctx);
        reveal(page_locked_match_lctx);
    }

    #[verifier::opaque]
    pub open spec fn container_locked_match_lctx(
        container_map: ContainerLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        // forward
        &&& (forall|c: RwLockContainerPtr|
            #![trigger lctx.container_lock_map().dom().contains(c)]
            lctx.container_lock_map().dom().contains(c)
            ==>
            container_map.dom().contains(c)
            && container_map[c].locked_by(lctx)
            && container_map[c].locking_thread() is Write)
        // reverse
        &&& (forall|c: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c)]
            container_map.dom().contains(c) && container_map[c].locked_by(lctx)
            ==> lctx.container_lock_map().dom().contains(c))
    }

    #[verifier::opaque]
    pub open spec fn process_locked_match_lctx(process_map: ProcessLockedMap, lctx: &LocalContext) -> bool {
        &&& (forall|p: RwLockProcessPtr|
            #![trigger lctx.process_lock_map().dom().contains(p)]
            lctx.process_lock_map().dom().contains(p)
            ==>
            process_map.dom().contains(p)
            && process_map[p].locked_by(lctx)
            && process_map[p].locking_thread() is Write)
        &&& (forall|p: RwLockProcessPtr|
            #![trigger process_map.dom().contains(p)]
            process_map.dom().contains(p) && process_map[p].locked_by(lctx)
            ==> lctx.process_lock_map().dom().contains(p))
    }

    #[verifier::opaque]
    pub open spec fn thread_locked_match_lctx(thread_map: ThreadLockedMap, lctx: &LocalContext) -> bool {
        &&& (forall|t: RwLockThreadPtr|
            #![trigger lctx.thread_lock_map().dom().contains(t)]
            lctx.thread_lock_map().dom().contains(t)
            ==>
            thread_map.dom().contains(t)
            && thread_map[t].locked_by(lctx)
            && thread_map[t].locking_thread() is Write)
        &&& (forall|t: RwLockThreadPtr|
            #![trigger thread_map.dom().contains(t)]
            thread_map.dom().contains(t) && thread_map[t].locked_by(lctx)
            ==> lctx.thread_lock_map().dom().contains(t))
    }

    #[verifier::opaque]
    pub open spec fn endpoint_locked_match_lctx(
        endpoint_map: EndpointLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger lctx.endpoint_lock_map().dom().contains(e)]
            lctx.endpoint_lock_map().dom().contains(e)
            ==>
            endpoint_map.dom().contains(e)
            && endpoint_map[e].locked_by(lctx)
            && endpoint_map[e].locking_thread() is Write)
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger endpoint_map.dom().contains(e)]
            endpoint_map.dom().contains(e) && endpoint_map[e].locked_by(lctx)
            ==> lctx.endpoint_lock_map().dom().contains(e))
    }

    #[verifier::opaque]
    pub open spec fn scheduler_locked_match_lctx(
        scheduler_map: SchedulerLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger lctx.scheduler_lock_map().dom().contains(s)]
            lctx.scheduler_lock_map().dom().contains(s)
            ==>
            scheduler_map.dom().contains(s)
            && scheduler_map[s].locked_by(lctx)
            && scheduler_map[s].locking_thread() is Write)
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger scheduler_map.dom().contains(s)]
            scheduler_map.dom().contains(s) && scheduler_map[s].locked_by(lctx)
            ==> lctx.scheduler_lock_map().dom().contains(s))
    }

    #[verifier::opaque]
    pub open spec fn pagetable_locked_match_lctx(
        pagetable_map: PageTableLockedMap,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
            lctx.pagetable_lock_map().dom().contains(pt)
            ==>
            pagetable_map.dom().contains(pt)
            && pagetable_map[pt].locked_by(lctx)
            && pagetable_map[pt].locking_thread() is Write)
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt)]
            pagetable_map.dom().contains(pt) && pagetable_map[pt].locked_by(lctx)
            ==> lctx.pagetable_lock_map().dom().contains(pt))
    }

    #[verifier::opaque]
    pub open spec fn page_locked_match_lctx(
        page_array: PageLockedArray,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|i: PageIndex|
            #![trigger lctx.page_lock_map().dom().contains(i)]
            #![trigger page_array[i]]
            lctx.page_lock_map().dom().contains(i)
            ==>
            page_index_wf(i)
            && page_array[i]@.locked_by(lctx)
            && page_array[i]@.locking_thread() is Write)
        &&& (forall|i: PageIndex|
            #![trigger page_array[i]@.locked_by(lctx)]
            #![trigger page_array[i]]
            page_index_wf(i) && page_array[i]@.locked_by(lctx)
            ==> lctx.page_lock_map().dom().contains(i))
    }

    #[verifier::opaque]
    pub open spec fn cpu_locked_match_lctx(
        cpu_array: CpuLockedArray,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|c: CpuId|
            #![trigger lctx.cpu_lock_map().dom().contains(c)]
            #![trigger cpu_array[c]]
            lctx.cpu_lock_map().dom().contains(c)
            ==>
            cpu_id_valid(c)
            && cpu_array[c]@.locked_by(lctx)
            && cpu_array[c]@.locking_thread() is Write)
        &&& (forall|c: CpuId|
            #![trigger cpu_array[c]@.locked_by(lctx)]
            #![trigger cpu_array[c]]
            cpu_id_valid(c) && cpu_array[c]@.locked_by(lctx)
            ==> lctx.cpu_lock_map().dom().contains(c))
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
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))]
            #![trigger alloc_map.spec_index(p)]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.locked_by(lctx)
            && alloc_map[p].quota.locking_thread() is Write)
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))]
            #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c]@.locked_by(lctx)
            && alloc_map[p].cpu_caches[c]@.locking_thread() is Write)
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))]
            #![trigger alloc_map.spec_index(p)]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_pool.locked_by(lctx)
            && alloc_map[p].global_pool.locking_thread() is Write)
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.dom().contains(p)]
            #![trigger alloc_map.spec_index(p)]
            alloc_map.dom().contains(p)
            ==>
            {
                &&& alloc_map[p].quota.locked_by(lctx)
                    ==> lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))
                &&& alloc_map[p].global_pool.locked_by(lctx)
                    ==> lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))
                &&& forall|c: CpuId|
                    #![trigger alloc_map[p].cpu_caches[c]@.locked_by(lctx)]
                    #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
                    cpu_id_valid(c) && alloc_map[p].cpu_caches[c]@.locked_by(lctx)
                    ==> lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))
            })
    }

    // ================================================================
    // Boundary preservation predicates, grouped by kernel subsystem.
    // Each relates the pre-boundary kernel `pre` to the post-boundary
    // kernel `post`: rodata of surviving objects is immutable, and any
    // object held in the corresponding LocalContext map (or write-locked by `lctx`) is
    // preserved in its entirety.
    // ================================================================

    pub open spec fn boundary_containers_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.container_map.dom().contains(c)]
            #![trigger post.container_map.dom().contains(c)]
            pre.container_map.dom().contains(c) && post.container_map.dom().contains(c)
            ==> post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata()
        &&& forall|c: RwLockContainerPtr|
            #![trigger lctx.container_lock_map().dom().contains(c)]
            #![trigger pre.container_map.spec_index(c).locked_by(lctx)]
            #![trigger pre.container_map.dom().contains(c)]
            #![trigger post.container_map.dom().contains(c)]
            (lctx.container_lock_map().dom().contains(c)
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
            #![trigger lctx.process_lock_map().dom().contains(p)]
            #![trigger pre.process_map.spec_index(p).locked_by(lctx)]
            #![trigger pre.process_map.dom().contains(p)]
            #![trigger post.process_map.dom().contains(p)]
            (lctx.process_lock_map().dom().contains(p)
                || (pre.process_map.dom().contains(p) && pre.process_map.spec_index(p).locked_by(lctx)))
            ==> post.process_map.dom().contains(p) && post.process_map[p] == pre.process_map[p]
    }

    pub open spec fn boundary_threads_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|t: RwLockThreadPtr|
            #![trigger lctx.thread_lock_map().dom().contains(t)]
            #![trigger pre.thread_map.spec_index(t).locked_by(lctx)]
            #![trigger pre.thread_map.dom().contains(t)]
            #![trigger post.thread_map.dom().contains(t)]
            (lctx.thread_lock_map().dom().contains(t)
                || (pre.thread_map.dom().contains(t) && pre.thread_map.spec_index(t).locked_by(lctx)))
            ==> post.thread_map.dom().contains(t) && post.thread_map[t] == pre.thread_map[t]
    }

    pub open spec fn boundary_endpoints_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|e: RwLockEndpointPtr|
            #![trigger lctx.endpoint_lock_map().dom().contains(e)]
            #![trigger pre.endpoint_map.spec_index(e).locked_by(lctx)]
            #![trigger pre.endpoint_map.dom().contains(e)]
            #![trigger post.endpoint_map.dom().contains(e)]
            (lctx.endpoint_lock_map().dom().contains(e)
                || (pre.endpoint_map.dom().contains(e) && pre.endpoint_map.spec_index(e).locked_by(lctx)))
            ==> post.endpoint_map.dom().contains(e) && post.endpoint_map[e] == pre.endpoint_map[e]
    }

    pub open spec fn boundary_schedulers_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|s: RwLockSchedulerPtr|
            #![trigger lctx.scheduler_lock_map().dom().contains(s)]
            #![trigger pre.scheduler_map.spec_index(s).locked_by(lctx)]
            #![trigger pre.scheduler_map.dom().contains(s)]
            #![trigger post.scheduler_map.dom().contains(s)]
            #![trigger post.scheduler_map.spec_index(s)]
            (lctx.scheduler_lock_map().dom().contains(s)
                || (pre.scheduler_map.dom().contains(s) && pre.scheduler_map.spec_index(s).locked_by(lctx)))
            ==> post.scheduler_map.dom().contains(s) && post.scheduler_map[s] == pre.scheduler_map[s]
    }

    pub open spec fn boundary_pagetables_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|pt: RwLockPageTableRoot|
            #![trigger lctx.pagetable_lock_map().dom().contains(pt)]
            #![trigger pre.pagetable_map.spec_index(pt).locked_by(lctx)]
            #![trigger pre.pagetable_map.dom().contains(pt)]
            #![trigger post.pagetable_map.dom().contains(pt)]
            (lctx.pagetable_lock_map().dom().contains(pt)
                || (pre.pagetable_map.dom().contains(pt) && pre.pagetable_map.spec_index(pt).locked_by(lctx)))
            ==> post.pagetable_map.dom().contains(pt) && post.pagetable_map[pt] == pre.pagetable_map[pt]
    }

    pub open spec fn boundary_pages_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|i: PageIndex|
            #![trigger lctx.page_lock_map().dom().contains(i)]
            #![trigger pre.page_array[i]@.locked_by(lctx)]
            (page_index_wf(i) && lctx.page_lock_map().dom().contains(i))
                || (page_index_wf(i) && pre.page_array[i]@.locked_by(lctx))
            ==> post.page_array[i]@ == pre.page_array[i]@
    }

    pub open spec fn boundary_cpus_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        forall|c: CpuId|
            #![trigger lctx.cpu_lock_map().dom().contains(c)]
            #![trigger pre.cpu_array[c]@.locked_by(lctx)]
            #![trigger post.cpu_array[c]@]
            (cpu_id_valid(c) && lctx.cpu_lock_map().dom().contains(c))
                || (cpu_id_valid(c) && pre.cpu_array[c]@.locked_by(lctx))
            ==> post.cpu_array[c]@ == pre.cpu_array[c]@
    }

    pub open spec fn boundary_allocators_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
        &&& forall|sz: PageSize, p: RwLockPageAllocatorPtr|
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Quota(p))
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
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::GlobalPool(p))
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
            #![trigger lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))]
            lctx.allocator_lock_map(sz).dom().contains(AllocatorLockObjId::Cache(p, c))
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

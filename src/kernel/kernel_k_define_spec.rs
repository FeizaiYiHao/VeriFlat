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
    pub type PcidAllocatorLockedMap = LockedMap<RwLockPcidAllocatorPtr, PcidAllocator, (), (), (), PCID_ALLOCATOR_HAS_KILL_STATE>;
    pub type EndpointLockedMap = LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>;
    pub type PageAllocatorUnLockedMap = UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>;
    pub type ProcessLockedMap = LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>;
    pub type ThreadLockedMap = LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>;

    pub struct KernelK{
        pub pagetable_map: PageTableLockedMap,
        pub iommu_table_map: IommuTableLockedMap,
        pub iommu_root_table: IommuRootTable,
        pub page_array: PageLockedArray,
        pub cpu_array: CpuLockedArray,
        pub container_map: ContainerLockedMap,
        pub scheduler_map: SchedulerLockedMap,
        pub pcid_allocator_map: PcidAllocatorLockedMap,
        pub process_map: ProcessLockedMap,
        pub thread_map: ThreadLockedMap,
        pub endpoint_map: EndpointLockedMap,
        pub allocator_4k_map: PageAllocatorUnLockedMap,
        pub allocator_2m_map: PageAllocatorUnLockedMap,
        pub allocator_1g_map: PageAllocatorUnLockedMap,
        pub cpu_tlb: CpuTLB,
        pub iommu_tlb: IommuTLB,

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
            iommu_table_perms_wf(self.iommu_table_map)
            &&&
            self.iommu_root_table.wf()
            &&&
            page_array_wf(self.page_array)
            &&&
            cpu_array_wf(self.cpu_array, self.default_pagetable.view())
            &&&
            self.cpu_tlb.inv()
            &&&
            self.iommu_tlb.inv()
            &&&
            container_perms_wf(self.container_map)
            &&&
            process_perms_wf(self.process_map)
            &&&
            thread_perms_wf(self.thread_map)
            &&&
            scheduler_perms_wf(self.scheduler_map)
            &&&
            pcid_allocator_perms_wf(self.pcid_allocator_map)
            &&&
            endpoint_perms_wf(self.endpoint_map)
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
            iommu_table_pages_wf(self.iommu_table_map, self.page_array)
            &&&
            thread_pages_wf(self.thread_map, self.page_array)
            &&&
            pcid_allocator_pages_wf(
                self.page_array,
                self.pcid_allocator_map,
            )
            &&&
            process_staged_pages_wf(self.process_map, self.page_array)
            &&&
            endpoint_pages_wf(self.endpoint_map, self.page_array)
            &&&
            process_pagetable_match(self.process_map, self.pagetable_map)
            &&&
            process_iommu_table_match(self.process_map, self.iommu_table_map)
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
            container_pcid_allocator_wf(
                self.container_map,
                self.pcid_allocator_map,
            )
            &&&
            process_pcid_allocator_wf(
                self.container_map,
                self.process_map,
                self.pcid_allocator_map,
            )
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
            &&&
            iommu_root_table_process_wf(
                &self.iommu_root_table,
                self.process_map,
                self.iommu_table_map,
            )
            &&&
            process_pci_function_ownership_wf(
                &self.iommu_root_table,
                self.process_map,
            )
            &&&
            iommu_tlb_wf_spec(
                self.iommu_tlb,
                &self.iommu_root_table,
                self.process_map,
                self.iommu_table_map,
            )
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
            self.default_pagetable.view().pcid_value() == KERNEL_DEFAULT_PCID
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
            &&& lctx.wf()
            &&& container_locked_match_lctx(
                self.container_map, lctx.container_lock_map(), lctx.thread_id())
            &&& process_locked_match_lctx(
                self.process_map, lctx.process_lock_map(), lctx.thread_id())
            &&& thread_locked_match_lctx(
                self.thread_map, lctx.thread_lock_map(), lctx.thread_id())
            &&& endpoint_locked_match_lctx(
                self.endpoint_map, lctx.endpoint_lock_map(), lctx.thread_id())
            &&& scheduler_locked_match_lctx(
                self.scheduler_map, lctx.scheduler_lock_map(), lctx.thread_id())
            &&& pcid_allocator_locked_match_lctx(
                self.pcid_allocator_map,
                lctx.pcid_allocator_lock_map(),
                lctx.thread_id())
            &&& pagetable_locked_match_lctx(
                self.pagetable_map, lctx.pagetable_lock_map(), lctx.thread_id())
            &&& iommu_table_locked_match_lctx(
                self.iommu_table_map,
                lctx.iommu_table_lock_map(),
                lctx.thread_id())
            &&& page_locked_match_lctx(
                self.page_array, lctx.page_lock_map(), lctx.thread_id())
            &&& cpu_locked_match_lctx(
                self.cpu_array, lctx.cpu_lock_map(), lctx.thread_id())
            &&& allocator_4k_locked_match_lctx(
                self.allocator_4k_map, lctx.allocator_4k_lock_map(), lctx.thread_id())
            &&& allocator_2m_locked_match_lctx(
                self.allocator_2m_map, lctx.allocator_2m_lock_map(), lctx.thread_id())
            &&& allocator_1g_locked_match_lctx(
                self.allocator_1g_map, lctx.allocator_1g_lock_map(), lctx.thread_id())
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
                final(lctx).wf(),
                final(lctx).lock_maps_equal(old(lctx)),
                final(lctx).lock_id_set() =~= old(lctx).lock_id_set(),
                final(lctx).kernel_view_locking_state() is Acquire,
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                // KernelSteps: ledger of recorded steps unchanged; snapshot
                // refreshed to the new (post-interleaving) projection.
                final(steps).steps == old(steps).steps,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                // Kernel still in agreement with lctx.
                final(self).locked_objects_match_lctx(final(lctx)),
                // A boundary cannot make this LocalContext acquire a lock.
                // Objects not locked by us before the interleaving remain not
                // locked by us afterwards, even though other threads may
                // otherwise mutate or lock those objects.
                boundary_no_new_locks(
                    old(self),
                    final(self),
                    old(lctx),
                    final(lctx),
                ),
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
                boundary_pcid_allocators_preserved(old(self), final(self), old(lctx)),
                boundary_pagetables_preserved(old(self), final(self), old(lctx)),
                boundary_iommu_tables_preserved(old(self), final(self), old(lctx)),
                boundary_pages_preserved(old(self), final(self), old(lctx)),
                boundary_cpus_preserved(old(self), final(self), old(lctx)),
                boundary_allocators_preserved(old(self), final(self), old(lctx)),
                forall|p: RwLockPageAllocatorPtr, c: CpuId|
                    #![trigger old(self).allocator_4k_map.spec_index(p)
                        .cpu_caches[c]@.wlocked_by(old(lctx))]
                    old(self).allocator_4k_map.dom().contains(p)
                        && cpu_id_valid(c)
                        && old(self).allocator_4k_map.spec_index(p)
                            .cpu_caches[c]@.wlocked_by(old(lctx))
                    ==> final(self).allocator_4k_map.dom().contains(p)
                        && final(self).allocator_4k_map.spec_index(p)
                            .cpu_caches[c]@
                            == old(self).allocator_4k_map.spec_index(p)
                                .cpu_caches[c]@
                        && final(self).allocator_4k_map.spec_index(p)
                            .cpu_caches[c]@.wlocked_by(final(lctx)),
                forall|p: RwLockPageAllocatorPtr|
                    #![trigger old(self).allocator_4k_map.spec_index(p)
                        .global_pool.wlocked_by(old(lctx))]
                    old(self).allocator_4k_map.dom().contains(p)
                        && old(self).allocator_4k_map.spec_index(p)
                            .global_pool.wlocked_by(old(lctx))
                    ==> final(self).allocator_4k_map.dom().contains(p)
                        && final(self).allocator_4k_map.spec_index(p).global_pool
                            == old(self).allocator_4k_map.spec_index(p).global_pool
                        && final(self).allocator_4k_map.spec_index(p)
                            .global_pool.wlocked_by(final(lctx)),
                forall|c: RwLockContainerPtr|
                    #![trigger old(self).container_map.spec_index(c).locked_by(old(lctx))]
                    old(self).container_map.dom().contains(c)
                        && old(self).container_map.spec_index(c).locked_by(old(lctx))
                    ==> final(self).container_map.dom().contains(c)
                        && final(self).container_map.spec_index(c)
                            == old(self).container_map.spec_index(c),
                forall|p: RwLockProcessPtr|
                    #![trigger old(self).process_map.spec_index(p).locked_by(old(lctx))]
                    old(self).process_map.dom().contains(p)
                        && old(self).process_map.spec_index(p).locked_by(old(lctx))
                    ==> final(self).process_map.dom().contains(p)
                        && final(self).process_map.spec_index(p)
                            == old(self).process_map.spec_index(p)
                        && final(self).process_map.lock_id_by_key(p)
                            == old(self).process_map.lock_id_by_key(p)
                        && final(self).process_map.spec_index(p)
                            .locked_by(final(lctx))
                        && final(self).container_map.dom().contains(
                            old(self).process_map.spec_index(p)
                                .view_rodata().view().owning_container)
                        && final(self).container_map.spec_index(
                            old(self).process_map.spec_index(p)
                                .view_rodata().view().owning_container)
                            .view_rodata()
                            == old(self).container_map.spec_index(
                                old(self).process_map.spec_index(p)
                                    .view_rodata().view().owning_container)
                                .view_rodata(),
                forall|t: RwLockThreadPtr|
                    #![trigger old(self).thread_map.spec_index(t).locked_by(old(lctx))]
                    old(self).thread_map.dom().contains(t)
                        && old(self).thread_map.spec_index(t).locked_by(old(lctx))
                    ==> final(self).thread_map.dom().contains(t)
                        && final(self).thread_map.spec_index(t)
                            == old(self).thread_map.spec_index(t),
                forall|s: RwLockSchedulerPtr|
                    #![trigger old(self).scheduler_map.spec_index(s).locked_by(old(lctx))]
                    old(self).scheduler_map.dom().contains(s)
                        && old(self).scheduler_map.spec_index(s).locked_by(old(lctx))
                    ==> final(self).scheduler_map.dom().contains(s)
                        && final(self).scheduler_map.spec_index(s)
                            == old(self).scheduler_map.spec_index(s),
                forall|i: PageIndex|
                    #![trigger old(self).page_array[i]@.locked_by(old(lctx))]
                    page_index_wf(i) && old(self).page_array[i]@.locked_by(old(lctx))
                    ==> final(self).page_array[i]@ == old(self).page_array[i]@,
                forall|c: CpuId|
                    #![trigger old(self).cpu_array[c]@.locked_by(old(lctx))]
                    cpu_id_valid(c) && old(self).cpu_array[c]@.locked_by(old(lctx))
                    ==> final(self).cpu_array[c]@ == old(self).cpu_array[c]@,
                lock_id_aligned(final(self), final(lctx)),
        {
            unimplemented!()
        }
    }

    // ---- Lock-id alignment ----
    #[verifier::opaque]
    pub open spec fn page_lock_id_aligned(
        page_array: PageLockedArray,
        lctx: &LocalContext,
    ) -> bool
        recommends page_locked_match_lctx(
            page_array, lctx.page_lock_map(), lctx.thread_id())
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

    /// Dynamic ordering ids agree with their currently locked objects before
    /// a boundary.  Pages are the only object family whose ordering id changes
    /// with payload state in the implemented transitions; static families are
    /// preserved by their acquire/release contracts.
    pub open spec fn lock_id_aligned(k: &KernelK, lctx: &LocalContext) -> bool {
        page_lock_id_aligned(k.page_array, lctx)
    }

    #[verifier::opaque]
    pub open spec fn container_locked_match_lctx(
        container_map: ContainerLockedMap,
        lock_map: Map<RwLockContainerPtr, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        // forward
        &&& (forall|c: RwLockContainerPtr|
            #![trigger lock_map.dom().contains(c)]
            lock_map.dom().contains(c)
            ==>
            container_map.dom().contains(c)
            && container_map[c].locked_by_thread(thread_id)
            && container_map[c].locking_thread() is Write
            && lock_map[c] == container_map.lock_id_by_key(c))
        // reverse
        &&& (forall|c: RwLockContainerPtr|
            #![trigger container_map.dom().contains(c)]
            container_map.dom().contains(c) && container_map[c].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(c))
    }

    #[verifier::opaque]
    pub open spec fn process_locked_match_lctx(
        process_map: ProcessLockedMap,
        lock_map: Map<RwLockProcessPtr, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|p: RwLockProcessPtr|
            #![trigger lock_map.dom().contains(p)]
            lock_map.dom().contains(p)
            ==>
            process_map.dom().contains(p)
            && process_map[p].locked_by_thread(thread_id)
            && process_map[p].locking_thread() is Write
            && lock_map[p] == process_map.lock_id_by_key(p))
        &&& (forall|p: RwLockProcessPtr|
            #![trigger process_map.dom().contains(p)]
            process_map.dom().contains(p) && process_map[p].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(p))
    }

    #[verifier::opaque]
    pub open spec fn thread_locked_match_lctx(
        thread_map: ThreadLockedMap,
        lock_map: Map<RwLockThreadPtr, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|t: RwLockThreadPtr|
            #![trigger lock_map.dom().contains(t)]
            lock_map.dom().contains(t)
            ==>
            thread_map.dom().contains(t)
            && thread_map[t].locked_by_thread(thread_id)
            && thread_map[t].locking_thread() is Write
            && lock_map[t] == thread_map.lock_id_by_key(t))
        &&& (forall|t: RwLockThreadPtr|
            #![trigger thread_map.dom().contains(t)]
            thread_map.dom().contains(t) && thread_map[t].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(t))
    }

    #[verifier::opaque]
    pub open spec fn endpoint_locked_match_lctx(
        endpoint_map: EndpointLockedMap,
        lock_map: Map<RwLockEndpointPtr, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger lock_map.dom().contains(e)]
            lock_map.dom().contains(e)
            ==>
            endpoint_map.dom().contains(e)
            && endpoint_map[e].locked_by_thread(thread_id)
            && endpoint_map[e].locking_thread() is Write
            && lock_map[e] == (LockId {
                container: LockOwnerId::none(),
                process: LockOwnerId::none(),
                major: ENDPOINT_LOCK_MAJOR,
                minor: e,
            }))
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger endpoint_map.dom().contains(e)]
            endpoint_map.dom().contains(e) && endpoint_map[e].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(e))
    }

    #[verifier::opaque]
    pub open spec fn scheduler_locked_match_lctx(
        scheduler_map: SchedulerLockedMap,
        lock_map: Map<RwLockSchedulerPtr, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger lock_map.dom().contains(s)]
            lock_map.dom().contains(s)
            ==>
            scheduler_map.dom().contains(s)
            && scheduler_map[s].locked_by_thread(thread_id)
            && scheduler_map[s].locking_thread() is Write
            && lock_map[s] == scheduler_map.lock_id_by_key(s))
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger scheduler_map.dom().contains(s)]
            scheduler_map.dom().contains(s) && scheduler_map[s].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(s))
    }

    #[verifier::opaque]
    pub open spec fn pcid_allocator_locked_match_lctx(
        allocator_map: PcidAllocatorLockedMap,
        lock_map: Map<RwLockPcidAllocatorPtr, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|allocator_ptr: RwLockPcidAllocatorPtr|
            #![trigger lock_map.dom().contains(allocator_ptr)]
            lock_map.dom().contains(allocator_ptr)
            ==>
            allocator_map.dom().contains(allocator_ptr)
            && allocator_map[allocator_ptr].locked_by_thread(thread_id)
            && allocator_map[allocator_ptr].locking_thread() is Write
            && lock_map[allocator_ptr]
                == allocator_map.lock_id_by_key(allocator_ptr))
        &&& (forall|allocator_ptr: RwLockPcidAllocatorPtr|
            #![trigger allocator_map.dom().contains(allocator_ptr)]
            allocator_map.dom().contains(allocator_ptr)
            && allocator_map[allocator_ptr].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(allocator_ptr))
    }

    #[verifier::opaque]
    pub open spec fn pagetable_locked_match_lctx(
        pagetable_map: PageTableLockedMap,
        lock_map: Map<RwLockPageTableRoot, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger lock_map.dom().contains(pt)]
            lock_map.dom().contains(pt)
            ==>
            pagetable_map.dom().contains(pt)
            && pagetable_map[pt].locked_by_thread(thread_id)
            && pagetable_map[pt].locking_thread() is Write
            && lock_map[pt] == pt.to_lock_id())
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt)]
            pagetable_map.dom().contains(pt) && pagetable_map[pt].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(pt))
    }

    #[verifier::opaque]
    pub open spec fn iommu_table_locked_match_lctx(
        iommu_table_map: IommuTableLockedMap,
        lock_map: Map<RwLockPageTableRoot, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|iommu_root: RwLockPageTableRoot|
            #![trigger lock_map.dom().contains(iommu_root)]
            lock_map.dom().contains(iommu_root)
            ==>
            iommu_table_map.dom().contains(iommu_root)
            && iommu_table_map[iommu_root].locked_by_thread(thread_id)
            && iommu_table_map[iommu_root].locking_thread() is Write
            && lock_map[iommu_root]
                == iommu_table_map.lock_id_by_key(iommu_root))
        &&& (forall|iommu_root: RwLockPageTableRoot|
            #![trigger iommu_table_map.dom().contains(iommu_root)]
            iommu_table_map.dom().contains(iommu_root)
            && iommu_table_map[iommu_root].locked_by_thread(thread_id)
            ==> lock_map.dom().contains(iommu_root))
    }

    #[verifier::opaque]
    pub open spec fn page_locked_match_lctx(
        page_array: PageLockedArray,
        lock_map: Map<PageIndex, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|i: PageIndex|
            #![trigger lock_map.dom().contains(i)]
            #![trigger page_array[i]]
            lock_map.dom().contains(i)
            ==>
            page_index_wf(i)
            && page_array[i]@.locked_by_thread(thread_id)
            && page_array[i]@.locking_thread() is Write
            && lock_map[i] == page_array.lock_id_by_index(i))
        &&& (forall|i: PageIndex|
            #![trigger page_array[i]@.locked_by_thread(thread_id)]
            #![trigger page_array[i]]
            page_index_wf(i) && page_array[i]@.locked_by_thread(thread_id)
            ==> lock_map.dom().contains(i))
    }

    #[verifier::opaque]
    pub open spec fn cpu_locked_match_lctx(
        cpu_array: CpuLockedArray,
        lock_map: Map<CpuId, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|c: CpuId|
            #![trigger lock_map.dom().contains(c)]
            #![trigger cpu_array[c]]
            lock_map.dom().contains(c)
            ==>
            cpu_id_valid(c)
            && cpu_array[c]@.locked_by_thread(thread_id)
            && cpu_array[c]@.locking_thread() is Write
            && lock_map[c] == cpu_array.lock_id_by_index(c))
        &&& (forall|c: CpuId|
            #![trigger cpu_array[c]@.locked_by_thread(thread_id)]
            #![trigger cpu_array[c]]
            cpu_id_valid(c) && cpu_array[c]@.locked_by_thread(thread_id)
            ==> lock_map.dom().contains(c))
    }

    #[verifier::opaque]
    pub open spec fn allocator_4k_locked_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        lock_map: Map<AllocatorLockObjId, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::Quota(p))]
            #![trigger alloc_map.spec_index(p)]
            lock_map.dom().contains(AllocatorLockObjId::Quota(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.locked_by_thread(thread_id)
            && alloc_map[p].quota.locking_thread() is Write
            && lock_map[AllocatorLockObjId::Quota(p)] == alloc_map[p].quota.lock_id())
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))]
            #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
            lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)
            && alloc_map[p].cpu_caches[c]@.locking_thread() is Write
            && lock_map[AllocatorLockObjId::Cache(p, c)]
                == alloc_map[p].cpu_caches.lock_id_by_index(c))
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))]
            #![trigger alloc_map.spec_index(p)]
            lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_pool.locked_by_thread(thread_id)
            && alloc_map[p].global_pool.locking_thread() is Write
            && lock_map[AllocatorLockObjId::GlobalPool(p)] == alloc_map[p].global_pool.lock_id())
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.dom().contains(p)]
            #![trigger alloc_map.spec_index(p)]
            alloc_map.dom().contains(p)
            ==>
            {
                &&& alloc_map[p].quota.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::Quota(p))
                &&& alloc_map[p].global_pool.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))
                &&& forall|c: CpuId|
                    #![trigger alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)]
                    #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
                    cpu_id_valid(c) && alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))
            })
    }

    #[verifier::opaque]
    pub open spec fn allocator_2m_locked_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        lock_map: Map<AllocatorLockObjId, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::Quota(p))]
            #![trigger alloc_map.spec_index(p)]
            lock_map.dom().contains(AllocatorLockObjId::Quota(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.locked_by_thread(thread_id)
            && alloc_map[p].quota.locking_thread() is Write
            && lock_map[AllocatorLockObjId::Quota(p)] == alloc_map[p].quota.lock_id())
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))]
            #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
            lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)
            && alloc_map[p].cpu_caches[c]@.locking_thread() is Write
            && lock_map[AllocatorLockObjId::Cache(p, c)]
                == alloc_map[p].cpu_caches.lock_id_by_index(c))
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))]
            #![trigger alloc_map.spec_index(p)]
            lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_pool.locked_by_thread(thread_id)
            && alloc_map[p].global_pool.locking_thread() is Write
            && lock_map[AllocatorLockObjId::GlobalPool(p)] == alloc_map[p].global_pool.lock_id())
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.dom().contains(p)]
            #![trigger alloc_map.spec_index(p)]
            alloc_map.dom().contains(p)
            ==>
            {
                &&& alloc_map[p].quota.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::Quota(p))
                &&& alloc_map[p].global_pool.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))
                &&& forall|c: CpuId|
                    #![trigger alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)]
                    #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
                    cpu_id_valid(c) && alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))
            })
    }

    #[verifier::opaque]
    pub open spec fn allocator_1g_locked_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        lock_map: Map<AllocatorLockObjId, LockId>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::Quota(p))]
            #![trigger alloc_map.spec_index(p)]
            lock_map.dom().contains(AllocatorLockObjId::Quota(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.locked_by_thread(thread_id)
            && alloc_map[p].quota.locking_thread() is Write
            && lock_map[AllocatorLockObjId::Quota(p)] == alloc_map[p].quota.lock_id())
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))]
            #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
            lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)
            && alloc_map[p].cpu_caches[c]@.locking_thread() is Write
            && lock_map[AllocatorLockObjId::Cache(p, c)]
                == alloc_map[p].cpu_caches.lock_id_by_index(c))
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))]
            #![trigger alloc_map.spec_index(p)]
            lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_pool.locked_by_thread(thread_id)
            && alloc_map[p].global_pool.locking_thread() is Write
            && lock_map[AllocatorLockObjId::GlobalPool(p)] == alloc_map[p].global_pool.lock_id())
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.dom().contains(p)]
            #![trigger alloc_map.spec_index(p)]
            alloc_map.dom().contains(p)
            ==>
            {
                &&& alloc_map[p].quota.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::Quota(p))
                &&& alloc_map[p].global_pool.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::GlobalPool(p))
                &&& forall|c: CpuId|
                    #![trigger alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)]
                    #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
                    cpu_id_valid(c) && alloc_map[p].cpu_caches[c]@.locked_by_thread(thread_id)
                    ==> lock_map.dom().contains(AllocatorLockObjId::Cache(p, c))
            })
    }

    // ================================================================
    // Boundary preservation predicates, grouped by kernel subsystem.
    // Each relates the pre-boundary kernel `pre` to the post-boundary
    // kernel `post`: rodata of surviving objects is immutable, and any
    // object held in the corresponding LocalContext map (or write-locked by `lctx`) is
    // preserved in its entirety.
    // ================================================================

    #[verifier::opaque]
    pub open spec fn allocator_boundary_no_new_locks(
        pre: PageAllocatorUnLockedMap,
        post: PageAllocatorUnLockedMap,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
    ) -> bool {
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(p).quota.locked_by(post_lctx)]
            post.dom().contains(p)
                && post.spec_index(p).quota.locked_by(post_lctx)
            ==> pre.dom().contains(p)
                && pre.spec_index(p).quota.locked_by(pre_lctx)
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(p).global_pool.locked_by(post_lctx)]
            post.dom().contains(p)
                && post.spec_index(p).global_pool.locked_by(post_lctx)
            ==> pre.dom().contains(p)
                && pre.spec_index(p).global_pool.locked_by(pre_lctx)
        &&& forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger post.spec_index(p).cpu_caches[c]@.locked_by(post_lctx)]
            post.dom().contains(p)
                && cpu_id_valid(c)
                && post.spec_index(p).cpu_caches[c]@.locked_by(post_lctx)
            ==> pre.dom().contains(p)
                && pre.spec_index(p).cpu_caches[c]@.locked_by(pre_lctx)
    }

    /// The boundary may let other threads change unlocked objects, but it
    /// cannot add an object to this thread-local lock ownership set.
    #[verifier::opaque]
    pub open spec fn boundary_no_new_locks(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
    ) -> bool {
        &&& (forall|c: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c).locked_by(post_lctx)]
            post.container_map.dom().contains(c)
                && post.container_map.spec_index(c).locked_by(post_lctx)
            ==> pre.container_map.dom().contains(c)
                && pre.container_map.spec_index(c).locked_by(pre_lctx))
        &&& (forall|p: RwLockProcessPtr|
            #![trigger post.process_map.spec_index(p).locked_by(post_lctx)]
            post.process_map.dom().contains(p)
                && post.process_map.spec_index(p).locked_by(post_lctx)
            ==> pre.process_map.dom().contains(p)
                && pre.process_map.spec_index(p).locked_by(pre_lctx))
        &&& (forall|t: RwLockThreadPtr|
            #![trigger post.thread_map.spec_index(t).locked_by(post_lctx)]
            post.thread_map.dom().contains(t)
                && post.thread_map.spec_index(t).locked_by(post_lctx)
            ==> pre.thread_map.dom().contains(t)
                && pre.thread_map.spec_index(t).locked_by(pre_lctx))
        &&& (forall|e: RwLockEndpointPtr|
            #![trigger post.endpoint_map.spec_index(e).locked_by(post_lctx)]
            post.endpoint_map.dom().contains(e)
                && post.endpoint_map.spec_index(e).locked_by(post_lctx)
            ==> pre.endpoint_map.dom().contains(e)
                && pre.endpoint_map.spec_index(e).locked_by(pre_lctx))
        &&& (forall|s: RwLockSchedulerPtr|
            #![trigger post.scheduler_map.spec_index(s).locked_by(post_lctx)]
            post.scheduler_map.dom().contains(s)
                && post.scheduler_map.spec_index(s).locked_by(post_lctx)
            ==> pre.scheduler_map.dom().contains(s)
                && pre.scheduler_map.spec_index(s).locked_by(pre_lctx))
        &&& (forall|allocator_ptr: RwLockPcidAllocatorPtr|
            #![trigger post.pcid_allocator_map.spec_index(allocator_ptr)
                .locked_by(post_lctx)]
            post.pcid_allocator_map.dom().contains(allocator_ptr)
                && post.pcid_allocator_map.spec_index(allocator_ptr)
                    .locked_by(post_lctx)
            ==> pre.pcid_allocator_map.dom().contains(allocator_ptr)
                && pre.pcid_allocator_map.spec_index(allocator_ptr)
                    .locked_by(pre_lctx))
        &&& (forall|pt: RwLockPageTableRoot|
            #![trigger post.pagetable_map.spec_index(pt).locked_by(post_lctx)]
            post.pagetable_map.dom().contains(pt)
                && post.pagetable_map.spec_index(pt).locked_by(post_lctx)
            ==> pre.pagetable_map.dom().contains(pt)
                && pre.pagetable_map.spec_index(pt).locked_by(pre_lctx))
        &&& (forall|iommu_root: RwLockPageTableRoot|
            #![trigger post.iommu_table_map.spec_index(iommu_root).locked_by(post_lctx)]
            post.iommu_table_map.dom().contains(iommu_root)
                && post.iommu_table_map.spec_index(iommu_root).locked_by(post_lctx)
            ==> pre.iommu_table_map.dom().contains(iommu_root)
                && pre.iommu_table_map.spec_index(iommu_root).locked_by(pre_lctx))
        &&& (forall|i: PageIndex|
            #![trigger post.page_array[i]@.locked_by(post_lctx)]
            page_index_wf(i)
                && post.page_array[i]@.locked_by(post_lctx)
            ==> pre.page_array[i]@.locked_by(pre_lctx))
        &&& (forall|c: CpuId|
            #![trigger post.cpu_array[c]@.locked_by(post_lctx)]
            cpu_id_valid(c)
                && post.cpu_array[c]@.locked_by(post_lctx)
            ==> pre.cpu_array[c]@.locked_by(pre_lctx))
        &&& allocator_boundary_no_new_locks(
            pre.allocator_4k_map,
            post.allocator_4k_map,
            pre_lctx,
            post_lctx,
        )
        &&& allocator_boundary_no_new_locks(
            pre.allocator_2m_map,
            post.allocator_2m_map,
            pre_lctx,
            post_lctx,
        )
        &&& allocator_boundary_no_new_locks(
            pre.allocator_1g_map,
            post.allocator_1g_map,
            pre_lctx,
            post_lctx,
        )
    }

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

    pub open spec fn boundary_pcid_allocators_preserved(
        pre: &KernelK,
        post: &KernelK,
        lctx: &LocalContext,
    ) -> bool {
        forall|allocator_ptr: RwLockPcidAllocatorPtr|
            #![trigger lctx.pcid_allocator_lock_map().dom().contains(allocator_ptr)]
            #![trigger pre.pcid_allocator_map.spec_index(allocator_ptr).locked_by(lctx)]
            #![trigger pre.pcid_allocator_map.dom().contains(allocator_ptr)]
            #![trigger post.pcid_allocator_map.dom().contains(allocator_ptr)]
            (lctx.pcid_allocator_lock_map().dom().contains(allocator_ptr)
                || (pre.pcid_allocator_map.dom().contains(allocator_ptr)
                    && pre.pcid_allocator_map.spec_index(allocator_ptr).locked_by(lctx)))
            ==> post.pcid_allocator_map.dom().contains(allocator_ptr)
                && post.pcid_allocator_map[allocator_ptr]
                    == pre.pcid_allocator_map[allocator_ptr]
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

    pub open spec fn boundary_iommu_tables_preserved(
        pre: &KernelK,
        post: &KernelK,
        lctx: &LocalContext,
    ) -> bool {
        forall|iommu_root: RwLockPageTableRoot|
            #![trigger lctx.iommu_table_lock_map().dom().contains(iommu_root)]
            #![trigger pre.iommu_table_map.spec_index(iommu_root).locked_by(lctx)]
            #![trigger pre.iommu_table_map.dom().contains(iommu_root)]
            #![trigger post.iommu_table_map.dom().contains(iommu_root)]
            (lctx.iommu_table_lock_map().dom().contains(iommu_root)
                || (pre.iommu_table_map.dom().contains(iommu_root)
                    && pre.iommu_table_map.spec_index(iommu_root).locked_by(lctx)))
            ==> post.iommu_table_map.dom().contains(iommu_root)
                && post.iommu_table_map[iommu_root]
                    == pre.iommu_table_map[iommu_root]
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

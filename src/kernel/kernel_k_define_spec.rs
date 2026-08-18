use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {

    pub const KERNEL_DEFAULT_PCID:Pcid = 0;

    pub type PageTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), STABLE_LOCK_ID, PAGE_TABLE_HAS_KILL_STATE>;
    pub type IommuTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<IOMMU_TYPE>, (), (), (), STABLE_LOCK_ID, PAGE_TABLE_HAS_KILL_STATE>;
    pub type PageLockedArray = LockedArray<Page, (), (), (), NUM_PAGES, MUTABLE_LOCK_ID, NO_KILL_STATE>;
    pub type CpuLockedArray = LockedArray<Cpu, (), (), (), NUM_CPUS, MUTABLE_LOCK_ID, CPU_HAS_KILL_STATE>;
    pub type ContainerLockedMap = LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, STABLE_LOCK_ID, CONTAINER_HAS_KILL_STATE>;
    pub type SchedulerLockedMap = LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), STABLE_LOCK_ID, SCHEDULER_HAS_KILL_STATE>;
    pub type PcidAllocatorLockedMap = LockedMap<RwLockPcidAllocatorPtr, PcidAllocator, (), (), (), STABLE_LOCK_ID, PCID_ALLOCATOR_HAS_KILL_STATE>;
    pub type EndpointLockedMap = LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), STABLE_LOCK_ID, ENDPOINT_HAS_KILL_STATE>;
    pub type PageAllocatorUnLockedMap = UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>;
    pub type ProcessLockedMap = LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), STABLE_LOCK_ID, PROCESS_HAS_KILL_STATE>;
    pub type ThreadLockedMap = LockedMap<RwLockThreadPtr, Thread, (), (), (), STABLE_LOCK_ID, THREAD_HAS_KILL_STATE>;

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
            thread_staged_pages_wf(self.thread_map, self.page_array)
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
            container_allocator_free_4k_page_wf(self.allocator_4k_map, self.page_array)
            &&&
            container_allocator_free_2m_page_wf(self.allocator_2m_map, self.page_array)
            &&&
            container_allocator_free_1g_page_wf(self.allocator_1g_map, self.page_array)
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
        // The LocalContext held-lock set and the kernel's physical lock state
        // are exact mirrors.  Each set entry carries both the current dynamic
        // lock id and the object locator, so an id cannot be copied from one
        // object to stand in for another.

        /// Trusted kernel-view step boundary.
        ///
        /// Models "end the current kernel-view atomic section and begin a
        /// new one." Between sections, the rest of the world may run
        /// arbitrary atomic sections:
        ///   - all our held objects (those recorded in the LocalContext set) keep
        ///     their state across the boundary — `view`, `view_kernel_ghost`,
        ///     `view_user_ghost`, `view_rodata`, `locking_thread`,
        ///     `being_killed` are preserved per held lock instance;
        ///   - everything else may change arbitrarily, including map
        ///     domains (except for the fixed-size arrays `cpu_array` and
        ///     `page_array`);
        ///   - the LocalContext held-lock set is unchanged (we still hold what
        ///     we held);
        ///   - the kernel invariant `inv()` is re-established by trust;
        ///   - kernel-view phase flips back to `Acquire`, ready for the
        ///     next atomic section.
        ///
        /// Before interleaving, the boundary compares the completed kernel
        /// section's user projection with `steps.snap_shot`.  A changed
        /// projection is appended as one user step; an unchanged projection is
        /// an internal stuttering step and is omitted.  Only then may other
        /// threads interleave, after which the snapshot is refreshed.
        ///
        /// Preconditions:
        ///   - `inv()` holds (we entered the boundary in a wf state),
        ///   - `kernel_view_locking_state is Release` (the current section
        ///     is done),
        ///   - `lock_id_aligned(self, lctx)` (no stealth locks, every
        ///     LocalContext entry corresponds to the named real held lock),
        #[verifier::external_body]
        pub proof fn kernel_step_boundary(
            tracked &mut self,
            tracked lctx: &mut LocalContext,
            tracked steps: &mut KernelSteps,
        )
            requires
                old(self).inv(),
                old(lctx).kernel_view_locking_state() is Release,
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                // LocalContext is thread-local: the phase flips to Acquire,
                // while its identity and exact held-lock set stay put.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).lock_id_set() == old(lctx).lock_id_set(),
                final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
                // Interleaving cannot acquire a lock on behalf of this
                // thread.  Preserve the lock-free state explicitly instead
                // of deriving it from an empty held-lock set plus alignment.
                old(self).all_objects_unlocked(old(lctx))
                    ==> final(self).all_objects_unlocked(final(lctx)),
                cpu_objects_unlocked(
                    old(self).cpu_array, old(lctx).thread_id(),
                ) ==> cpu_objects_unlocked(
                    final(self).cpu_array, final(lctx).thread_id(),
                ),
                forall|exceptions: Set<CpuId>|
                    #![trigger cpu_objects_unlocked_except(
                        old(self).cpu_array, old(lctx).thread_id(), exceptions)]
                    cpu_objects_unlocked_except(
                        old(self).cpu_array, old(lctx).thread_id(), exceptions,
                    ) ==> cpu_objects_unlocked_except(
                        final(self).cpu_array, final(lctx).thread_id(), exceptions,
                    ),
                page_objects_unlocked(
                    old(self).page_array, old(lctx).thread_id(),
                ) ==> page_objects_unlocked(
                    final(self).page_array, final(lctx).thread_id(),
                ),
                forall|exceptions: Set<PageIndex>|
                    #![trigger page_objects_unlocked_except(
                        old(self).page_array, old(lctx).thread_id(), exceptions)]
                    page_objects_unlocked_except(
                        old(self).page_array, old(lctx).thread_id(), exceptions,
                    ) ==> page_objects_unlocked_except(
                        final(self).page_array, final(lctx).thread_id(), exceptions,
                    ),
                container_objects_unlocked(
                    old(self).container_map, old(lctx).thread_id())
                    ==> container_objects_unlocked(
                        final(self).container_map, final(lctx).thread_id()),
                process_objects_unlocked(
                    old(self).process_map, old(lctx).thread_id())
                    ==> process_objects_unlocked(
                        final(self).process_map, final(lctx).thread_id()),
                thread_objects_unlocked(
                    old(self).thread_map, old(lctx).thread_id())
                    ==> thread_objects_unlocked(
                        final(self).thread_map, final(lctx).thread_id()),
                endpoint_objects_unlocked(
                    old(self).endpoint_map, old(lctx).thread_id())
                    ==> endpoint_objects_unlocked(
                        final(self).endpoint_map, final(lctx).thread_id()),
                pagetable_objects_unlocked(
                    old(self).pagetable_map, old(lctx).thread_id())
                    ==> pagetable_objects_unlocked(
                        final(self).pagetable_map, final(lctx).thread_id()),
                iommu_table_objects_unlocked(
                    old(self).iommu_table_map, old(lctx).thread_id())
                    ==> iommu_table_objects_unlocked(
                        final(self).iommu_table_map, final(lctx).thread_id()),
                scheduler_objects_unlocked(
                    old(self).scheduler_map, old(lctx).thread_id())
                    ==> scheduler_objects_unlocked(
                        final(self).scheduler_map, final(lctx).thread_id()),
                pcid_allocator_objects_unlocked(
                    old(self).pcid_allocator_map, old(lctx).thread_id())
                    ==> pcid_allocator_objects_unlocked(
                        final(self).pcid_allocator_map, final(lctx).thread_id()),
                allocator_objects_unlocked(
                    old(self).allocator_4k_map, old(lctx).thread_id())
                    ==> allocator_objects_unlocked(
                        final(self).allocator_4k_map, final(lctx).thread_id()),
                allocator_objects_unlocked(
                    old(self).allocator_2m_map, old(lctx).thread_id())
                    ==> allocator_objects_unlocked(
                        final(self).allocator_2m_map, final(lctx).thread_id()),
                allocator_objects_unlocked(
                    old(self).allocator_1g_map, old(lctx).thread_id())
                    ==> allocator_objects_unlocked(
                        final(self).allocator_1g_map, final(lctx).thread_id()),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).kernel_view_locking_state() is Acquire,
                // Record this thread's completed section before refreshing the
                // snapshot to the post-interleaving projection.
                final(steps).steps == record_user_view_change(
                    old(steps).steps,
                    old(steps).snap_shot,
                    kernel_k_to_kernel_u(*old(self)),
                ),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                // The kernel lock state is the anchor: every object held
                // before interleaving is
                // still present and bit-for-bit unchanged afterwards.
                held_containers_unchanged(
                    old(self).container_map, final(self).container_map,
                    old(lctx)),
                held_processes_unchanged(
                    old(self).process_map, final(self).process_map,
                    old(lctx)),
                held_process_owning_containers_unchanged(
                    old(self).process_map, final(self).process_map,
                    old(self).container_map, final(self).container_map,
                    old(lctx)),
                held_threads_unchanged(
                    old(self).thread_map, final(self).thread_map,
                    old(lctx)),
                held_endpoints_unchanged(
                    old(self).endpoint_map, final(self).endpoint_map,
                    old(lctx)),
                held_schedulers_unchanged(
                    old(self).scheduler_map, final(self).scheduler_map,
                    old(lctx)),
                held_pcid_allocators_unchanged(
                    old(self).pcid_allocator_map, final(self).pcid_allocator_map,
                    old(lctx)),
                held_pagetables_unchanged(
                    old(self).pagetable_map, final(self).pagetable_map,
                    old(lctx)),
                held_iommu_tables_unchanged(
                    old(self).iommu_table_map, final(self).iommu_table_map,
                    old(lctx)),
                held_pages_unchanged(
                    old(self).page_array, final(self).page_array,
                    old(lctx)),
                held_cpus_unchanged(
                    old(self).cpu_array, final(self).cpu_array,
                    old(lctx)),
                held_allocator_objects_unchanged(
                    old(self).allocator_4k_map, final(self).allocator_4k_map,
                    old(lctx)),
                held_allocator_objects_unchanged(
                    old(self).allocator_2m_map, final(self).allocator_2m_map,
                    old(lctx)),
                held_allocator_objects_unchanged(
                    old(self).allocator_1g_map, final(self).allocator_1g_map,
                    old(lctx)),
                // Deliberately omitted from the old boundary contract:
                // - root/default-pagetable equality across interleaving;
                // Global rodata immutability and final lock-id alignment remain
                // explicit because both are common next-section framing facts.
        {
            unimplemented!()
        }
    }

    // ---- Held-lock / kernel-state alignment ----

    /// Exact mirror for the dynamic-id ledger.  Stable-id objects are tracked
    /// independently in `LocalContext` and do not depend on kernel state.
    #[verifier::opaque]
    pub open spec fn lock_id_aligned(k: &KernelK, lctx: &LocalContext) -> bool {
        &&& (forall|id: LockId, index: PageIndex|
            #![trigger lctx.lock_id_set().contains((id, KernelObjId::Page(index)))]
            lctx.lock_id_set().contains((id, KernelObjId::Page(index))) == {
                &&& index_valid(NUM_PAGES, index)
                &&& k.page_array.spec_index(index).view()
                    .locked_by(lctx)
                &&& id == k.page_array.lock_id_by_index(index)
            })
        &&& (forall|id: LockId, cpu_id: CpuId|
            #![trigger lctx.lock_id_set().contains((id, KernelObjId::Cpu(cpu_id)))]
            lctx.lock_id_set().contains((id, KernelObjId::Cpu(cpu_id))) == {
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& k.cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(lctx.thread_id())
                &&& id == k.cpu_array.lock_id_by_index(cpu_id)
            })
        &&& (forall|index: PageIndex|
            #![trigger k.page_array.spec_index(index).view().locked_by(lctx),
                k.page_array.lock_id_by_index(index)]
            index_valid(NUM_PAGES, index)
                && k.page_array.spec_index(index).view().locked_by(lctx)
            ==> lctx.lock_id_set().contains((
                k.page_array.lock_id_by_index(index), KernelObjId::Page(index))))
        &&& (forall|cpu_id: CpuId|
            #![trigger k.cpu_array.spec_index(cpu_id).view().locked_by(lctx),
                k.cpu_array.lock_id_by_index(cpu_id)]
            index_valid(NUM_CPUS, cpu_id)
                && k.cpu_array.spec_index(cpu_id).view().locked_by(lctx)
            ==> lctx.lock_id_set().contains((
                k.cpu_array.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))))
    }

}

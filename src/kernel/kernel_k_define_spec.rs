use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {

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
            thread_caller_callee_wf(self.thread_map)
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
        ///   - `typed_lock_maps_aligned(self, lctx)` (no stealth locks, every
        ///     LocalContext entry corresponds to the named real held lock),
        /// TCB maintenance rule: do not change this function's signature,
        /// contract, triggers, or body without the user's explicit approval.
        ///
        #[verifier::external_body]
        pub proof fn kernel_step_boundary(
            tracked &mut self,
            tracked lctx: &mut LocalContext,
            tracked steps: &mut KernelSteps,
        )
            requires
                old(self).inv(),
                old(lctx).kernel_view_locking_state() is Release,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                // LocalContext is thread-local: the phase flips to Acquire,
                // while its identity and exact typed lock maps stay put.
                final(lctx).thread_id() == old(lctx).thread_id(),
                typed_lock_maps_unchanged(old(lctx), final(lctx)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                final(lctx).kernel_view_locking_state() is Acquire,
                // Record this thread's completed section before refreshing the
                // snapshot to the post-interleaving projection.
                final(steps).steps == record_user_view_change(
                    old(steps).steps,
                    old(steps).snap_shot,
                    kernel_k_to_kernel_u(*old(self)),
                ),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                containers_rodata_unchanged(
                    old(self).container_map, final(self).container_map,
                ),
                processes_rodata_unchanged(
                    old(self).process_map, final(self).process_map,
                ),
                // The forward typed lock-map domains are the framing range: every
                // object they contain before interleaving is still present
                // and bit-for-bit unchanged afterwards.
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
                    old(lctx).allocator_quota_4k_lock_map(),
                    old(lctx).allocator_global_pool_4k_lock_map(),
                    old(lctx).allocator_cache_4k_lock_map()),
                held_allocator_objects_unchanged(
                    old(self).allocator_2m_map, final(self).allocator_2m_map,
                    old(lctx).allocator_quota_2m_lock_map(),
                    old(lctx).allocator_global_pool_2m_lock_map(),
                    old(lctx).allocator_cache_2m_lock_map()),
                held_allocator_objects_unchanged(
                    old(self).allocator_1g_map, final(self).allocator_1g_map,
                    old(lctx).allocator_quota_1g_lock_map(),
                    old(lctx).allocator_global_pool_1g_lock_map(),
                    old(lctx).allocator_cache_1g_lock_map()),
                // Deliberately omitted from the old boundary contract:
                // - root/default-pagetable equality across interleaving;
                // Global rodata immutability and final typed-lock alignment remain
                // explicit because both are common next-section framing facts.
        {
            unimplemented!()
        }
    }

    // ---- Held-lock / kernel-state alignment ----

    /// Exact forward mirror for every typed lockable object family.
    pub open spec fn typed_lock_maps_aligned(
        k: &KernelK,
        lctx: &LocalContext,
    ) -> bool {
        &&& k.page_array.typed_lock_map_aligned(
            lctx.page_lock_map(), lctx.thread_id())
        &&& k.cpu_array.typed_lock_map_aligned(
            lctx.cpu_lock_map(), lctx.thread_id())
        &&& k.container_map.typed_lock_map_aligned(
            lctx.container_lock_map(), lctx.thread_id())
        &&& k.process_map.typed_lock_map_aligned(
            lctx.process_lock_map(), lctx.thread_id())
        &&& k.thread_map.typed_lock_map_aligned(
            lctx.thread_lock_map(), lctx.thread_id())
        &&& k.endpoint_map.typed_lock_map_aligned(
            lctx.endpoint_lock_map(), lctx.thread_id())
        &&& k.scheduler_map.typed_lock_map_aligned(
            lctx.scheduler_lock_map(), lctx.thread_id())
        &&& k.pcid_allocator_map.typed_lock_map_aligned(
            lctx.pcid_allocator_lock_map(), lctx.thread_id())
        &&& k.pagetable_map.typed_lock_map_aligned(
            lctx.pagetable_lock_map(), lctx.thread_id())
        &&& k.iommu_table_map.typed_lock_map_aligned(
            lctx.iommu_table_lock_map(), lctx.thread_id())
        &&& k.allocator_4k_map.typed_quota_lock_map_aligned(
            lctx.allocator_quota_4k_lock_map(), lctx.thread_id())
        &&& k.allocator_4k_map.typed_cache_lock_map_aligned(
            lctx.allocator_cache_4k_lock_map(), lctx.thread_id())
        &&& k.allocator_4k_map.typed_global_pool_lock_map_aligned(
            lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id())
        &&& k.allocator_2m_map.typed_quota_lock_map_aligned(
            lctx.allocator_quota_2m_lock_map(), lctx.thread_id())
        &&& k.allocator_2m_map.typed_cache_lock_map_aligned(
            lctx.allocator_cache_2m_lock_map(), lctx.thread_id())
        &&& k.allocator_2m_map.typed_global_pool_lock_map_aligned(
            lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id())
        &&& k.allocator_1g_map.typed_quota_lock_map_aligned(
            lctx.allocator_quota_1g_lock_map(), lctx.thread_id())
        &&& k.allocator_1g_map.typed_cache_lock_map_aligned(
            lctx.allocator_cache_1g_lock_map(), lctx.thread_id())
        &&& k.allocator_1g_map.typed_global_pool_lock_map_aligned(
            lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id())
    }

pub proof fn enter_kernel_view_release_preserving_typed_lock_alignment(
    kernel: &KernelK,
    tracked lctx: &mut LocalContext,
)
    requires
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(kernel, old(lctx)),
    ensures
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_maps_aligned(kernel, final(lctx)),
{
    lctx.enter_kernel_view_release();
}

}

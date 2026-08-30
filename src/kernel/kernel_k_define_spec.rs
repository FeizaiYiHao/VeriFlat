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
        pub pt_mp: PageTableLockedMap,
        pub it_mp: IommuTableLockedMap,
        pub irt: IommuRootTable,
        pub pg_arr: PageLockedArray,
        pub cpu_arr: CpuLockedArray,
        pub ctn_mp: ContainerLockedMap,
        pub sched_mp: SchedulerLockedMap,
        pub pcid_allc_mp: PcidAllocatorLockedMap,
        pub prc_mp: ProcessLockedMap,
        pub thr_mp: ThreadLockedMap,
        pub ep_mp: EndpointLockedMap,
        pub allc_4k_mp: PageAllocatorUnLockedMap,
        pub allc_2m_mp: PageAllocatorUnLockedMap,
        pub allc_1g_mp: PageAllocatorUnLockedMap,
        pub cpu_tlb: CpuTLB,
        pub iommu_tlb: IommuTLB,

        pub rt_ctn: RwLockContainerPtr, // Never dies

        // pub number_containers: RwLock<NumContainers, (), (), NO_KILL_STATE>,

        // pub container_to_pagetable_map: Ghost<Map<RwLockContainerPtr, Set<RwLockPageTableRoot>>>,

        pub dflt_pt: ReadOnlyNode<PageTable<PT_TYPE>>, // Read only
    }

    impl KernelK{
        /// all spec functions under this are open
        pub open spec fn subsystems_inv(&self) -> bool {
            &&&
            self.default_pagetable_wf()
            &&&
            pagetable_perms_wf(self.pt_mp)
            &&&
            iommu_table_perms_wf(self.it_mp)
            &&&
            self.irt.wf()
            &&&
            page_array_wf(self.pg_arr)
            &&&
            cpu_array_wf(self.cpu_arr, self.dflt_pt.view())
            &&&
            self.cpu_tlb.inv()
            &&&
            self.iommu_tlb.inv()
            &&&
            container_perms_wf(self.ctn_mp)
            &&&
            process_perms_wf(self.prc_mp)
            &&&
            thread_perms_wf(self.thr_mp)
            &&&
            scheduler_perms_wf(self.sched_mp)
            &&&
            pcid_allocator_perms_wf(self.pcid_allc_mp)
            &&&
            endpoint_perms_wf(self.ep_mp)
            &&&
            allocator_perms_wf(self.allc_4k_mp)
            &&&
            allocator_perms_wf(self.allc_2m_mp)
            &&&
            allocator_perms_wf(self.allc_1g_mp)
        }

        pub open spec fn memory_management_inv(&self) -> bool {
            &&&
            allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&&
            container_page_owner_wf(self.ctn_mp, self.pg_arr)
            &&&
            hugepage_2m_wf(self.pg_arr)
            &&&
            hugepage_1g_wf(self.pg_arr)
            &&&
            page_pagetable_wf(self.pt_mp, self.pg_arr)
            &&&
            container_process_page_pagetable_wf(self.ctn_mp, self.prc_mp, self.pt_mp, self.pg_arr)
            &&&
            container_pages_wf(self.pg_arr, self.ctn_mp)
            &&&
            process_pages_wf(self.pg_arr, self.prc_mp)
            &&&
            pagetable_pages_wf(self.pt_mp, self.pg_arr)
            &&&
            iommu_table_pages_wf(self.it_mp, self.pg_arr)
            &&&
            thread_pages_wf(self.thr_mp, self.pg_arr)
            &&&
            pcid_allocator_pages_wf(
                self.pg_arr,
                self.pcid_allc_mp,
            )
            &&&
            thread_staged_pages_wf(self.thr_mp, self.pg_arr)
            &&&
            endpoint_pages_wf(self.ep_mp, self.pg_arr)
            &&&
            process_pagetable_match(self.prc_mp, self.pt_mp)
            &&&
            process_iommu_table_match(self.prc_mp, self.it_mp)
            &&&
            self.allocator_free_pages_wf()
            &&&
            container_process_allocator_quota_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&&
            container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&&
            container_allocator_free_4k_page_wf(self.allc_4k_mp, self.pg_arr)
            &&&
            container_allocator_free_2m_page_wf(self.allc_2m_mp, self.pg_arr)
            &&&
            container_allocator_free_1g_page_wf(self.allc_1g_mp, self.pg_arr)
        }

        pub open spec fn process_management_inv(&self) -> bool {
            &&&
            container_tree_wf(self.rt_ctn, self.ctn_mp)
            &&&
            container_process_wf(self.ctn_mp, self.prc_mp)
            &&&
            per_container_process_tree_wf(self.ctn_mp, self.prc_mp)
            &&&
            container_endpoint_wf(self.ctn_mp, self.ep_mp)
            &&&
            container_cpu_wf(self.ctn_mp, self.cpu_arr)
            &&&
            thread_endpoint_ref_counter_wf(self.thr_mp, self.ep_mp)
            &&&
            thread_endpoint_queue_wf(self.thr_mp, self.ep_mp)
            &&&
            thread_caller_callee_wf(self.thr_mp)
            &&&
            container_thread_endpoint_wf(self.ctn_mp, self.thr_mp, self.ep_mp)
            &&&
            container_scheduler_wf(self.ctn_mp, self.sched_mp)
            &&&
            container_pcid_allocator_wf(
                self.ctn_mp,
                self.pcid_allc_mp,
            )
            &&&
            process_pcid_allocator_wf(
                self.ctn_mp,
                self.prc_mp,
                self.pcid_allc_mp,
            )
            &&&
            container_thread_scheduler_wf(self.ctn_mp, self.thr_mp, self.sched_mp)
            &&&
            container_thread_wf(self.ctn_mp, self.thr_mp)
            &&&
            process_cpu_wf(self.prc_mp, self.cpu_arr)
            &&&
            process_thread_wf(self.prc_mp, self.thr_mp)
            &&&
            thread_cpu_wf(self.thr_mp, self.cpu_arr)
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
                &self.irt,
                self.prc_mp,
                self.it_mp,
            )
            &&&
            process_pci_function_ownership_wf(
                &self.irt,
                self.prc_mp,
            )
            &&&
            iommu_tlb_wf_spec(
                self.iommu_tlb,
                &self.irt,
                self.prc_mp,
                self.it_mp,
            )
            // TLB spec
            &&&
            cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)
            &&&
            tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)
        }

        #[verifier::opaque]
        pub open spec fn default_pagetable_wf(&self) -> bool {
            &&&
            self.dflt_pt.view().inv()
            &&&
            self.dflt_pt.view().pcid_value() == KERNEL_DEFAULT_PCID
            &&&
            self.dflt_pt.view().is_empty()
        }

        pub open spec fn allocator_free_pages_wf(&self) -> bool{
            &&&
            allocator_free_page_ptrs_wf(self.allc_4k_mp)
            &&&
            allocator_free_page_ptrs_wf(self.allc_2m_mp)
            &&&
            allocator_free_page_ptrs_wf(self.allc_1g_mp)
        }

        // pub open spec fn allocator_cpu_cache_clean(&self) -> bool{
        //     &&&
        //     forall|alloc_ptr: RwLockPageAllocatorPtr|
        //         #![trigger self.allc_4k_mp.spec_index(alloc_ptr).local_quota_clean()]
        //         self.allc_4k_mp.dom().contains(alloc_ptr)
        //         ==>
        //         self.allc_4k_mp.spec_index(alloc_ptr).local_quota_clean()
        //     &&&
        //     forall|alloc_ptr: RwLockPageAllocatorPtr|
        //         #![trigger self.allc_2m_mp.spec_index(alloc_ptr).local_quota_clean()]
        //         self.allc_2m_mp.dom().contains(alloc_ptr)
        //         ==>
        //         self.allc_2m_mp.spec_index(alloc_ptr).local_quota_clean()
        //     &&&
        //     forall|alloc_ptr: RwLockPageAllocatorPtr|
        //         #![trigger self.allc_1g_mp.spec_index(alloc_ptr).local_quota_clean()]
        //         self.allc_1g_mp.dom().contains(alloc_ptr)
        //         ==>
        //         self.allc_1g_mp.spec_index(alloc_ptr).local_quota_clean()
        // }

        // ============================================================
        //   Lock-map / krnl-state agreement
        // ============================================================
        //
        // The LocalContext held-lock set and the krnl's physical lock state
        // are exact mirrors.  Each set entry carries both the current dynamic
        // lock id and the object locator, so an id cannot be copied from one
        // object to stand in for another.

        /// Trusted krnl-view step boundary.
        ///
        /// Models "end the current krnl-view atomic section and begin a
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
        ///   - the krnl invariant `inv()` is re-established by trust;
        ///   - krnl-view phase flips back to `Acquire`, ready for the
        ///     next atomic section.
        ///
        /// Before interleaving, the boundary compares the completed krnl
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
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).kernel_view_locking_state() is Acquire,
                // LocalContext is thread-local: the phase flips to Acquire,
                // while its identity and exact held-lock set stay put.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).lock_id_set() == old(lctx).lock_id_set(),
                // Direct ledger-keyed framing for owner objects.  Callers that
                // already hold an exact pair never need to reverse
                // `lock_id_aligned` merely to recover the held object.
                forall|id: LockId, cpu_id: CpuId|
                    #![trigger old(lctx).lock_id_set().contains((
                        id, KernelObjId::Cpu(cpu_id)))]
                    old(lctx).lock_id_set().contains((
                        id, KernelObjId::Cpu(cpu_id)))
                    ==> final(self).cpu_arr.spec_index(cpu_id).view()
                        == old(self).cpu_arr.spec_index(cpu_id).view(),
                forall|id: LockId, container_ptr: RwLockContainerPtr|
                    #![trigger old(lctx).lock_id_set().contains((
                        id, KernelObjId::Container(container_ptr)))]
                    old(lctx).lock_id_set().contains((
                        id, KernelObjId::Container(container_ptr)))
                    ==> {
                        &&& final(self).ctn_mp.dom().contains(container_ptr)
                        &&& final(self).ctn_mp.lock_id_by_key(container_ptr)
                            == old(self).ctn_mp.lock_id_by_key(container_ptr)
                        &&& final(self).ctn_mp.spec_index(container_ptr)
                            == old(self).ctn_mp.spec_index(container_ptr)
                    },
                forall|id: LockId, process_ptr: RwLockProcessPtr|
                    #![trigger old(lctx).lock_id_set().contains((
                        id, KernelObjId::Process(process_ptr)))]
                    old(lctx).lock_id_set().contains((
                        id, KernelObjId::Process(process_ptr)))
                    ==> {
                        &&& final(self).prc_mp.dom().contains(process_ptr)
                        &&& final(self).prc_mp.lock_id_by_key(process_ptr)
                            == old(self).prc_mp.lock_id_by_key(process_ptr)
                        &&& final(self).prc_mp.spec_index(process_ptr)
                            == old(self).prc_mp.spec_index(process_ptr)
                    },
                forall|id: LockId, thread_ptr: RwLockThreadPtr|
                    #![trigger old(lctx).lock_id_set().contains((
                        id, KernelObjId::Thread(thread_ptr)))]
                    old(lctx).lock_id_set().contains((
                        id, KernelObjId::Thread(thread_ptr)))
                    ==> {
                        &&& final(self).thr_mp.dom().contains(thread_ptr)
                        &&& final(self).thr_mp.lock_id_by_key(thread_ptr)
                            == old(self).thr_mp.lock_id_by_key(thread_ptr)
                        &&& final(self).thr_mp.spec_index(thread_ptr)
                            == old(self).thr_mp.spec_index(thread_ptr)
                    },
                forall|id: LockId, pagetable_ptr: RwLockPageTableRoot|
                    #![trigger old(lctx).lock_id_set().contains((
                        id, KernelObjId::PageTable(pagetable_ptr)))]
                    old(lctx).lock_id_set().contains((
                        id, KernelObjId::PageTable(pagetable_ptr)))
                    ==> {
                        &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                        &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr)
                            == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                        &&& final(self).pt_mp.spec_index(pagetable_ptr)
                            == old(self).pt_mp.spec_index(pagetable_ptr)
                    },
                // Interleaving cannot acquire a lock on behalf of this
                // thread.  Preserve the lock-free state explicitly instead
                // of deriving it from an empty held-lock set plus alignment.
                old(self).all_objects_unlocked(old(lctx))
                    ==> final(self).all_objects_unlocked(final(lctx)),
                cpu_objects_unlocked(
                    old(self).cpu_arr, old(lctx).thread_id(),
                ) ==> cpu_objects_unlocked(
                    final(self).cpu_arr, final(lctx).thread_id(),
                ),
                forall|exceptions: Set<CpuId>|
                    #![trigger cpu_objects_unlocked_except(
                        old(self).cpu_arr, old(lctx).thread_id(), exceptions)]
                    cpu_objects_unlocked_except(
                        old(self).cpu_arr, old(lctx).thread_id(), exceptions,
                    ) ==> cpu_objects_unlocked_except(
                        final(self).cpu_arr, final(lctx).thread_id(), exceptions,
                    ),
                forall|exceptions: Set<PageIndex>|
                    #![trigger page_objects_unlocked_except(
                        old(self).pg_arr, old(lctx).thread_id(), exceptions)]
                    page_objects_unlocked_except(
                        old(self).pg_arr, old(lctx).thread_id(), exceptions,
                    ) ==> page_objects_unlocked_except(
                        final(self).pg_arr, final(lctx).thread_id(), exceptions,
                    ),
                forall|exceptions: Set<RwLockContainerPtr>|
                    #![trigger container_objects_unlocked_except(
                        old(self).ctn_mp, old(lctx).thread_id(), exceptions)]
                    container_objects_unlocked_except(
                        old(self).ctn_mp, old(lctx).thread_id(), exceptions)
                    ==> container_objects_unlocked_except(
                        final(self).ctn_mp, final(lctx).thread_id(), exceptions),
                forall|exceptions: Set<RwLockProcessPtr>|
                    #![trigger process_objects_unlocked_except(
                        old(self).prc_mp, old(lctx).thread_id(), exceptions)]
                    process_objects_unlocked_except(
                        old(self).prc_mp, old(lctx).thread_id(), exceptions)
                    ==> process_objects_unlocked_except(
                        final(self).prc_mp, final(lctx).thread_id(), exceptions),
                forall|exceptions: Set<RwLockThreadPtr>|
                    #![trigger thread_objects_unlocked_except(
                        old(self).thr_mp, old(lctx).thread_id(), exceptions)]
                    thread_objects_unlocked_except(
                        old(self).thr_mp, old(lctx).thread_id(), exceptions)
                    ==> thread_objects_unlocked_except(
                        final(self).thr_mp, final(lctx).thread_id(), exceptions),
                forall|exceptions: Set<RwLockPageTableRoot>|
                    #![trigger pagetable_objects_unlocked_except(
                        old(self).pt_mp, old(lctx).thread_id(), exceptions)]
                    pagetable_objects_unlocked_except(
                        old(self).pt_mp, old(lctx).thread_id(), exceptions)
                    ==> pagetable_objects_unlocked_except(
                        final(self).pt_mp, final(lctx).thread_id(), exceptions),
                forall|exceptions: Set<RwLockEndpointPtr>|
                    #![trigger endpoint_objects_unlocked_except(
                        old(self).ep_mp, old(lctx).thread_id(), exceptions)]
                    endpoint_objects_unlocked_except(
                        old(self).ep_mp, old(lctx).thread_id(), exceptions,
                    ) ==> endpoint_objects_unlocked_except(
                        final(self).ep_mp, final(lctx).thread_id(), exceptions,
                    ),
                forall|exceptions: Set<RwLockSchedulerPtr>|
                    #![trigger scheduler_objects_unlocked_except(
                        old(self).sched_mp, old(lctx).thread_id(), exceptions)]
                    scheduler_objects_unlocked_except(
                        old(self).sched_mp, old(lctx).thread_id(), exceptions,
                    ) ==> scheduler_objects_unlocked_except(
                        final(self).sched_mp, final(lctx).thread_id(), exceptions,
                    ),
                page_objects_unlocked(
                    old(self).pg_arr, old(lctx).thread_id(),
                ) ==> page_objects_unlocked(
                    final(self).pg_arr, final(lctx).thread_id(),
                ),
                container_objects_unlocked(
                    old(self).ctn_mp, old(lctx).thread_id())
                    ==> container_objects_unlocked(
                        final(self).ctn_mp, final(lctx).thread_id()),
                process_objects_unlocked(
                    old(self).prc_mp, old(lctx).thread_id())
                    ==> process_objects_unlocked(
                        final(self).prc_mp, final(lctx).thread_id()),
                thread_objects_unlocked(
                    old(self).thr_mp, old(lctx).thread_id())
                    ==> thread_objects_unlocked(
                        final(self).thr_mp, final(lctx).thread_id()),
                endpoint_objects_unlocked(
                    old(self).ep_mp, old(lctx).thread_id())
                    ==> endpoint_objects_unlocked(
                        final(self).ep_mp, final(lctx).thread_id()),
                pagetable_objects_unlocked(
                    old(self).pt_mp, old(lctx).thread_id())
                    ==> pagetable_objects_unlocked(
                        final(self).pt_mp, final(lctx).thread_id()),
                iommu_table_objects_unlocked(
                    old(self).it_mp, old(lctx).thread_id())
                    ==> iommu_table_objects_unlocked(
                        final(self).it_mp, final(lctx).thread_id()),
                scheduler_objects_unlocked(
                    old(self).sched_mp, old(lctx).thread_id())
                    ==> scheduler_objects_unlocked(
                        final(self).sched_mp, final(lctx).thread_id()),
                pcid_allocator_objects_unlocked(
                    old(self).pcid_allc_mp, old(lctx).thread_id())
                    ==> pcid_allocator_objects_unlocked(
                        final(self).pcid_allc_mp, final(lctx).thread_id()),
                allocator_objects_unlocked(
                    old(self).allc_4k_mp, old(lctx).thread_id())
                    ==> allocator_objects_unlocked(
                        final(self).allc_4k_mp, final(lctx).thread_id()),
                allocator_objects_unlocked(
                    old(self).allc_2m_mp, old(lctx).thread_id())
                    ==> allocator_objects_unlocked(
                        final(self).allc_2m_mp, final(lctx).thread_id()),
                allocator_objects_unlocked(
                    old(self).allc_1g_mp, old(lctx).thread_id())
                    ==> allocator_objects_unlocked(
                        final(self).allc_1g_mp, final(lctx).thread_id()),
                lock_id_aligned(final(self), final(lctx)),
                // Record this thread's completed section before refreshing the
                // snapshot to the post-interleaving projection.
                final(steps).steps == record_user_view_change(
                    old(steps).steps,
                    old(steps).snap_shot,
                    kernel_k_to_kernel_u(*old(self)),
                ),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                containers_rodata_unchanged(
                    old(self).ctn_mp, final(self).ctn_mp,
                ),
                processes_rodata_unchanged(
                    old(self).prc_mp, final(self).prc_mp,
                ),
                // The krnl lock state is the anchor: every object held
                // before interleaving is
                // still present and bit-for-bit unchanged afterwards.
                held_containers_unchanged(
                    old(self).ctn_mp, final(self).ctn_mp,
                    old(lctx)),
                held_processes_unchanged(
                    old(self).prc_mp, final(self).prc_mp,
                    old(lctx)),
                held_process_owning_containers_unchanged(
                    old(self).prc_mp, final(self).prc_mp,
                    old(self).ctn_mp, final(self).ctn_mp,
                    old(lctx)),
                held_threads_unchanged(
                    old(self).thr_mp, final(self).thr_mp,
                    old(lctx)),
                held_endpoints_unchanged(
                    old(self).ep_mp, final(self).ep_mp,
                    old(lctx)),
                held_schedulers_unchanged(
                    old(self).sched_mp, final(self).sched_mp,
                    old(lctx)),
                held_pcid_allocators_unchanged(
                    old(self).pcid_allc_mp, final(self).pcid_allc_mp,
                    old(lctx)),
                held_pagetables_unchanged(
                    old(self).pt_mp, final(self).pt_mp,
                    old(lctx)),
                held_iommu_tables_unchanged(
                    old(self).it_mp, final(self).it_mp,
                    old(lctx)),
                held_pages_unchanged(
                    old(self).pg_arr, final(self).pg_arr,
                    old(lctx)),
                held_cpus_unchanged(
                    old(self).cpu_arr, final(self).cpu_arr,
                    old(lctx)),
                held_allocator_objects_unchanged(
                    old(self).allc_4k_mp, final(self).allc_4k_mp,
                    old(lctx)),
                held_allocator_objects_unchanged(
                    old(self).allc_2m_mp, final(self).allc_2m_mp,
                    old(lctx)),
                held_allocator_objects_unchanged(
                    old(self).allc_1g_mp, final(self).allc_1g_mp,
                    old(lctx)),
                // Deliberately omitted from the old boundary contract:
                // - root/default-pagetable equality across interleaving;
                // Global rodata immutability and final lock-id alignment remain
                // explicit because both are common next-section framing facts.
        {
            unimplemented!()
        }
    }

    // ---- Held-lock / krnl-state alignment ----

    /// Exact object-sensitive mirror for the single held-lock ledger.
    #[verifier::opaque]
    pub open spec fn lock_id_aligned(k: &KernelK, lctx: &LocalContext) -> bool {
        forall|held: HeldLock|
            #![trigger lctx.lock_id_set().contains(held)]
            lctx.lock_id_set().contains(held) == {
                let id = held.0;
                match held.1 {
                    KernelObjId::Container(ptr) => {
                        &&& k.ctn_mp.dom().contains(ptr)
                        &&& k.ctn_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.ctn_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::Process(ptr) => {
                        &&& k.prc_mp.dom().contains(ptr)
                        &&& k.prc_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.prc_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::Thread(ptr) => {
                        &&& k.thr_mp.dom().contains(ptr)
                        &&& k.thr_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.thr_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::Endpoint(ptr) => {
                        &&& k.ep_mp.dom().contains(ptr)
                        &&& k.ep_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.ep_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::Scheduler(ptr) => {
                        &&& k.sched_mp.dom().contains(ptr)
                        &&& k.sched_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.sched_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::PcidAllocator(ptr) => {
                        &&& k.pcid_allc_mp.dom().contains(ptr)
                        &&& k.pcid_allc_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.pcid_allc_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::PageTable(ptr) => {
                        &&& k.pt_mp.dom().contains(ptr)
                        &&& k.pt_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.pt_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::IommuTable(ptr) => {
                        &&& k.it_mp.dom().contains(ptr)
                        &&& k.it_mp.spec_index(ptr).locked_by_thread(lctx.thread_id())
                        &&& id == k.it_mp.lock_id_by_key(ptr)
                    },
                    KernelObjId::Page(index) => {
                        &&& index_valid(NUM_PAGES, index)
                        &&& k.pg_arr.spec_index(index).view().locked_by_thread(lctx.thread_id())
                        &&& id == k.pg_arr.lock_id_by_index(index)
                    },
                    KernelObjId::Cpu(cpu_id) => {
                        &&& index_valid(NUM_CPUS, cpu_id)
                        &&& k.cpu_arr.spec_index(cpu_id).view().locked_by_thread(lctx.thread_id())
                        &&& id == k.cpu_arr.lock_id_by_index(cpu_id)
                    },
                    KernelObjId::AllocatorQuota(size, ptr) => match size {
                        PageSize::SZ4k => {
                            &&& k.allc_4k_mp.dom().contains(ptr)
                            &&& k.allc_4k_mp.spec_index(ptr).quota.locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_4k_mp.spec_index(ptr).quota.lock_id()
                        },
                        PageSize::SZ2m => {
                            &&& k.allc_2m_mp.dom().contains(ptr)
                            &&& k.allc_2m_mp.spec_index(ptr).quota.locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_2m_mp.spec_index(ptr).quota.lock_id()
                        },
                        PageSize::SZ1g => {
                            &&& k.allc_1g_mp.dom().contains(ptr)
                            &&& k.allc_1g_mp.spec_index(ptr).quota.locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_1g_mp.spec_index(ptr).quota.lock_id()
                        },
                    },
                    KernelObjId::AllocatorCache(size, ptr, cpu_id) => match size {
                        PageSize::SZ4k => {
                            &&& k.allc_4k_mp.dom().contains(ptr)
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& k.allc_4k_mp.spec_index(ptr).cpu_caches.spec_index(cpu_id).view()
                                .locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_4k_mp.spec_index(ptr).cpu_caches.lock_id_by_index(cpu_id)
                        },
                        PageSize::SZ2m => {
                            &&& k.allc_2m_mp.dom().contains(ptr)
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& k.allc_2m_mp.spec_index(ptr).cpu_caches.spec_index(cpu_id).view()
                                .locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_2m_mp.spec_index(ptr).cpu_caches.lock_id_by_index(cpu_id)
                        },
                        PageSize::SZ1g => {
                            &&& k.allc_1g_mp.dom().contains(ptr)
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& k.allc_1g_mp.spec_index(ptr).cpu_caches.spec_index(cpu_id).view()
                                .locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_1g_mp.spec_index(ptr).cpu_caches.lock_id_by_index(cpu_id)
                        },
                    },
                    KernelObjId::AllocatorGlobalPoll(size, ptr) => match size {
                        PageSize::SZ4k => {
                            &&& k.allc_4k_mp.dom().contains(ptr)
                            &&& k.allc_4k_mp.spec_index(ptr).global_pool.locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_4k_mp.spec_index(ptr).global_pool.lock_id()
                        },
                        PageSize::SZ2m => {
                            &&& k.allc_2m_mp.dom().contains(ptr)
                            &&& k.allc_2m_mp.spec_index(ptr).global_pool.locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_2m_mp.spec_index(ptr).global_pool.lock_id()
                        },
                        PageSize::SZ1g => {
                            &&& k.allc_1g_mp.dom().contains(ptr)
                            &&& k.allc_1g_mp.spec_index(ptr).global_pool.locked_by_thread(lctx.thread_id())
                            &&& id == k.allc_1g_mp.spec_index(ptr).global_pool.lock_id()
                        },
                    },
                }
            }
    }

pub proof fn enter_kernel_view_release_preserving_lock_id_alignment(
    krnl: &KernelK,
    tracked lctx: &mut LocalContext,
)
    requires
        old(lctx).kernel_view_locking_state() is Acquire,
        lock_id_aligned(krnl, old(lctx)),
    ensures
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        lock_id_aligned(krnl, final(lctx)),
{
    lctx.enter_kernel_view_release();
    assert(lock_id_aligned(krnl, &*lctx)) by {
        reveal(lock_id_aligned);
    };
}

}

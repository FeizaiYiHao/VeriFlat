use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {

    pub type PageTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>;
    pub type IommuTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>;
    pub type PageLockedArray = LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>;
    pub type CpuLockedArray = LockedArray<Cpu, (), (), NUM_CPUS, CPU_HAS_KILL_STATE>;
    pub type ContainerLockedMap = LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhost, CONTAINER_HAS_KILL_STATE>;
    pub type SchedulerLockedMap = LockedMap<RwLockSchedulerPtr, Scheduler, (), (), SCHEDULER_HAS_KILL_STATE>;
    pub type CpuSetLockedMap = LockedMap<RwLockCpuSetPtr, CpuSet, (), (), CPU_SET_HAS_KILL_STATE>;
    pub type PcidAllocatorLockedMap = LockedMap<RwLockPcidAllocatorPtr, PcidAllocator, (), (), PCID_ALLOCATOR_HAS_KILL_STATE>;
    pub type EndpointLockedMap = LockedMap<RwLockEndpointPtr, Endpoint, (), (), ENDPOINT_HAS_KILL_STATE>;
    pub type PageAllocatorUnLockedMap = UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>;
    pub type ProcessLockedMap = LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, ProcessGhost, PROCESS_HAS_KILL_STATE>;
    pub struct KernelK{
        pub pt_mp: PageTableLockedMap,
        pub it_mp: IommuTableLockedMap,
        pub irt: IommuRootTable,
        pub pg_arr: PageLockedArray,
        pub cpu_arr: CpuLockedArray,
        pub pcid_needflush: PcidNeedFlushArray,
        pub cpu_published: CpuPublishedArray,
        pub ctn_mp: ContainerLockedMap,
        pub sched_mp: SchedulerLockedMap,
        pub pcid_allc_mp: PcidAllocatorLockedMap,
        pub cpu_set_mp: CpuSetLockedMap,
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
            &&& pcid_needflush_wf(self.pcid_needflush)
            &&& cpu_published_wf(self.cpu_published, self.cpu_arr, self.pcid_needflush)
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
            cpu_set_perms_wf(self.cpu_set_mp)
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
            scheduler_pages_wf(self.sched_mp, self.pg_arr)
            &&&
            cpu_set_pages_wf(self.cpu_set_mp, self.pg_arr)
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
            self.ctn_mp.spec_index(self.rt_ctn).view().root_process_in_processes()
            &&&
            container_process_wf(self.ctn_mp, self.prc_mp)
            &&&
            per_container_process_tree_wf(self.ctn_mp, self.prc_mp)
            &&&
            container_endpoint_wf(self.ctn_mp, self.ep_mp)
            &&&
            container_cpu_wf(self.ctn_mp, self.cpu_set_mp, self.cpu_arr)
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
            container_cpu_set_wf(self.ctn_mp, self.cpu_set_mp)
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
            cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)
            &&&
            tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr, self.pcid_needflush)
        }

        #[verifier::opaque]
        pub open spec fn default_pagetable_wf(&self) -> bool {
            &&&
            self.dflt_pt.view().inv()
            &&&
            self.dflt_pt.view().pcid_value() == KERNEL_DEFAULT_PCID
            &&&
            self.dflt_pt.view().is_empty()
            &&&
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger self.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end]
                self.pt_mp.dom().contains(pagetable_ptr)
                ==> self.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == self.dflt_pt.view().kernel_l4_end
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
        ///     their state across the boundary — `view`, `view_ghost`,
        ///     `view_rodata`, `locking_thread`,
        ///     `being_killed` are preserved per held lock instance;
        ///   - the local CPU's hardware CR3/PCID and published atomic value stay
        ///     unchanged even without its CPU lock;
        ///   - needflush entries are independent of the CPU lock: only entries
        ///     held in the typed needflush map are preserved;
        ///   - held page tables cannot acquire stale translations after their
        ///     present-submap condition has been established. Rebinding a PCID
        ///     or ending its deferred-flush exemption establishes that condition;
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
        ///   - `typed_lock_maps_aligned(self, lctx)` and
        ///     `lock_id_set_aligned(lctx)` (physical locks, typed entries, and
        ///     exact ordering pairs agree),
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
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                    &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                    &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                    &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
                },
                final(self).inv(),
                final(lctx).kernel_view_locking_state() is Acquire,
                // LocalContext is thread-local: the phase flips to Acquire,
                // while its identity and exact held-lock set stay put.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).lock_id_set() == old(lctx).lock_id_set(),
                typed_lock_maps_unchanged(old(lctx), final(lctx)),
                forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                    old(lctx).pagetable_lock_map().dom().contains(pt)
                    && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
                forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                    #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                    old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                    && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                    ==> {
                        let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                        let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                        after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                        && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                            || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                            || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                                && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                                && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                        ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                    },
                forall|cpu_id: CpuId, pcid: Pcid|
                    #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                    old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                    ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k) ==> final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m) ==> final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g) ==> final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|major: LockMajorId|
                    #![trigger old(lctx).held_lock_majors_lt(major)]
                    old(lctx).held_lock_majors_lt(major) ==> final(lctx).held_lock_majors_lt(major),
                // Direct typed-map framing for owner objects.
                forall|cpu_id: CpuId|
                    #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                    old(lctx).cpu_lock_map().dom().contains(cpu_id)
                    ==> final(self).cpu_arr.spec_index(cpu_id).view()
                        == old(self).cpu_arr.spec_index(cpu_id).view(),
                forall|container_ptr: RwLockContainerPtr|
                    #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                    old(lctx).container_lock_map().dom().contains(container_ptr)
                    ==> {
                        &&& final(self).ctn_mp.dom().contains(container_ptr)
                        &&& final(self).ctn_mp.lock_id_by_key(container_ptr)
                            == old(self).ctn_mp.lock_id_by_key(container_ptr)
                        &&& final(self).ctn_mp.spec_index(container_ptr)
                            == old(self).ctn_mp.spec_index(container_ptr)
                    },
                forall|process_ptr: RwLockProcessPtr|
                    #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                    old(lctx).process_lock_map().dom().contains(process_ptr)
                    ==> {
                        &&& final(self).prc_mp.dom().contains(process_ptr)
                        &&& final(self).prc_mp.lock_id_by_key(process_ptr)
                            == old(self).prc_mp.lock_id_by_key(process_ptr)
                        &&& final(self).prc_mp.spec_index(process_ptr)
                            == old(self).prc_mp.spec_index(process_ptr)
                    },
                forall|thread_ptr: RwLockThreadPtr|
                    #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                    old(lctx).thread_lock_map().dom().contains(thread_ptr)
                    ==> {
                        &&& final(self).thr_mp.dom().contains(thread_ptr)
                        &&& final(self).thr_mp.lock_id_by_key(thread_ptr)
                            == old(self).thr_mp.lock_id_by_key(thread_ptr)
                        &&& final(self).thr_mp.spec_index(thread_ptr)
                            == old(self).thr_mp.spec_index(thread_ptr)
                    },
                forall|pagetable_ptr: RwLockPageTableRoot|
                    #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                    old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                    ==> {
                        &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                        &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr)
                            == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                        &&& final(self).pt_mp.spec_index(pagetable_ptr)
                            == old(self).pt_mp.spec_index(pagetable_ptr)
                    },
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // Record this thread's completed section before refreshing the
                // snapshot to the post-interleaving projection.
                final(steps).steps == record_user_view_change(
                    old(steps).steps,
                    old(steps).snap_shot,
                    kernel_k_to_kernel_u(*old(self)),
                ),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                final(self).dflt_pt == old(self).dflt_pt,
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
                held_cpu_sets_unchanged(
                    old(self).cpu_set_mp, final(self).cpu_set_mp,
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
                    old(lctx), PageSize::SZ4k),
                held_allocator_objects_unchanged(
                    old(self).allc_2m_mp, final(self).allc_2m_mp,
                    old(lctx), PageSize::SZ2m),
                held_allocator_objects_unchanged(
                    old(self).allc_1g_mp, final(self).allc_1g_mp,
                    old(lctx), PageSize::SZ1g),
                // Deliberately omitted from the old boundary contract:
                // - root-container equality across interleaving;
                // The default page table is read-only and is framed directly.
                // Global rodata immutability and final lock-id alignment remain
                // explicit because both are common next-section framing facts.
        {
            unimplemented!()
        }
    }

    // ---- Held-lock / krnl-state alignment ----

    pub open spec fn typed_lock_maps_aligned(k: &KernelK, lctx: &LocalContext) -> bool {
        &&& k.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())
        &&& k.cpu_arr.typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id())
        &&& k.pcid_needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id())
        &&& (forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write)]
            typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write)
            ==> k.pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == Some(lctx.cpu_id()))
        &&& k.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
        &&& k.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())
        &&& k.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())
        &&& k.ep_mp.typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id())
        &&& k.sched_mp.typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id())
        &&& k.pcid_allc_mp.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())
        &&& k.cpu_set_mp.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id())
        &&& k.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())
        &&& k.it_mp.typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id())
        &&& k.allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id())
        &&& k.allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id())
        &&& k.allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id())
        &&& k.allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id())
        &&& k.allc_2m_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id())
        &&& k.allc_2m_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id())
        &&& k.allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id())
        &&& k.allc_1g_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_1g_lock_map(), lctx.thread_id())
        &&& k.allc_1g_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id())
    }

pub proof fn enter_kernel_view_release_preserving_lock_alignments(
    krnl: &KernelK,
    tracked lctx: &mut LocalContext,
)
    requires
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(krnl, old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_maps_aligned(krnl, final(lctx)),
        lock_id_set_aligned(final(lctx)),
        krnl.all_objects_unlocked(final(lctx)) == krnl.all_objects_unlocked(old(lctx)),
{
    lctx.enter_kernel_view_release();
    assert(krnl.all_objects_unlocked(lctx) == krnl.all_objects_unlocked(old(lctx))) by { reveal(KernelK::all_objects_unlocked); };
}

}

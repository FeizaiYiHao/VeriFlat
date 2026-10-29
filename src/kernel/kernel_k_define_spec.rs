#[cfg(verus_keep_ghost)]
use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {
    pub type PageTableLockedMap = LockedMap<RwLockPageTableRoot, PageTableHigher<PT_TYPE>, (), PageTableLower<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>;
    pub type PageTableLowerMap = Map<RwLockPageTableRoot, PageTableLower<PT_TYPE>>;
    pub type IommuTableLockedMap = LockedMap<RwLockPageTableRoot, PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>;
    pub type PageLockedArray = LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>;
    pub type CpuLockedArray = LockedArray<Cpu, (), Option<CpuId>, NUM_CPUS, CPU_HAS_KILL_STATE>;
    pub type ContainerLockedMap = LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhost, CONTAINER_HAS_KILL_STATE>;
    pub type CpuSetLockedMap = LockedMap<RwLockCpuSetPtr, CpuSet, (), (), CPU_SET_HAS_KILL_STATE>;
    pub type PcidAllocatorLockedMap = LockedMap<RwLockPcidAllocatorPtr, PcidAllocator, (), (), PCID_ALLOCATOR_HAS_KILL_STATE>;
    pub type EndpointLockedMap = LockedMap<RwLockEndpointPtr, Endpoint, (), (), ENDPOINT_HAS_KILL_STATE>;
    pub type PageAllocatorUnLockedMap<const SIZE: usize> = UnLockedMap<RwLockPageAllocatorPtr, PageAllocator<SIZE>>;
    pub type ProcessLockedMap = LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, ProcessGhost, PROCESS_HAS_KILL_STATE>;
    // `irt` leads the layout (`init.rs` pins its offset); `repr(C)` keeps that independent of lock-word niches.
    #[repr(C)]
    pub struct KernelK{
        pub irt: IommuRootTableLock,
        pub pt_mp: PageTableLockedMap,
        pub pt_lower: Tracked<PageTableLowerMap>,
        pub it_mp: IommuTableLockedMap,
        pub pg_arr: PageLockedArray,
        pub cpu_arr: CpuLockedArray,
        pub pcid_needflush: PcidNeedFlushArray,
        pub cpu_offline_mp: CpuOfflineFlagsUnLockedMap,
        pub cpu_hw_cr3_pcid: CpuHwCr3PcidArray,
        pub cpu_op: Tracked<CpuOpArray>,
        pub ctn_mp: ContainerLockedMap,
        pub sched_mp: SchedulerUnLockedMap,
        pub pcid_allc_mp: PcidAllocatorLockedMap,
        pub cpu_set_mp: CpuSetLockedMap,
        pub prc_mp: ProcessLockedMap,
        pub thr_mp: ThreadLockedMap,
        pub ep_mp: EndpointLockedMap,
        pub allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>,
        pub allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
        pub allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>,
        pub cpu_tlb: CpuTLB,
        pub iommu_tlb: IommuTLB,

        pub rt_ctn: RwLockContainerPtr, // Never dies

        pub dflt_pt: ReadOnlyNode<PageTable<PT_TYPE>>, // Read only
    }

    impl KernelK{
        /// all spec functions under this are open
        pub open spec fn subsystems_inv(&self) -> bool {
            &&& self.default_pagetable_wf()
            &&& pagetable_perms_wf(self.pt_mp)
            &&& pagetable_lower_wf(self.pt_mp, self.pt_lower.view())
            &&& pagetable_window_holders_hold_pagetable(self.pt_mp, self.pt_lower.view())
            &&& pagetable_lower_backup_wf(self.pt_mp, self.pt_lower.view())
            &&& pagetable_hidden_leaves_only_when_locked(self.pt_mp, self.pt_lower.view())
            &&& pagetable_window_stale_cpus_only_when_locked(self.pt_mp, self.pt_lower.view())
            &&& iommu_table_perms_wf(self.it_mp)
            &&& self.irt.inv()
            &&& page_array_wf(self.pg_arr)
            &&& cpu_array_wf(self.cpu_arr, self.dflt_pt.view())
            &&& pcid_needflush_wf(self.pcid_needflush)
            &&& cpu_offline_flags_wf(self.cpu_offline_mp, self.cpu_arr)
            &&& cpu_hw_cr3_pcid_wf(self.cpu_hw_cr3_pcid, self.cpu_arr, self.pcid_needflush)
            &&& self.cpu_op.view().view().len() == NUM_CPUS
            &&& cpu_op_wf(self.cpu_op.view().view(), self.cpu_arr)
            &&& self.cpu_tlb.inv()
            &&& self.iommu_tlb.inv()
            &&& container_perms_wf(self.ctn_mp)
            &&& process_perms_wf(self.prc_mp)
            &&& thread_perms_wf(self.thr_mp)
            &&& scheduler_perms_wf(self.sched_mp)
            &&& cpu_set_perms_wf(self.cpu_set_mp)
            &&& pcid_allocator_perms_wf(self.pcid_allc_mp)
            &&& endpoint_perms_wf(self.ep_mp)
            &&& allocator_perms_wf(self.allc_4k_mp)
            &&& allocator_perms_wf(self.allc_2m_mp)
            &&& allocator_perms_wf(self.allc_1g_mp)
        }

        pub open spec fn memory_management_inv(&self) -> bool {
            &&& allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&& container_page_owner_wf(self.ctn_mp, self.pg_arr)
            &&& hugepage_2m_wf(self.pg_arr)
            &&& hugepage_1g_wf(self.pg_arr)
            &&& page_pagetable_wf(self.pt_mp, self.pt_lower.view(), self.pg_arr)
            &&& container_process_page_pagetable_wf(self.ctn_mp, self.prc_mp, self.pt_mp, self.pg_arr)
            &&& page_iommu_table_wf(self.ctn_mp, self.prc_mp, self.it_mp, self.pg_arr)
            &&& container_pages_wf(self.pg_arr, self.ctn_mp)
            &&& process_pages_wf(self.pg_arr, self.prc_mp)
            &&& pagetable_pages_wf(self.pt_mp, self.pt_lower.view(), self.pg_arr)
            &&& iommu_table_pages_wf(self.it_mp, self.pg_arr)
            &&& thread_pages_wf(self.thr_mp, self.pg_arr)
            &&& scheduler_pages_wf(self.sched_mp, self.pg_arr)
            &&& cpu_set_pages_wf(self.cpu_set_mp, self.pg_arr)
            &&& pcid_allocator_pages_wf(self.pg_arr, self.pcid_allc_mp)
            &&& thread_staged_pages_wf(self.thr_mp, self.pg_arr)
            &&& endpoint_pages_wf(self.ep_mp, self.pg_arr)
            &&& process_pagetable_match(self.prc_mp, self.pt_mp)
            &&& process_iommu_table_match(self.prc_mp, self.it_mp)
            &&& pagetable_no_huge_leaf_wf(self.pt_mp, self.pt_lower.view(), self.it_mp)
            &&& process_emptied_tables_wf(self.prc_mp, self.pt_mp, self.pt_lower.view(), self.it_mp)
            &&& process_kernel_pages_owner_wf(self.pg_arr, self.prc_mp, self.pt_mp, self.it_mp)
            &&& page_object_owner_wf(self.pg_arr, self.ctn_mp, self.thr_mp)
            &&& self.allocator_free_pages_wf()
            &&& container_process_allocator_quota_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&& container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&& container_kill_retire_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)
            &&& container_allocator_free_4k_page_wf(self.allc_4k_mp, self.pg_arr)
            &&& container_allocator_free_2m_page_wf(self.allc_2m_mp, self.pg_arr)
            &&& container_allocator_free_1g_page_wf(self.allc_1g_mp, self.pg_arr)
        }

        pub open spec fn process_management_inv(&self) -> bool {
            &&& container_tree_wf(self.rt_ctn, self.ctn_mp)
            &&& self.ctn_mp.spec_index(self.rt_ctn).view_ghost().owned_processes.view().contains(self.ctn_mp.spec_index(self.rt_ctn).view().root_process)
            &&& container_process_wf(self.ctn_mp, self.prc_mp)
            &&& per_container_process_tree_wf(self.ctn_mp, self.prc_mp)
            &&& process_kill_mark_wf(self.ctn_mp, self.prc_mp)
            &&& container_kill_mark_wf(self.ctn_mp, self.prc_mp)
            &&& cpu_set_kill_mark_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp)
            &&& process_state_lock_wf(self.prc_mp)
            &&& container_endpoint_wf(self.ctn_mp, self.ep_mp)
            &&& container_cpu_wf(self.ctn_mp, self.cpu_set_mp, self.cpu_arr)
            &&& thread_endpoint_ref_counter_wf(self.thr_mp, self.ep_mp)
            &&& thread_endpoint_queue_wf(self.thr_mp, self.ep_mp)
            &&& thread_caller_callee_wf(self.thr_mp)
            &&& container_thread_endpoint_wf(self.ctn_mp, self.thr_mp, self.ep_mp)
            &&& container_scheduler_wf(self.ctn_mp, self.sched_mp)
            &&& container_cpu_set_wf(self.ctn_mp, self.cpu_set_mp)
            &&& container_cpu_offline_flags_wf(self.ctn_mp, self.cpu_offline_mp)
            &&& container_pcid_allocator_wf(self.ctn_mp, self.pcid_allc_mp)
            &&& process_pcid_allocator_wf(self.ctn_mp, self.prc_mp, self.pcid_allc_mp)
            &&& container_thread_scheduler_wf(self.ctn_mp, self.thr_mp, self.sched_mp)
            &&& container_thread_wf(self.ctn_mp, self.thr_mp)
            &&& process_cpu_wf(self.prc_mp, self.cpu_arr)
            &&& process_thread_wf(self.prc_mp, self.thr_mp)
            &&& process_emptied_threads_wf(self.prc_mp, self.thr_mp)
            &&& thread_cpu_wf(self.thr_mp, self.cpu_arr)
            &&& thread_dangling_chain_end_wf(self.thr_mp)
        }
        /// All spec functions under this are closed
        pub open spec fn inv(&self) -> bool {
            &&& self.subsystems_inv()
            &&& self.memory_management_inv()
            &&& self.process_management_inv()
            &&& iommu_root_table_process_wf(self.irt.view(), self.prc_mp, self.it_mp)
            &&& process_pci_function_ownership_wf(self.irt.view(), self.prc_mp)
            &&& iommu_tlb_wf_spec(self.iommu_tlb, self.irt.view(), self.prc_mp, self.it_mp)
            // TLB spec
            &&& cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)
            &&& tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.pt_lower.view(), self.cpu_arr, self.pcid_needflush)
        }

        #[verifier::opaque]
        pub open spec fn default_pagetable_wf(&self) -> bool {
            &&& self.dflt_pt.view().inv()
            &&& self.dflt_pt.view().pcid_value() == KERNEL_DEFAULT_PCID
            &&& self.dflt_pt.view().is_empty()
            &&& self.dflt_pt.view().kernel_l4_end == KERNEL_MEM_END_L4INDEX
            &&& forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger self.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end]
                self.pt_mp.dom().contains(pagetable_ptr) ==> self.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == self.dflt_pt.view().kernel_l4_end
        }

        pub proof fn default_pagetable_view_inv(&self)
            requires self.default_pagetable_wf()
            ensures
                self.dflt_pt.view().inv(),
                page_ptr_valid(self.dflt_pt.view().cr3),
        { reveal(KernelK::default_pagetable_wf); self.dflt_pt.view().table_pages_wf_cr3_at(); }

        /// Page table `pagetable_ptr` shares the default table's kernel L4 range end, `KERNEL_MEM_END_L4INDEX`.
        pub proof fn default_pagetable_wf_at(&self, pagetable_ptr: RwLockPageTableRoot)
            requires
                self.default_pagetable_wf(),
                self.pt_mp.dom().contains(pagetable_ptr),
            ensures
                self.dflt_pt.view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
                self.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == self.dflt_pt.view().kernel_l4_end,
        { reveal(KernelK::default_pagetable_wf); }

        pub open spec fn allocator_free_pages_wf(&self) -> bool {
            &&& allocator_free_page_ptrs_wf(self.allc_4k_mp)
            &&& allocator_free_page_ptrs_wf(self.allc_2m_mp)
            &&& allocator_free_page_ptrs_wf(self.allc_1g_mp)
        }

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
        /// arbitrary atomic sections. `kernel_step_boundary_framing` states what
        /// survives them:
        ///   - all our held objects (those recorded in the LocalContext set) keep
        ///     their state across the boundary — `view`, `view_ghost`,
        ///     `view_rodata`, `locking_thread`,
        ///     `being_killed` are preserved per held lock instance, except that a
        ///     read-held page table keeps only its payload, this thread's read hold,
        ///     and its kill mark;
        ///   - each held 2M window keeps its L2 entry, lock owner, linked L1 page,
        ///     and leaves; nothing is said about the window half of a page table
        ///     beyond its held windows;
        ///   - while the local cpu is inside a kernel step (this thread holds it),
        ///     its hardware cr3/pcid word stays unchanged; its running state stays
        ///     put or drops to Idle (a killer's running-to-idle IPI, a wake IPI);
        ///   - owners of held objects keep their read-only data: their pointers
        ///     cannot be freed and reused between sections;
        ///   - needflush entries are independent of the CPU lock: only entries
        ///     held in the typed needflush map are preserved;
        ///   - everything else may change arbitrarily, including map
        ///     domains (except for the fixed-size arrays `cpu_array` and
        ///     `page_array`);
        ///   - the krnl invariant `inv()` is re-established by trust.
        /// Outside that framing, the LocalContext held-lock set is unchanged (we
        /// still hold what we held), and the krnl-view phase flips back to
        /// `Acquire`, ready for the next atomic section.
        ///
        /// Before interleaving, the boundary compares the completed krnl
        /// section's user projection with `steps.snapshot_u()`.  A changed
        /// projection is appended as one user step; an unchanged projection is
        /// an internal stuttering step and is omitted.  Only then may other
        /// threads interleave, after which the snapshot is refreshed.
        ///
        /// Preconditions:
        ///   - `inv()` holds (we entered the boundary in a wf state),
        ///   - `kernel_view_locking_state is Release` (the current section
        ///     is done),
        ///   - `typed_lock_maps_aligned(self, lctx)` (physical locks and typed
        ///     entries agree),
        /// TCB maintenance rule: do not change this function's signature,
        /// contract, triggers, or body, or the body of `kernel_step_boundary_framing`,
        /// without the user's explicit approval.
        ///
        #[verifier::external_body]
        pub(super) proof fn kernel_step_boundary_raw(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps)
            requires
                old(self).inv(),
                old(lctx).kernel_view_locking_state() is Release,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(lctx).kernel_view_locking_state() is Acquire,
                // LocalContext is thread-local: the phase flips to Acquire,
                // while its identity and exact held-lock set stay put.
                final(lctx).thread_id() == old(lctx).thread_id(),
                typed_lock_maps_unchanged(old(lctx), final(lctx)),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k) ==> final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m) ==> final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g) ==> final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|major: LockMajorId| #![trigger old(lctx).held_lock_majors_lt(major)] old(lctx).held_lock_majors_lt(major) ==> final(lctx).held_lock_majors_lt(major),
                typed_lock_maps_aligned(final(self), final(lctx)),
                // Record this thread's completed section before refreshing the
                // snapshot to the post-interleaving projection.
                final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
                final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
                final(steps).snapshot_k() == *final(self),
        {
            unimplemented!()
        }
    }

    /// What the trusted step boundary `KernelK::kernel_step_boundary_raw` keeps from `pre` to `post` for the thread whose
    /// local context across the boundary is `lctx`: the local cpu's hardware cr3/pcid word while that cpu is inside a
    /// kernel step, and its running state unless an IPI drops it to Idle, the re-established invariant, every object
    /// `lctx` holds, lock-id alignment, the default page table, and the read-only data of the owners of held objects.
    /// Part of the boundary's TCB contract.
    pub open spec fn kernel_step_boundary_framing(pre: KernelK, post: KernelK, lctx: LocalContext) -> bool {
        &&& index_valid(NUM_CPUS, lctx.cpu_id()) ==> {
            let own = lctx.cpu_id() as int;
            &&& pre.cpu_op.view().view()[own] is InStep ==> post.cpu_hw_cr3_pcid[own].view() == pre.cpu_hw_cr3_pcid[own].view()
            &&& post.cpu_op.view().view()[own] == pre.cpu_op.view().view()[own] || post.cpu_op.view().view()[own] is Idle
        }
        &&& post.inv()
        &&& forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger lctx.pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
            lctx.pcid_needflush_lock_map().dom().contains((cpu_id, pcid)) ==> post.pcid_needflush.spec_index(cpu_id, pcid) == pre.pcid_needflush.spec_index(cpu_id, pcid)
        // Direct typed-map framing for owner objects.
        &&& forall|cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(cpu_id)] lctx.cpu_lock_map().dom().contains(cpu_id) ==> post.cpu_arr.spec_index(cpu_id).view() == pre.cpu_arr.spec_index(cpu_id).view()
        // A held remote cpu that runs a thread may still trap, return to user mode, or divert to its idle loop once
        // marked; every other held cpu keeps its running state.
        &&& forall|cpu_id: CpuId|
            #![trigger lctx.cpu_lock_map().dom().contains(cpu_id)]
            lctx.cpu_lock_map().dom().contains(cpu_id) ==> {
                let op = post.cpu_op.view().view()[cpu_id as int];
                if cpu_id != lctx.cpu_id() && pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running {
                    op is User || op is Trap || (op is Idle && pre.cpu_arr.spec_index(cpu_id).view().being_killed())
                } else {
                    op == pre.cpu_op.view().view()[cpu_id as int]
                }
            }
        &&& forall|container_ptr: RwLockContainerPtr|
            #![trigger lctx.container_lock_map().dom().contains(container_ptr)]
            lctx.container_lock_map().dom().contains(container_ptr) ==> {
                &&& post.ctn_mp.dom().contains(container_ptr)
                &&& post.ctn_mp.lock_id_by_key(container_ptr) == pre.ctn_mp.lock_id_by_key(container_ptr)
                &&& post.ctn_mp.spec_index(container_ptr) == pre.ctn_mp.spec_index(container_ptr)
            }
        &&& forall|process_ptr: RwLockProcessPtr|
            #![trigger lctx.process_lock_map().dom().contains(process_ptr)]
            lctx.process_lock_map().dom().contains(process_ptr) ==> {
                &&& post.prc_mp.dom().contains(process_ptr)
                &&& post.prc_mp.lock_id_by_key(process_ptr) == pre.prc_mp.lock_id_by_key(process_ptr)
                &&& post.prc_mp.spec_index(process_ptr) == pre.prc_mp.spec_index(process_ptr)
            }
        &&& forall|thread_ptr: RwLockThreadPtr|
            #![trigger lctx.thread_lock_map().dom().contains(thread_ptr)]
            lctx.thread_lock_map().dom().contains(thread_ptr) ==> {
                &&& post.thr_mp.dom().contains(thread_ptr)
                &&& post.thr_mp.lock_id_by_key(thread_ptr) == pre.thr_mp.lock_id_by_key(thread_ptr)
                &&& post.thr_mp.spec_index(thread_ptr) == pre.thr_mp.spec_index(thread_ptr)
            }
        &&& forall|pagetable_ptr: RwLockPageTableRoot|
            #![trigger lctx.pagetable_lock_map().dom().contains(pagetable_ptr)]
            lctx.pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                &&& post.pt_mp.dom().contains(pagetable_ptr)
                &&& post.pt_mp.lock_id_by_key(pagetable_ptr) == pre.pt_mp.lock_id_by_key(pagetable_ptr)
                &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
                    ==> post.pt_mp.spec_index(pagetable_ptr) == pre.pt_mp.spec_index(pagetable_ptr)
                &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                    &&& post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view()
                    &&& post.pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(lctx.thread_id())
                    &&& post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed()
                    &&& post.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.spec_index(lctx.thread_id()) == pre.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.spec_index(lctx.thread_id())
                }
            }
        // Deliberately omitted: root-container equality across interleaving, and rodata of objects that are neither held
        // nor owners of held objects, whose pointers may be freed and reused. The default page table is read-only and is
        // framed directly. Final lock-id alignment remains explicit because it is a common next-section framing fact.
        &&& typed_lock_maps_aligned(&post, &lctx)
        &&& post.dflt_pt == pre.dflt_pt
        &&& held_owner_rodata_unchanged(pre, post, lctx)
        // The krnl lock state is the anchor: every object held before interleaving is still present and bit-for-bit
        // unchanged afterwards.
        &&& held_containers_unchanged(pre.ctn_mp, post.ctn_mp, &lctx)
        &&& held_processes_unchanged(pre.prc_mp, post.prc_mp, &lctx)
        &&& held_threads_unchanged(pre.thr_mp, post.thr_mp, &lctx)
        &&& held_endpoints_unchanged(pre.ep_mp, post.ep_mp, &lctx)
        &&& held_schedulers_unchanged(pre.sched_mp, post.sched_mp, &lctx)
        &&& held_pcid_allocators_unchanged(pre.pcid_allc_mp, post.pcid_allc_mp, &lctx)
        &&& held_cpu_sets_unchanged(pre.cpu_set_mp, post.cpu_set_mp, &lctx)
        &&& held_pagetables_unchanged(pre.pt_mp, post.pt_mp, &lctx)
        &&& held_pagetable_windows_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), &lctx)
        &&& held_iommu_tables_unchanged(pre.it_mp, post.it_mp, &lctx)
        &&& held_iommu_root_table_unchanged(pre.irt, post.irt, &lctx)
        &&& held_pages_unchanged(pre.pg_arr, post.pg_arr, &lctx)
        &&& held_cpus_unchanged(pre.cpu_arr, post.cpu_arr, &lctx)
        &&& held_allocator_objects_unchanged(pre.allc_4k_mp, post.allc_4k_mp, &lctx, PageSize::SZ4k)
        &&& held_allocator_objects_unchanged(pre.allc_2m_mp, post.allc_2m_mp, &lctx, PageSize::SZ2m)
        &&& held_allocator_objects_unchanged(pre.allc_1g_mp, post.allc_1g_mp, &lctx, PageSize::SZ1g)
        // A write holder's hidden leaves are never re-cached (`CAP.CM = 0`); the attached domains of its table may only gain present translations.
        &&& forall|it: RwLockPageTableRoot| #![trigger lctx.iommu_table_lock_map().dom().contains(it)]
            typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), it, TypedLockMode::Write) && iommu_table_tlb_entries_present(pre.iommu_tlb, pre.irt.view(), pre.it_mp, it)
                ==> iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, it)
    }

    /// The step-boundary framing composes for one thread, provided the thread holds its own cpu whenever that cpu is
    /// inside a kernel step at `a`: only then does the cpu stay inside the step, keeping its hardware cr3/pcid word, at `b`.
    pub proof fn kernel_step_boundary_framing_trans(a: KernelK, b: KernelK, c: KernelK, lctx: LocalContext)
        requires
            kernel_step_boundary_framing(a, b, lctx),
            kernel_step_boundary_framing(b, c, lctx),
            index_valid(NUM_CPUS, lctx.cpu_id()) && a.cpu_op.view().view()[lctx.cpu_id() as int] is InStep ==> lctx.cpu_lock_map().dom().contains(lctx.cpu_id()),
        ensures
            kernel_step_boundary_framing(a, c, lctx),
    {
        assert(held_allocator_objects_unchanged(a.allc_4k_mp, c.allc_4k_mp, &lctx, PageSize::SZ4k)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        assert(held_allocator_objects_unchanged(a.allc_2m_mp, c.allc_2m_mp, &lctx, PageSize::SZ2m)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        assert(held_allocator_objects_unchanged(a.allc_1g_mp, c.allc_1g_mp, &lctx, PageSize::SZ1g)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
    }

    // ---- Held-lock / krnl-state alignment ----

    /// Every lock this context holds orders below a locker whose held pages must stay under
    /// `page_bound`: no dirty-PCID records, no Off cpus, no scheduled threads, and no
    /// allocator quota, cache, or pool locks.
    pub open spec fn held_locks_order_below(k: &KernelK, lctx: &LocalContext, page_bound: LockMajorId) -> bool {
        &&& lctx.pcid_needflush_lock_map().dom().is_empty()
        &&& lctx.cpu_offline_flag_lock_map().dom().is_empty()
        &&& forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(k.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
        &&& forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> {
            let page = k.pg_arr.spec_index(held_page).view().view();
            if page_bound <= PAGETABLE_PAGE_MAJOR { page.orders_below_table_locks() } else { page.orders_below_allocator_locks() }
        }
        &&& forall|held_thread: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(held_thread)] lctx.thread_lock_map().dom().contains(held_thread) ==> !(k.thr_mp.spec_index(held_thread).view().state is SCHEDULED)
        &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
        &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
        &&& lctx.holds_no_allocator_locks(PageSize::SZ1g)
    }

    pub open spec fn typed_lock_maps_aligned(k: &KernelK, lctx: &LocalContext) -> bool {
        &&& k.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())
        &&& k.cpu_arr.typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id())
        &&& (forall|cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)]
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
            ==> k.cpu_arr.spec_index(cpu_id).view().view_ghost() == Some(lctx.cpu_id()))
        &&& k.pcid_needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id())
        &&& (forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write)]
            typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write)
            ==> k.pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == Some(lctx.cpu_id()))
        &&& k.cpu_offline_mp.typed_flag_lock_map_aligned(lctx.cpu_offline_flag_lock_map(), lctx.thread_id())
        &&& iommu_root_table_typed_lock_map_aligned(k.irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())
        &&& k.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id())
        &&& k.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())
        &&& k.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())
        &&& k.ep_mp.typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id())
        &&& k.sched_mp.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id())
        &&& k.pcid_allc_mp.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id())
        &&& k.cpu_set_mp.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id())
        &&& k.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())
        &&& pagetable_window_typed_lock_map_aligned(k.pt_mp, k.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id())
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

    /// Locks a killer holds between steps: its running CPU, process and thread, the containers `containers`, plus the
    /// objects it marked.
    pub open spec fn killer_held_context(k: KernelK, lctx: LocalContext, killer_process: RwLockProcessPtr, killer_thread: RwLockThreadPtr, containers: Set<RwLockContainerPtr>) -> bool {
        &&& killer_held_context_except_tables(k, lctx, killer_process, killer_thread, containers)
        &&& lctx.page_lock_map().dom().is_empty()
        &&& lctx.pagetable_lock_map().dom().is_empty()
        &&& lctx.pagetable_window_lock_map().dom().is_empty()
        &&& lctx.iommu_table_lock_map().dom().is_empty()
    }

    /// `killer_held_context` without its empty page, page-table, and IOMMU-table lock maps.
    pub open spec fn killer_held_context_except_tables(
        k: KernelK, lctx: LocalContext, killer_process: RwLockProcessPtr, killer_thread: RwLockThreadPtr, containers: Set<RwLockContainerPtr>,
    ) -> bool {
        let cpu_id = lctx.cpu_id();
        let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
        &&& index_valid(NUM_CPUS, cpu_id)
        &&& lctx.cpu_lock_map().dom() =~= set![cpu_id]
        &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
        &&& cpu.state is Running
        &&& cpu.current_process == Some(killer_process)
        &&& cpu.current_thread == Some(killer_thread)
        &&& typed_lock_map_contains_mode(lctx.process_lock_map(), killer_process, TypedLockMode::Write)
        &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), killer_thread, TypedLockMode::Write)
        &&& forall|p: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(p)] lctx.process_lock_map().dom().contains(p) && p != killer_process ==> k.prc_mp.spec_index(p).being_killed()
        &&& forall|t: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(t)] lctx.thread_lock_map().dom().contains(t) && t != killer_thread ==> k.thr_mp.spec_index(t).being_killed()
        &&& lctx.pcid_needflush_lock_map().dom().is_empty()
        &&& lctx.cpu_offline_flag_lock_map().dom().is_empty()
        &&& lctx.container_lock_map().dom() =~= containers
        &&& forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) && c != cpu.owning_container ==> k.ctn_mp.spec_index(c).being_killed()
        &&& lctx.endpoint_lock_map().dom().is_empty()
        &&& lctx.scheduler_lock_map().dom().is_empty()
        &&& lctx.pcid_allocator_lock_map().dom().is_empty()
        &&& forall|s: RwLockCpuSetPtr| #![trigger lctx.cpu_set_lock_map().dom().contains(s)] lctx.cpu_set_lock_map().dom().contains(s) ==> k.cpu_set_mp.spec_index(s).being_killed()
        &&& lctx.iommu_root_table_lock_map().dom().is_empty()
        &&& lctx.allocator_quota_4k_lock_map().dom().is_empty()
        &&& lctx.allocator_cache_4k_lock_map().dom().is_empty()
        &&& lctx.allocator_global_pool_4k_lock_map().dom().is_empty()
        &&& lctx.allocator_quota_2m_lock_map().dom().is_empty()
        &&& lctx.allocator_cache_2m_lock_map().dom().is_empty()
        &&& lctx.allocator_global_pool_2m_lock_map().dom().is_empty()
        &&& lctx.allocator_quota_1g_lock_map().dom().is_empty()
        &&& lctx.allocator_cache_1g_lock_map().dom().is_empty()
        &&& lctx.allocator_global_pool_1g_lock_map().dom().is_empty()
    }

    /// A killer holding only its own thread among threads and the containers `containers` may lock any thread of a
    /// deeper container or of a deeper process of its container, whatever its state.
    pub open spec fn killer_any_thread_lock_context(k: KernelK, lctx: LocalContext, thread_ptr: RwLockThreadPtr, containers: Set<RwLockContainerPtr>) -> bool {
        let cpu = k.cpu_arr.spec_index(lctx.cpu_id()).view().view().view();
        let thread = k.thr_mp.spec_index(thread_ptr).view();
        &&& killer_held_context(k, lctx, cpu.current_process->Some_0, cpu.current_thread->Some_0, containers)
        &&& lctx.thread_lock_map().dom() =~= set![cpu.current_thread->Some_0]
        &&& thread.container_depth > cpu.container_depth || (thread.container_depth == cpu.container_depth && thread.process_depth > cpu.process_depth)
    }

    /// Locks a thread holds while it reclaims killed threads: its running cpu, any containers and processes, its running
    /// thread, and killed or marked threads, none of them waiting on an endpoint or a reply, in IPC transit, or scheduled.
    pub open spec fn killed_thread_reclaim_lock_context(k: KernelK, lctx: LocalContext) -> bool {
        let cpu_id = lctx.cpu_id();
        let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
        &&& index_valid(NUM_CPUS, cpu_id)
        &&& lctx.cpu_lock_map().dom() =~= set![cpu_id]
        &&& cpu.state is Running
        &&& cpu.current_thread is Some
        &&& lctx.thread_lock_map().dom().contains(cpu.current_thread->Some_0)
        &&& forall|t: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(t)] lctx.thread_lock_map().dom().contains(t) ==> {
            let state = k.thr_mp.spec_index(t).view().state;
            &&& t == cpu.current_thread->Some_0 || state is KILLED || k.thr_mp.spec_index(t).being_killed()
            &&& !(state.is_endpoint_waiting() || state.is_reply_waiting() || state is IPC_TRANSIT || state is SCHEDULED)
        }
        &&& lctx.page_lock_map().dom().is_empty()
        &&& lctx.pcid_needflush_lock_map().dom().is_empty()
        &&& lctx.cpu_offline_flag_lock_map().dom().is_empty()
        &&& lctx.endpoint_lock_map().dom().is_empty()
        &&& lctx.scheduler_lock_map().dom().is_empty()
        &&& lctx.pcid_allocator_lock_map().dom().is_empty()
        &&& lctx.cpu_set_lock_map().dom().is_empty()
        &&& lctx.pagetable_lock_map().dom().is_empty()
        &&& lctx.iommu_table_lock_map().dom().is_empty()
        &&& lctx.iommu_root_table_lock_map().dom().is_empty()
        &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
        &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
        &&& lctx.holds_no_allocator_locks(PageSize::SZ1g)
    }
}

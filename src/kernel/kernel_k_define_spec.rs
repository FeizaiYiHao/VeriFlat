use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {

    pub const KERNEL_DEFAULT_PCID:Pcid = 0; 
    pub struct KernelK{
        pub pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>,
        pub page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
        pub cpu_array: LockedArray<Cpu, (), (), (), NUM_CPUS, CPU_HAS_KILL_STATE>,
        pub cpu_tlb: CpuTLB,

        pub root_container: RwLockContainerPtr, // Never dies
        pub container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,        
        // pub number_containers: RwLock<NumContainers, (), (), NO_KILL_STATE>,
        pub scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>,
        pub process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), (), PROCESS_HAS_KILL_STATE>,
        pub thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>,
        pub endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>,
        pub allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        pub allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        pub allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,

        // pub clontainer_to_pagetable_map: Ghost<Map<RwLockContainerPtr, Set<RwLockPageTableRoot>>>,

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
            self.container_pages_wf()
            &&&
            self.process_pages_wf()       
            &&&
            pagetable_pages_wf(self.pagetable_map, self.page_array)     
            &&&
            thread_pages_wf(self.thread_map, self.page_array)
            &&&
            thread_owned_pages_wf(self.thread_map, self.page_array)
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

        /// Forward direction: every entry in `lctx.lock_map` corresponds to
        /// a real, currently-locked object whose lock id matches the map.
        pub open spec fn lctx_implies_locked(&self, lctx: &LocalContext) -> bool {
            &&&
            forall|c: RwLockContainerPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Container(c))]
                lctx.lock_map().dom().contains(KernelObjId::Container(c))
                ==>
                self.container_map.dom().contains(c)
                && self.container_map[c].locked_by(lctx)
                && self.container_map[c].locking_thread() is Write
                && self.container_map[c].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Container(c)]
            &&&
            forall|p: RwLockProcessPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Process(p))]
                lctx.lock_map().dom().contains(KernelObjId::Process(p))
                ==>
                self.process_map.dom().contains(p)
                && self.process_map[p].locked_by(lctx)
                && self.process_map[p].locking_thread() is Write
                && self.process_map[p].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Process(p)]
            &&&
            forall|t: RwLockThreadPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Thread(t))]
                lctx.lock_map().dom().contains(KernelObjId::Thread(t))
                ==>
                self.thread_map.dom().contains(t)
                && self.thread_map[t].locked_by(lctx)
                && self.thread_map[t].locking_thread() is Write
                && self.thread_map[t].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Thread(t)]
            &&&
            forall|e: RwLockEndpointPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))]
                lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))
                ==>
                self.endpoint_map.dom().contains(e)
                && self.endpoint_map[e].locked_by(lctx)
                && self.endpoint_map[e].locking_thread() is Write
                && self.endpoint_map[e].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Endpoint(e)]
            &&&
            forall|s: RwLockSchedulerPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))]
                lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                ==>
                self.scheduler_map.dom().contains(s)
                && self.scheduler_map[s].locked_by(lctx)
                && self.scheduler_map[s].locking_thread() is Write
                && self.scheduler_map[s].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Scheduler(s)]
            &&&
            forall|pt: RwLockPageTableRoot|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))]
                lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))
                ==>
                self.pagetable_map.dom().contains(pt)
                && self.pagetable_map[pt].locked_by(lctx)
                && self.pagetable_map[pt].locking_thread() is Write
                && self.pagetable_map[pt].locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::PageTable(pt)]
            &&&
            forall|i: PageIndex|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Page(i))]
                lctx.lock_map().dom().contains(KernelObjId::Page(i))
                ==>
                page_index_wf(i)
                && self.page_array[i]@.locked_by(lctx)
                && self.page_array[i]@.locking_thread() is Write
                && self.page_array[i]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Page(i)]
            &&&
            forall|c: CpuId|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::Cpu(c))]
                lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
                ==>
                cpu_id_valid(c)
                && self.cpu_array[c]@.locked_by(lctx)
                && self.cpu_array[c]@.locking_thread() is Write
                && self.cpu_array[c]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Cpu(c)]
            &&&
            forall|sz: PageSize, p: RwLockPageAllocatorPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))]
                lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
                ==>
                {
                    let m = match sz {
                        PageSize::SZ4k => self.allocator_4k_map,
                        PageSize::SZ2m => self.allocator_2m_map,
                        PageSize::SZ1g => self.allocator_1g_map,
                    };
                    &&& m.dom().contains(p)
                    &&& m[p].quota.locked_by(lctx)
                    &&& m[p].quota.locking_thread() is Write
                    &&& m[p].quota.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorQuota(sz, p)]
                }
            &&&
            forall|sz: PageSize, p: RwLockPageAllocatorPtr, c: CpuId|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))]
                lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
                ==>
                {
                    let m = match sz {
                        PageSize::SZ4k => self.allocator_4k_map,
                        PageSize::SZ2m => self.allocator_2m_map,
                        PageSize::SZ1g => self.allocator_1g_map,
                    };
                    &&& m.dom().contains(p)
                    &&& cpu_id_valid(c)
                    &&& m[p].cpu_caches[c]@.locked_by(lctx)
                    &&& m[p].cpu_caches[c]@.locking_thread() is Write
                    &&& m[p].cpu_caches[c]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorCache(sz, p, c)]
                }
            &&&
            forall|sz: PageSize, p: RwLockPageAllocatorPtr|
                #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))]
                lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
                ==>
                {
                    let m = match sz {
                        PageSize::SZ4k => self.allocator_4k_map,
                        PageSize::SZ2m => self.allocator_2m_map,
                        PageSize::SZ1g => self.allocator_1g_map,
                    };
                    &&& m.dom().contains(p)
                    &&& m[p].global_poll.locked_by(lctx)
                    &&& m[p].global_poll.locking_thread() is Write
                    &&& m[p].global_poll.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorGlobalPoll(sz, p)]
                }
        }

        /// Reverse direction: every kernel object currently held by `lctx`
        /// is recorded in `lctx.lock_map`. (No stealth locks.)
        pub open spec fn locked_implies_lctx(&self, lctx: &LocalContext) -> bool {
            &&&
            forall|c: RwLockContainerPtr|
                #![trigger self.container_map.dom().contains(c)]
                self.container_map.dom().contains(c) && self.container_map[c].locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Container(c))
            &&&
            forall|p: RwLockProcessPtr|
                #![trigger self.process_map.dom().contains(p)]
                self.process_map.dom().contains(p) && self.process_map[p].locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Process(p))
            &&&
            forall|t: RwLockThreadPtr|
                #![trigger self.thread_map.dom().contains(t)]
                self.thread_map.dom().contains(t) && self.thread_map[t].locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Thread(t))
            &&&
            forall|e: RwLockEndpointPtr|
                #![trigger self.endpoint_map.dom().contains(e)]
                self.endpoint_map.dom().contains(e) && self.endpoint_map[e].locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Endpoint(e))
            &&&
            forall|s: RwLockSchedulerPtr|
                #![trigger self.scheduler_map.dom().contains(s)]
                self.scheduler_map.dom().contains(s) && self.scheduler_map[s].locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
            &&&
            forall|pt: RwLockPageTableRoot|
                #![trigger self.pagetable_map.dom().contains(pt)]
                self.pagetable_map.dom().contains(pt) && self.pagetable_map[pt].locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::PageTable(pt))
            &&&
            forall|i: PageIndex|
                #![trigger self.page_array[i]@.locked_by(lctx)]
                page_index_wf(i) && self.page_array[i]@.locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Page(i))
            &&&
            forall|c: CpuId|
                #![trigger self.cpu_array[c]@.locked_by(lctx)]
                cpu_id_valid(c) && self.cpu_array[c]@.locked_by(lctx)
                ==> lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
            &&&
            forall|p: RwLockPageAllocatorPtr|
                #![trigger self.allocator_4k_map.dom().contains(p)]
                self.allocator_4k_map.dom().contains(p)
                ==>
                {
                    &&&
                    self.allocator_4k_map[p].quota.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(PageSize::SZ4k, p))
                    &&&
                    self.allocator_4k_map[p].global_poll.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p))
                    &&&
                    forall|c: CpuId|
                        #![trigger self.allocator_4k_map[p].cpu_caches[c]@.locked_by(lctx)]
                        cpu_id_valid(c) && self.allocator_4k_map[p].cpu_caches[c]@.locked_by(lctx)
                        ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, p, c))
                }
            &&&
            forall|p: RwLockPageAllocatorPtr|
                #![trigger self.allocator_2m_map.dom().contains(p)]
                self.allocator_2m_map.dom().contains(p)
                ==>
                {
                    &&&
                    self.allocator_2m_map[p].quota.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(PageSize::SZ2m, p))
                    &&&
                    self.allocator_2m_map[p].global_poll.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p))
                    &&&
                    forall|c: CpuId|
                        #![trigger self.allocator_2m_map[p].cpu_caches[c]@.locked_by(lctx)]
                        cpu_id_valid(c) && self.allocator_2m_map[p].cpu_caches[c]@.locked_by(lctx)
                        ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ2m, p, c))
                }
            &&&
            forall|p: RwLockPageAllocatorPtr|
                #![trigger self.allocator_1g_map.dom().contains(p)]
                self.allocator_1g_map.dom().contains(p)
                ==>
                {
                    &&&
                    self.allocator_1g_map[p].quota.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(PageSize::SZ1g, p))
                    &&&
                    self.allocator_1g_map[p].global_poll.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p))
                    &&&
                    forall|c: CpuId|
                        #![trigger self.allocator_1g_map[p].cpu_caches[c]@.locked_by(lctx)]
                        cpu_id_valid(c) && self.allocator_1g_map[p].cpu_caches[c]@.locked_by(lctx)
                        ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ1g, p, c))
                }
        }

        /// Bidirectional agreement: kernel locks and `lctx.lock_map` are
        /// exact mirrors of each other. Used as a precondition for the
        /// kernel-view linearization point.
        pub open spec fn locked_objects_match_lctx(&self, lctx: &LocalContext) -> bool {
            &&& self.lctx_implies_locked(lctx)
            &&& self.locked_implies_lctx(lctx)
        }

        /// Trusted kernel-view linearization primitive.
        ///
        /// Models "the rest of the world runs arbitrary atomic sections
        /// while we sit between two of our own atomic sections":
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
        /// Preconditions:
        ///   - `inv()` holds (we entered the boundary in a wf state),
        ///   - `kernel_view_locking_state is Release` (the syscall declared
        ///     this is the linearization point),
        ///   - `locked_objects_match_lctx(lctx)` (no stealth locks, every
        ///     `lctx.lock_map` entry corresponds to a real held lock).
        ///
        /// Note: this is the *kernel-view* linearization point only. The
        /// user-view counterpart is a separate primitive (TBD).
        #[verifier::external_body]
        pub proof fn kernel_view_linearize(tracked &mut self, tracked lctx: &mut LocalContext)
            requires
                old(self).inv(),
                old(lctx).kernel_view_locking_state() is Release,
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                final(self).inv(),
                // LocalContext: phase flips to Acquire; everything else preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).lock_map() == old(lctx).lock_map(),
                final(lctx).kernel_view_locking_state() is Acquire,
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
                // Kernel still in agreement with lctx.
                final(self).locked_objects_match_lctx(final(lctx)),
                // Read-only data unchanged at the kernel level.
                final(self).root_container == old(self).root_container,
                final(self).default_pagetable == old(self).default_pagetable,
                // Held containers / processes / etc. unchanged in entirety.
                forall|c: RwLockContainerPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Container(c))]
                    old(lctx).lock_map().dom().contains(KernelObjId::Container(c))
                    ==>
                    final(self).container_map.dom().contains(c)
                    && final(self).container_map[c] == old(self).container_map[c],
                forall|p: RwLockProcessPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Process(p))]
                    old(lctx).lock_map().dom().contains(KernelObjId::Process(p))
                    ==>
                    final(self).process_map.dom().contains(p)
                    && final(self).process_map[p] == old(self).process_map[p],
                forall|t: RwLockThreadPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Thread(t))]
                    old(lctx).lock_map().dom().contains(KernelObjId::Thread(t))
                    ==>
                    final(self).thread_map.dom().contains(t)
                    && final(self).thread_map[t] == old(self).thread_map[t],
                forall|e: RwLockEndpointPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Endpoint(e))]
                    old(lctx).lock_map().dom().contains(KernelObjId::Endpoint(e))
                    ==>
                    final(self).endpoint_map.dom().contains(e)
                    && final(self).endpoint_map[e] == old(self).endpoint_map[e],
                forall|s: RwLockSchedulerPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                    old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                    ==>
                    final(self).scheduler_map.dom().contains(s)
                    && final(self).scheduler_map[s] == old(self).scheduler_map[s],
                forall|pt: RwLockPageTableRoot|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::PageTable(pt))]
                    old(lctx).lock_map().dom().contains(KernelObjId::PageTable(pt))
                    ==>
                    final(self).pagetable_map.dom().contains(pt)
                    && final(self).pagetable_map[pt] == old(self).pagetable_map[pt],
                // Held pages: full RwLock instance preserved.
                forall|i: PageIndex|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Page(i))]
                    page_index_wf(i) && old(lctx).lock_map().dom().contains(KernelObjId::Page(i))
                    ==>
                    final(self).page_array[i]@ == old(self).page_array[i]@,
                // Held cpus: full RwLock instance preserved.
                forall|c: CpuId|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))]
                    cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    ==>
                    final(self).cpu_array[c]@ == old(self).cpu_array[c]@,
                // Held allocator-quota: that specific RwLock preserved.
                // The enclosing PageAllocator may change in other ways
                // (other internal locks, ghost fields, owning_container),
                // since these aren't protected by the held lock.
                forall|sz: PageSize, p: RwLockPageAllocatorPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))]
                    old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
                    ==>
                    {
                        let old_m = match sz {
                            PageSize::SZ4k => old(self).allocator_4k_map,
                            PageSize::SZ2m => old(self).allocator_2m_map,
                            PageSize::SZ1g => old(self).allocator_1g_map,
                        };
                        let new_m = match sz {
                            PageSize::SZ4k => final(self).allocator_4k_map,
                            PageSize::SZ2m => final(self).allocator_2m_map,
                            PageSize::SZ1g => final(self).allocator_1g_map,
                        };
                        new_m.dom().contains(p) && new_m[p].quota == old_m[p].quota
                    },
                forall|sz: PageSize, p: RwLockPageAllocatorPtr|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))]
                    old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
                    ==>
                    {
                        let old_m = match sz {
                            PageSize::SZ4k => old(self).allocator_4k_map,
                            PageSize::SZ2m => old(self).allocator_2m_map,
                            PageSize::SZ1g => old(self).allocator_1g_map,
                        };
                        let new_m = match sz {
                            PageSize::SZ4k => final(self).allocator_4k_map,
                            PageSize::SZ2m => final(self).allocator_2m_map,
                            PageSize::SZ1g => final(self).allocator_1g_map,
                        };
                        new_m.dom().contains(p) && new_m[p].global_poll == old_m[p].global_poll
                    },
                forall|sz: PageSize, p: RwLockPageAllocatorPtr, c: CpuId|
                    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))]
                    old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
                    ==>
                    {
                        let old_m = match sz {
                            PageSize::SZ4k => old(self).allocator_4k_map,
                            PageSize::SZ2m => old(self).allocator_2m_map,
                            PageSize::SZ1g => old(self).allocator_1g_map,
                        };
                        let new_m = match sz {
                            PageSize::SZ4k => final(self).allocator_4k_map,
                            PageSize::SZ2m => final(self).allocator_2m_map,
                            PageSize::SZ1g => final(self).allocator_1g_map,
                        };
                        new_m.dom().contains(p)
                        && cpu_id_valid(c)
                        && new_m[p].cpu_caches[c]@ == old_m[p].cpu_caches[c]@
                    },
                // Fixed-size arrays keep their full domain (always true for
                // LockedArray, but stated here so callers can rely on it).
                // The unheld entries' values may have changed.
        {
            unimplemented!()
        }
    }

}
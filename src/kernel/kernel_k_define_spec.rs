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
        pub process_map: ProcessLockedMap,
        pub thread_map: ThreadLockedMap,
        pub endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>,
        pub allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        pub allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        pub allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,

        // pub clontainer_to_pagetable_map: Ghost<Map<RwLockContainerPtr, Set<RwLockPageTableRoot>>>,

        pub default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>, // Read only
    }

    // ============================================================
    //   Lock-map / kernel-state agreement — per-object-kind pieces
    // ============================================================
    //
    // `lctx_implies_locked` / `locked_implies_lctx` were two single ~150-line
    // methods, each ANDing one quantifier per object kind across opposite
    // directions. They are now folded into ONE opaque, BIDIRECTIONAL
    // `open spec fn` per map/array: `{kind}_locked_match_lctx` ANDs both the
    // forward (lctx entry ⟹ object locked, with matching lock id) and the
    // reverse (object locked by this thread ⟹ recorded in lctx) facts for that
    // one kind. Keeping each piece opaque means a consumer that only touches,
    // say, the page array reveals just `page_locked_match_lctx` instead of
    // seeding the proof context with all ~20 quantifiers. `locked_objects_match_lctx`
    // (below) is the `open` wrapper that ANDs the pieces, so the (external-body)
    // `kernel_step_boundary` contract — which names only `locked_objects_match_lctx`
    // — is unchanged.
    //
    // The allocator piece takes the map + its `PageSize` tag explicitly; the
    // wrapper instantiates it at (4k, SZ4k) / (2m, SZ2m) / (1g, SZ1g). Since
    // `PageSize` has exactly those three variants, the three concrete calls are
    // logically the old single `forall|sz: PageSize|` (whose body selected the
    // map by `sz`).

    #[verifier::opaque]
    pub open spec fn container_locked_match_lctx(
        container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,
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
        endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>,
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
        scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>,
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
        pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>,
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
        page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|i: PageIndex|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Page(i))]
            lctx.lock_map().dom().contains(KernelObjId::Page(i))
            ==>
            page_index_wf(i)
            && page_array[i]@.locked_by(lctx)
            && page_array[i]@.locking_thread() is Write
            && page_array[i]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Page(i)]
            // Pinned recorded lock id (full id; sound because every field is
            // STABLE while the page is held): owner ids are the page's constant
            // `None/None`, the minor is the page's (fixed) array index, and the
            // recorded major is one of Page's DECLARED majors. Crucially the
            // major is pinned to the constant SET {FREE, MAPPED, MERGED,
            // ALLOCATED} — NOT to `current_lock_major()` — because a held page
            // may change state (e.g. Free4k→Owned4k) while locked, which would
            // move `current_lock_major()` but never the recorded id. All four
            // page majors are ≥ ALLOCATED_PAGE_MAJOR (1000), which lets callers
            // holding only sub-1000-major locks (e.g. a cpu cache at major 106)
            // derive that NO page is held — hence a fresh page index to lock.
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
            page_index_wf(i) && page_array[i]@.locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Page(i)))
    }

    #[verifier::opaque]
    pub open spec fn cpu_locked_match_lctx(
        cpu_array: LockedArray<Cpu, (), (), (), NUM_CPUS, CPU_HAS_KILL_STATE>,
        lctx: &LocalContext,
    ) -> bool {
        &&& (forall|c: CpuId|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::Cpu(c))]
            lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
            ==>
            cpu_id_valid(c)
            && cpu_array[c]@.locked_by(lctx)
            && cpu_array[c]@.locking_thread() is Write
            && cpu_array[c]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::Cpu(c)])
        &&& (forall|c: CpuId|
            #![trigger cpu_array[c]@.locked_by(lctx)]
            cpu_id_valid(c) && cpu_array[c]@.locked_by(lctx)
            ==> lctx.lock_map().dom().contains(KernelObjId::Cpu(c)))
    }

    /// Bidirectional agreement for one allocator map, tagged by its `PageSize`.
    #[verifier::opaque]
    pub open spec fn allocator_locked_match_lctx(
        alloc_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        sz: PageSize,
        lctx: &LocalContext,
    ) -> bool {
        // forward: quota / cache / global_poll
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].quota.locked_by(lctx)
            && alloc_map[p].quota.locking_thread() is Write
            && alloc_map[p].quota.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorQuota(sz, p)])
        &&& (forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
            ==>
            alloc_map.dom().contains(p)
            && cpu_id_valid(c)
            && alloc_map[p].cpu_caches[c]@.locked_by(lctx)
            && alloc_map[p].cpu_caches[c]@.locking_thread() is Write
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorCache(sz, p, c)]
            // Pinned recorded lock id (sound: every field is STABLE while the
            // cache is held). An `AllocatorCache` has constant `NotApp/NotApp`
            // owner ids, its array minor is the (fixed) cpu index `c`, and its
            // `current_lock_major` is ALWAYS `ALLOCATOR_CACHE_MAJOR` (the cache's
            // `lock_major_1_predicate` is `true`, so the major never moves with
            // state). Pinning these lets a caller holding only this-or-lower
            // locks prove the cache is NOT already held — i.e. it is fresh to
            // re-lock. (The owners are `NotApp` wildcards, so the freshness
            // contradiction is decided by major/minor: a held cache would force
            // `cache_id.spec_gt(cache_id)`, which is false.)
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.container == LockOwnerId::NotApp
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.process == LockOwnerId::NotApp
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.minor == c
            && alloc_map[p].cpu_caches[c]@.locking_thread()->Write_lock_id.major == ALLOCATOR_CACHE_MAJOR)
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))]
            lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
            ==>
            alloc_map.dom().contains(p)
            && alloc_map[p].global_poll.locked_by(lctx)
            && alloc_map[p].global_poll.locking_thread() is Write
            && alloc_map[p].global_poll.locking_thread()->Write_lock_id == lctx.lock_map()[KernelObjId::AllocatorGlobalPoll(sz, p)])
        // reverse: any locked piece of any allocator is recorded
        &&& (forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.dom().contains(p)]
            alloc_map.dom().contains(p)
            ==>
            {
                &&& alloc_map[p].quota.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorQuota(sz, p))
                &&& alloc_map[p].global_poll.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(sz, p))
                &&& forall|c: CpuId|
                    #![trigger alloc_map[p].cpu_caches[c]@.locked_by(lctx)]
                    cpu_id_valid(c) && alloc_map[p].cpu_caches[c]@.locked_by(lctx)
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(sz, p, c))
            })
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
            self.thread_perms_wf()
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
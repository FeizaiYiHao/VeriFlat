use vstd::prelude::*;
use crate::*;
verus! {

    pub broadcast proof fn cpu_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<CpuId>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map(),
            #[trigger] cpu_objects_unlocked_except(
                pre.cpu_arr, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            cpu_objects_unlocked_except(
                post.cpu_arr, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedArray::typed_lock_map_aligned);
    }

    pub broadcast proof fn page_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<PageIndex>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.page_lock_map() == pre_lctx.page_lock_map(),
            #[trigger] page_objects_unlocked_except(
                pre.pg_arr, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            page_objects_unlocked_except(
                post.pg_arr, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedArray::typed_lock_map_aligned);
    }

    pub broadcast proof fn container_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockContainerPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.container_lock_map() == pre_lctx.container_lock_map(),
            #[trigger] container_objects_unlocked_except(
                pre.ctn_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            container_objects_unlocked_except(
                post.ctn_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn container_objects_unlocked_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.container_lock_map() == pre_lctx.container_lock_map(),
            #[trigger] container_objects_unlocked(
                pre.ctn_mp, pre_lctx.thread_id(),
            ),
        ensures
            container_objects_unlocked(
                post.ctn_mp, post_lctx.thread_id(),
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn scheduler_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockSchedulerPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map(),
            #[trigger] scheduler_objects_unlocked_except(
                pre.sched_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            scheduler_objects_unlocked_except(
                post.sched_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn scheduler_objects_unlocked_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.scheduler_lock_map() == pre_lctx.scheduler_lock_map(),
            #[trigger] scheduler_objects_unlocked(
                pre.sched_mp, pre_lctx.thread_id(),
            ),
        ensures
            scheduler_objects_unlocked(
                post.sched_mp, post_lctx.thread_id(),
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn process_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockProcessPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.process_lock_map() == pre_lctx.process_lock_map(),
            #[trigger] process_objects_unlocked_except(
                pre.prc_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            process_objects_unlocked_except(
                post.prc_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn thread_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockThreadPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
            #[trigger] thread_objects_unlocked_except(
                pre.thr_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            thread_objects_unlocked_except(
                post.thr_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub proof fn thread_lock_id_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        thread_ptr: RwLockThreadPtr,
    )
        requires
            pre.inv(),
            post.inv(),
            typed_lock_maps_aligned(pre, pre_lctx),
            typed_lock_maps_aligned(post, post_lctx),
            post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
            pre_lctx.thread_lock_map().dom().contains(thread_ptr),
        ensures
            post.thr_mp.lock_id_by_key(thread_ptr)
                == pre.thr_mp.lock_id_by_key(thread_ptr),
    {
        reveal(thread_perms_wf);
        reveal(LockedMap::typed_lock_map_aligned);
        lock_id_fields_eq_imply_eq();
    }

    pub proof fn cpu_lock_id_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        cpu_id: CpuId,
    )
        requires
            typed_lock_maps_aligned(pre, pre_lctx),
            typed_lock_maps_aligned(post, post_lctx),
            post_lctx.cpu_lock_map() == pre_lctx.cpu_lock_map(),
            pre_lctx.cpu_lock_map().dom().contains(cpu_id),
        ensures
            post.cpu_arr.lock_id_by_index(cpu_id)
                == pre.cpu_arr.lock_id_by_index(cpu_id),
    {
        reveal(LockedArray::typed_lock_map_aligned);
    }

    pub proof fn process_lock_id_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        process_ptr: RwLockProcessPtr,
    )
        requires
            pre.inv(),
            post.inv(),
            typed_lock_maps_aligned(pre, pre_lctx),
            typed_lock_maps_aligned(post, post_lctx),
            post_lctx.process_lock_map() == pre_lctx.process_lock_map(),
            pre_lctx.process_lock_map().dom().contains(process_ptr),
        ensures
            post.prc_mp.lock_id_by_key(process_ptr)
                == pre.prc_mp.lock_id_by_key(process_ptr),
    {
        reveal(process_perms_wf);
        reveal(LockedMap::typed_lock_map_aligned);
        lock_id_fields_eq_imply_eq();
    }

    pub proof fn endpoint_lock_id_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        endpoint_ptr: RwLockEndpointPtr,
    )
        requires
            pre.inv(),
            post.inv(),
            typed_lock_maps_aligned(pre, pre_lctx),
            typed_lock_maps_aligned(post, post_lctx),
            post_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map(),
            pre_lctx.endpoint_lock_map().dom().contains(endpoint_ptr),
        ensures
            post.ep_mp.lock_id_by_key(endpoint_ptr)
                == pre.ep_mp.lock_id_by_key(endpoint_ptr),
    {
        reveal(endpoint_perms_wf);
        reveal(LockedMap::typed_lock_map_aligned);
        lock_id_fields_eq_imply_eq();
    }

    pub broadcast proof fn endpoint_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockEndpointPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.endpoint_lock_map() == pre_lctx.endpoint_lock_map(),
            #[trigger] endpoint_objects_unlocked_except(
                pre.ep_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            endpoint_objects_unlocked_except(
                post.ep_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn pagetable_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockPageTableRoot>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.pagetable_lock_map()
                == pre_lctx.pagetable_lock_map(),
            #[trigger] pagetable_objects_unlocked_except(
                pre.pt_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            pagetable_objects_unlocked_except(
                post.pt_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn iommu_table_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockPageTableRoot>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.iommu_table_lock_map()
                == pre_lctx.iommu_table_lock_map(),
            #[trigger] iommu_table_objects_unlocked_except(
                pre.it_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            iommu_table_objects_unlocked_except(
                post.it_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn iommu_table_objects_unlocked_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.iommu_table_lock_map()
                == pre_lctx.iommu_table_lock_map(),
            #[trigger] iommu_table_objects_unlocked(
                pre.it_mp, pre_lctx.thread_id(),
            ),
        ensures
            iommu_table_objects_unlocked(
                post.it_mp, post_lctx.thread_id(),
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn pcid_allocator_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockPcidAllocatorPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.pcid_allocator_lock_map()
                == pre_lctx.pcid_allocator_lock_map(),
            #[trigger] pcid_allocator_objects_unlocked_except(
                pre.pcid_allc_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            pcid_allocator_objects_unlocked_except(
                post.pcid_allc_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn pcid_allocator_objects_unlocked_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.pcid_allocator_lock_map()
                == pre_lctx.pcid_allocator_lock_map(),
            #[trigger] pcid_allocator_objects_unlocked(
                pre.pcid_allc_mp, pre_lctx.thread_id(),
            ),
        ensures
            pcid_allocator_objects_unlocked(
                post.pcid_allc_mp, post_lctx.thread_id(),
            ),
    {
        reveal(LockedMap::typed_lock_map_aligned);
    }

    pub broadcast proof fn allocator_4k_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockPageAllocatorPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.allocator_quota_4k_lock_map()
                == pre_lctx.allocator_quota_4k_lock_map(),
            post_lctx.allocator_cache_4k_lock_map()
                == pre_lctx.allocator_cache_4k_lock_map(),
            post_lctx.allocator_global_pool_4k_lock_map()
                == pre_lctx.allocator_global_pool_4k_lock_map(),
            #[trigger] allocator_objects_unlocked_except(
                pre.allc_4k_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            allocator_objects_unlocked_except(
                post.allc_4k_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(UnLockedMap::typed_quota_lock_map_aligned);
        reveal(UnLockedMap::typed_cache_lock_map_aligned);
        reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
    }

    pub broadcast proof fn allocator_2m_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockPageAllocatorPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.allocator_2m_lock_maps()
                == pre_lctx.allocator_2m_lock_maps(),
            #[trigger] allocator_objects_unlocked_except(
                pre.allc_2m_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            allocator_objects_unlocked_except(
                post.allc_2m_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(UnLockedMap::typed_quota_lock_map_aligned);
        reveal(UnLockedMap::typed_cache_lock_map_aligned);
        reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
    }

    pub broadcast proof fn allocator_1g_objects_unlocked_except_preserved_for_typed_maps_unchanged(
        pre: &KernelK,
        post: &KernelK,
        pre_lctx: &LocalContext,
        post_lctx: &LocalContext,
        exceptions: Set<RwLockPageAllocatorPtr>,
    )
        requires
            #[trigger] typed_lock_maps_aligned(pre, pre_lctx),
            #[trigger] typed_lock_maps_aligned(post, post_lctx),
            post_lctx.allocator_1g_lock_maps()
                == pre_lctx.allocator_1g_lock_maps(),
            #[trigger] allocator_objects_unlocked_except(
                pre.allc_1g_mp, pre_lctx.thread_id(), exceptions,
            ),
        ensures
            allocator_objects_unlocked_except(
                post.allc_1g_mp, post_lctx.thread_id(), exceptions,
            ),
    {
        reveal(UnLockedMap::typed_quota_lock_map_aligned);
        reveal(UnLockedMap::typed_cache_lock_map_aligned);
        reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
    }

    pub broadcast group group_object_types_unlocked_except_preserved_for_typed_maps_unchanged {
        cpu_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        page_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        container_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        scheduler_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        process_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        thread_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        endpoint_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        pagetable_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        iommu_table_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        pcid_allocator_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        allocator_4k_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        allocator_2m_objects_unlocked_except_preserved_for_typed_maps_unchanged,
        allocator_1g_objects_unlocked_except_preserved_for_typed_maps_unchanged,
    }

    pub open spec fn kernel_objects_unlocked_except(
        krnl: &KernelK,
        thread_id: LockThreadId,
        cpu_exceptions: Set<CpuId>,
        container_exceptions: Set<RwLockContainerPtr>,
        scheduler_exceptions: Set<RwLockSchedulerPtr>,
        process_exceptions: Set<RwLockProcessPtr>,
        thread_exceptions: Set<RwLockThreadPtr>,
        page_exceptions: Set<PageIndex>,
        endpoint_exceptions: Set<RwLockEndpointPtr>,
        pagetable_exceptions: Set<RwLockPageTableRoot>,
        iommu_table_exceptions: Set<RwLockPageTableRoot>,
        pcid_allocator_exceptions: Set<RwLockPcidAllocatorPtr>,
        allocator_4k_exceptions: Set<RwLockPageAllocatorPtr>,
        allocator_2m_exceptions: Set<RwLockPageAllocatorPtr>,
        allocator_1g_exceptions: Set<RwLockPageAllocatorPtr>,
    ) -> bool {
        &&& cpu_objects_unlocked_except(krnl.cpu_arr, thread_id, cpu_exceptions)
        &&& container_objects_unlocked_except(krnl.ctn_mp, thread_id, container_exceptions)
        &&& scheduler_objects_unlocked_except(krnl.sched_mp, thread_id, scheduler_exceptions)
        &&& process_objects_unlocked_except(krnl.prc_mp, thread_id, process_exceptions)
        &&& thread_objects_unlocked_except(krnl.thr_mp, thread_id, thread_exceptions)
        &&& page_objects_unlocked_except(krnl.pg_arr, thread_id, page_exceptions)
        &&& endpoint_objects_unlocked_except(krnl.ep_mp, thread_id, endpoint_exceptions)
        &&& pagetable_objects_unlocked_except(krnl.pt_mp, thread_id, pagetable_exceptions)
        &&& iommu_table_objects_unlocked_except(krnl.it_mp, thread_id, iommu_table_exceptions)
        &&& pcid_allocator_objects_unlocked_except(krnl.pcid_allc_mp, thread_id, pcid_allocator_exceptions)
        &&& allocator_objects_unlocked_except(krnl.allc_4k_mp, thread_id, allocator_4k_exceptions)
        &&& allocator_objects_unlocked_except(krnl.allc_2m_mp, thread_id, allocator_2m_exceptions)
        &&& allocator_objects_unlocked_except(krnl.allc_1g_mp, thread_id, allocator_1g_exceptions)
    }

    /// Commit path: allocate 4k page, create thread, release all locks.
    pub fn release_cpu_and_finish_syscall(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            lctx.kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(&lctx),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(lctx).cpu_process_thread_lock_scope(set![cpu_id], Set::<RwLockProcessPtr>::empty(), Set::<RwLockThreadPtr>::empty()),
            kernel_objects_unlocked_except(
                old(krnl), old(lctx).thread_id(), set![cpu_id], Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty()),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();

        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }

    /// Release process + cpu when the current thread cannot be locked.
    pub fn release_cpu_and_process_and_finish_syscall(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        process_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            lctx.kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(&lctx),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == lctx.thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(&lctx),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            old(lctx).cpu_process_thread_lock_scope(set![cpu_id], set![process_ptr], Set::<RwLockThreadPtr>::empty()),
            kernel_objects_unlocked_except(
                old(krnl), old(lctx).thread_id(), set![cpu_id], Set::empty(), Set::empty(), set![process_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty()),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
    {
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }
    pub fn release_cpu_and_process_and_thread_and_finish_syscall(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        thread_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            !(old(krnl).thr_mp.spec_index(thread_ptr).view().state
                is IPC_ENDPOINT_TRANSIT),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id()
                == old(krnl).cpu_arr.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(krnl).prc_mp.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(lctx).cpu_process_thread_lock_scope(set![cpu_id], set![process_ptr], set![thread_ptr]),
            kernel_objects_unlocked_except(
                old(krnl), old(lctx).thread_id(), set![cpu_id], Set::empty(), Set::empty(), set![process_ptr], set![thread_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty()),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
    {
        let tracked thread_lock_perm = thread_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(
            process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
        );
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }

}

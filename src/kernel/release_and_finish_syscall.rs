use vstd::prelude::*;
use crate::*;
verus! {
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
        assert(post.thr_mp.lock_id_by_key(thread_ptr)
                == post_lctx.thread_lock_map().index(thread_ptr).lock_id
            && pre.thr_mp.lock_id_by_key(thread_ptr)
                == pre_lctx.thread_lock_map().index(thread_ptr).lock_id) by {
            reveal(thread_perms_wf);
            reveal(LockedMap::typed_lock_map_aligned);
            lock_id_fields_eq_imply_eq();
        };
    }

    pub proof fn no_locks_held_imply_all_objects_unlocked(
        krnl: &KernelK,
        lctx: &LocalContext,
    )
        requires
            lctx.no_locks_held(),
            typed_lock_maps_aligned(krnl, lctx),
        ensures
            krnl.all_objects_unlocked(lctx),
    {
        reveal(KernelK::all_objects_unlocked);
        reveal(LockedArray::typed_lock_map_aligned);
        reveal(LockedArray2D::typed_lock_map_aligned);
        reveal(LockedMap::typed_lock_map_aligned);
        reveal(UnLockedMap::typed_quota_lock_map_aligned);
        reveal(UnLockedMap::typed_cache_lock_map_aligned);
        reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
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
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        ensures
            kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
            forall|i: CpuId|
                #![trigger final(krnl).cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> final(krnl).cpu_arr.spec_index(i).view().view().view() == old(krnl).cpu_arr.spec_index(i).view().view().view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
    {

        let tracked cpu_lock_perm = cpu_lock_perm.get();

        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl);
            };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
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
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == lctx.thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        ensures
            kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
            forall|i: CpuId|
                #![trigger final(krnl).cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> final(krnl).cpu_arr.spec_index(i).view().view().view() == old(krnl).cpu_arr.spec_index(i).view().view().view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
    {

        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl);
            };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
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
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id()
                == old(krnl).cpu_arr.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(krnl).prc_mp.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(krnl).thr_mp.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        ensures
            kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
            forall|i: CpuId|
                #![trigger final(krnl).cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> final(krnl).cpu_arr.spec_index(i).view().view().view() == old(krnl).cpu_arr.spec_index(i).view().view().view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(krnl).ep_mp == old(krnl).ep_mp,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
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
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl);
            };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
    }
}

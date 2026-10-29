use vstd::prelude::*;
use crate::*;
verus! {
    pub proof fn thread_lock_id_preserved_for_typed_maps_unchanged(pre: &KernelK, post: &KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext, thread_ptr: RwLockThreadPtr)
        requires
            pre.inv(),
            post.inv(),
            typed_lock_maps_aligned(pre, pre_lctx),
            typed_lock_maps_aligned(post, post_lctx),
            post_lctx.thread_lock_map() == pre_lctx.thread_lock_map(),
            pre_lctx.thread_lock_map().dom().contains(thread_ptr),
        ensures
            post.thr_mp.lock_id_by_key(thread_ptr) == pre.thr_mp.lock_id_by_key(thread_ptr),
    {
        assert(post.thr_mp.lock_id_by_key(thread_ptr) == post_lctx.thread_lock_map().index(thread_ptr).lock_id
            && pre.thr_mp.lock_id_by_key(thread_ptr) == pre_lctx.thread_lock_map().index(thread_ptr).lock_id) by {
            reveal(thread_perms_wf); reveal(LockedMap::typed_lock_map_aligned);
        };
    }

    pub proof fn no_locks_held_imply_all_objects_unlocked(krnl: &KernelK, lctx: &LocalContext)
        requires
            lctx.no_locks_held(),
            typed_lock_maps_aligned(krnl, lctx),
        ensures
            krnl.all_objects_unlocked(lctx),
    {
        reveal(KernelK::all_objects_unlocked); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedArray2D::typed_lock_map_aligned);
        reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
        reveal(UnLockedMap::typed_global_pool_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
    }

    /// Write-locks the own cpu at a syscall entry and enters its kernel step; the cpu runs a thread and comes from its trap
    /// path. A cpu a killer marked is not waited for: the call returns at once, the step ends without a user-visible
    /// change, and the syscall returns CpuIdle.
    pub fn wlock_cpu_if_running(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId) -> (ret: Option<Tracked<LockPerm>>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).inv(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            (ret is Some) == !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            ret is None ==> {
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& final(lctx).no_locks_held()
                &&& final(krnl).all_objects_unlocked(final(lctx))
                &&& final(steps).view() == old(steps).view()
                &&& final(steps).nonlock_view() == old(steps).nonlock_view()
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl))
                &&& kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl))
            },
            ret is Some ==> {
                let pre = old(krnl).cpu_arr.spec_index(cpu_id).view();
                let post = final(krnl).cpu_arr.spec_index(cpu_id).view();
                let cpu = post.view().view();
                let perm = ret->Some_0.view();
                &&& *final(steps) == *old(steps)
                &&& final(lctx).kernel_view_locking_state() is Acquire
                &&& cpu.state is Running
                &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
                &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
                &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
                &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, ..*old(krnl) })
                &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
                &&& final(lctx).kernel_call_perm() == Some(cpu_id)
                &&& final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id)
                &&& final(krnl).cpu_arr.inv()
                &&& cpu == pre.view().view()
                &&& post.view().kernel_call_perm() is None
                &&& post.wlocked_by(final(lctx))
                &&& post.locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: perm.lock_id() }
                &&& post.inv()
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() == Some(cpu_id)
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
                &&& pre.locked() == false
                &&& perm.state() is WriteLock
                &&& post.locking_thread()->Write_lock_id == perm.lock_id()
                &&& perm.ordering_lock_id() == old(krnl).cpu_arr.lock_id_by_index(cpu_id)
                &&& perm.thread_id() == final(lctx).thread_id()
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id), TypedHeldLock { lock_id: final(krnl).cpu_arr.lock_id_by_index(cpu_id), mode: TypedLockMode::Write })
            },
    {
        proof { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }
        let cpu_lock_res = krnl.wlock_own_cpu(cpu_id, Tracked(&mut *lctx));
        if cpu_lock_res.is_none() {
            proof { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); enter_kernel_view_release_preserving_lock_alignments(&*krnl, lctx); }
            return None;
        }
        cpu_lock_res
    }

    /// Releases the held CPU lock and finishes the syscall.
    pub fn release_cpu_and_finish_syscall(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, cpu_lock_perm: Tracked<LockPerm>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
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
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, ..*old(krnl) }),
            final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id),
            final(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*final(krnl))),
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
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
            final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state)),
            final(lctx).kernel_call_perm() is None,
    {
        proof {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let t = cpu.view().view().current_thread->Some_0;
            assert(cpu.being_killed() ==> krnl.thr_mp.spec_index(t).locked_by_thread(lctx.thread_id())) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedArray::typed_lock_map_aligned); };
            assert(!cpu.being_killed()) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedMap::typed_lock_map_aligned); };
        }
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl); };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
    }

    /// Release process + cpu when the current thread cannot be locked.
    pub fn release_cpu_and_process_and_finish_syscall(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, process_lock_perm: Tracked<LockPerm>, cpu_lock_perm: Tracked<LockPerm>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == lctx.thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == lctx.thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
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
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl)),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, prc_mp: final(krnl).prc_mp, ..*old(krnl) }),
            final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id),
            final(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).locking_thread() is None,
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*final(krnl))),
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
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
            final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state)),
            final(lctx).kernel_call_perm() is None,
    {
        proof {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let t = cpu.view().view().current_thread->Some_0;
            assert(cpu.being_killed() ==> krnl.thr_mp.spec_index(t).locked_by_thread(lctx.thread_id())) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedArray::typed_lock_map_aligned); };
            assert(!cpu.being_killed()) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedMap::typed_lock_map_aligned); };
        }
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
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
    /// Release thread + cpu on an IPC rejection; the IPC path takes no process lock.
    pub fn release_cpu_and_thread_and_finish_syscall(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        thread_ptr: RwLockThreadPtr, thread_lock_perm: Tracked<LockPerm>, cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl)),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
            final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id),
            final(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            final(krnl).cpu_arr.spec_index(cpu_id).value.being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).value.being_killed(),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() is None,
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*final(krnl))),
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
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
            final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state)),
            final(lctx).kernel_call_perm() is None,
    {
        proof {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let t = cpu.view().view().current_thread->Some_0;
            assert(cpu.being_killed() ==> krnl.thr_mp.spec_index(t).locked_by_thread(lctx.thread_id())) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedArray::typed_lock_map_aligned); };
            assert(!cpu.being_killed()) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedMap::typed_lock_map_aligned); };
        }
        let tracked thread_lock_perm = thread_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
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
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, thread_lock_perm: Tracked<LockPerm>, process_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
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
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl)),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
            final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id),
            final(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).locking_thread() is None,
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() is None,
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*final(krnl))),
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
            final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
            final(steps).snapshot_k() == *final(krnl),
            final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state)),
            final(lctx).kernel_call_perm() is None,
    {
        proof {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let t = cpu.view().view().current_thread->Some_0;
            assert(cpu.being_killed() ==> krnl.thr_mp.spec_index(t).locked_by_thread(lctx.thread_id())) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedArray::typed_lock_map_aligned); };
            assert(!cpu.being_killed()) by { thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); reveal(LockedMap::typed_lock_map_aligned); };
        }
        let tracked thread_lock_perm = thread_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
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

use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_spec::*;
use super::syscall_alloc_quota_trace::*;
use super::syscall_alloc_quota_eof::*;
verus! {
    pub(super) fn commit_alloc_quota_4k(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        process_ptr: RwLockProcessPtr,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        alloc_amount: usize,
        cpu_lock_perm: Tracked<LockPerm>,
        container_lock_perm: Tracked<LockPerm>,
        quota_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, allc_4k_mp: old(krnl).allc_4k_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
            old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).locking_thread() is None,
            old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            container_lock_perm.view().state() is WriteLock,
            container_lock_perm.view().thread_id() == old(lctx).thread_id(),
            container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            old(krnl).ctn_mp.spec_index(container_ptr).being_killed() == false,
            !old(krnl).ctn_mp.spec_index(container_ptr).view().zombie,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota.is_init(),
            quota_lock_perm.view().state() is WriteLock,
            quota_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_lock_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write),
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom() =~= set![container_ptr],
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom() =~= set![alloc_ptr_4k],
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            alloc_amount <= usize::MAX - old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k,
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota.view().value >= alloc_amount,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == if alloc_amount > 0 { old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }) } else { old(steps).view() },
            alloc_quota_4k_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, RetValueType::Success),
            final(steps).nonlock_view() == if alloc_amount > 0 {
                old(steps).nonlock_view().push(KernelStep {
                    old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)),
                })
            } else { old(steps).nonlock_view() },
            alloc_amount == 0 ==> final(steps).nonlock_view() == old(steps).nonlock_view(),
            alloc_amount > 0 ==> alloc_quota_4k_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, alloc_amount),
            alloc_amount > 0 ==> alloc_quota_4k_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, alloc_amount),
    {
        proof {
            assert(
                krnl.prc_mp.perms_wf()
                && krnl.allc_4k_mp.perms_wf()
                && krnl.prc_mp.spec_index(process_ptr).is_init()
            ) by { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, alloc_ptr_4k); };
        }
        if alloc_amount > 0 {
            let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm.borrow()));
            process_mut.quota_4k = process_mut.quota_4k + alloc_amount;
            let quota_mut = krnl.allc_4k_mp.borrow_mut_quota_typed(alloc_ptr_4k, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_lock_perm.borrow()));
            quota_mut.value = quota_mut.value - alloc_amount;
        }

        proof {
            if alloc_amount > 0 {
                assert(commit_alloc_quota_4k_eof_transition_framing(&*old(krnl), &*krnl, process_ptr, alloc_ptr_4k, alloc_amount)) by { reveal(commit_alloc_quota_4k_eof_transition_framing); };
                commit_alloc_quota_4k_eof(&*old(krnl), &*krnl, container_ptr, process_ptr, alloc_ptr_4k, alloc_amount);
            }
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
        krnl.wunlock_allocator_quota_4k(alloc_ptr_4k, Tracked(&mut *lctx), quota_lock_perm);
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
        proof {
            if alloc_amount > 0 {
                let quota_before = steps.view();
                assert(kernel_process_quota_4k_changed(&steps.snapshot_k(), &*krnl, cpu_id, process_ptr, container_ptr, alloc_amount as int)) by {
                    reveal(kernel_process_quota_4k_changed);
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                    reveal(kernel_pagetable_nonlock_fields_unchanged);
                    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                    broadcast use kernel_endpoint_nonlock_fields_unchanged_transitive;
                };
                steps.end_kernel_step_process_quota_4k_changed(&*krnl, &*lctx, cpu_id, process_ptr, container_ptr, alloc_amount as int);
                assert(alloc_quota_4k_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount, RetValueType::Success)
                    && alloc_quota_4k_step_pre(steps.nonlock_view().last().old_u, cpu_id, alloc_amount)
                    && alloc_quota_4k_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, alloc_amount)) by {
                    alloc_quota_4k_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, alloc_amount);
                    alloc_quota_4k_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, process_ptr, container_ptr, alloc_amount);
                    alloc_quota_4k_trace_step(&*steps, quota_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount);
                };
            }
            if alloc_amount == 0 {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_process_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, alloc_amount, RetValueType::Success);
            }
        }
    }

    pub(super) fn commit_alloc_thread_quota_4k(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        alloc_amount: usize,
        cpu_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        thread_lock_perm: Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
            old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread() is None,
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
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
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            0 < alloc_amount <= old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k,
            alloc_amount <= usize::MAX - old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            alloc_thread_quota_4k_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, RetValueType::Success),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
            alloc_thread_quota_4k_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, alloc_amount),
            alloc_thread_quota_4k_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, alloc_amount),
    {
        proof {
            assert(
                krnl.prc_mp.perms_wf()
                && krnl.thr_mp.perms_wf()
                && krnl.prc_mp.spec_index(process_ptr).is_init()
                && krnl.thr_mp.spec_index(thread_ptr).is_init()
            ) by { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
        }
        let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm.borrow()));
        process_mut.quota_4k = process_mut.quota_4k - alloc_amount;
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm.borrow()));
        thread_mut.quota_4k = thread_mut.quota_4k + alloc_amount;

        proof {
            assert(commit_alloc_thread_quota_4k_eof_transition_framing(&*old(krnl), &*krnl, process_ptr, thread_ptr, alloc_amount)) by { reveal(commit_alloc_thread_quota_4k_eof_transition_framing); };
            commit_alloc_thread_quota_4k_eof(&*old(krnl), &*krnl, container_ptr, process_ptr, thread_ptr, alloc_amount);
        }
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), thread_lock_perm);
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
        proof {
            let quota_before = steps.view();
            assert(kernel_process2thread_quota_4k_changed(&steps.snapshot_k(), &*krnl, cpu_id, process_ptr, thread_ptr, alloc_amount as int)) by {
                reveal(kernel_process2thread_quota_4k_changed);
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            };
            steps.end_kernel_step_process2thread_quota_4k_changed(&*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, alloc_amount as int);
            assert(alloc_thread_quota_4k_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount, RetValueType::Success)
                && alloc_thread_quota_4k_step_pre(steps.nonlock_view().last().old_u, cpu_id, alloc_amount)
                && alloc_thread_quota_4k_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, alloc_amount)) by {
                alloc_thread_quota_4k_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, alloc_amount);
                alloc_thread_quota_4k_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, process_ptr, thread_ptr, alloc_amount);
                alloc_thread_quota_4k_trace_step(&*steps, quota_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount);
            };
        }
    }

    pub(super) fn commit_alloc_quota_2m(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        process_ptr: RwLockProcessPtr,
        alloc_ptr_2m: RwLockPageAllocatorPtr,
        alloc_amount: usize,
        cpu_lock_perm: Tracked<LockPerm>,
        container_lock_perm: Tracked<LockPerm>,
        quota_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, allc_2m_mp: old(krnl).allc_2m_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
            old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).locking_thread() is None,
            old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            container_lock_perm.view().state() is WriteLock,
            container_lock_perm.view().thread_id() == old(lctx).thread_id(),
            container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            old(krnl).ctn_mp.spec_index(container_ptr).being_killed() == false,
            !old(krnl).ctn_mp.spec_index(container_ptr).view().zombie,
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota.is_init(),
            quota_lock_perm.view().state() is WriteLock,
            quota_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_lock_perm.view().lock_id() == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), alloc_ptr_2m, TypedLockMode::Write),
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom() =~= set![container_ptr],
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom() =~= set![alloc_ptr_2m],
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
            alloc_amount <= usize::MAX - old(krnl).prc_mp.spec_index(process_ptr).view().quota_2m,
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota.view().value >= alloc_amount,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == if alloc_amount > 0 { old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }) } else { old(steps).view() },
            alloc_quota_2m_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, RetValueType::Success),
            final(steps).nonlock_view() == if alloc_amount > 0 {
                old(steps).nonlock_view().push(KernelStep {
                    old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)),
                })
            } else { old(steps).nonlock_view() },
            alloc_amount == 0 ==> final(steps).nonlock_view() == old(steps).nonlock_view(),
            alloc_amount > 0 ==> alloc_quota_2m_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, alloc_amount),
            alloc_amount > 0 ==> alloc_quota_2m_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, alloc_amount),
    {
        proof {
            assert(krnl.prc_mp.perms_wf() && krnl.allc_2m_mp.perms_wf() && krnl.prc_mp.spec_index(process_ptr).is_init()) by {
                process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, alloc_ptr_2m);
            };
        }
        if alloc_amount > 0 {
            let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm.borrow()));
            process_mut.quota_2m = process_mut.quota_2m + alloc_amount;
            let quota_mut = krnl.allc_2m_mp.borrow_mut_quota_typed(alloc_ptr_2m, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(quota_lock_perm.borrow()));
            quota_mut.value = quota_mut.value - alloc_amount;
        }

        proof {
            if alloc_amount > 0 {
                assert(commit_alloc_quota_2m_eof_transition_framing(&*old(krnl), &*krnl, process_ptr, alloc_ptr_2m, alloc_amount)) by { reveal(commit_alloc_quota_2m_eof_transition_framing); };
                commit_alloc_quota_2m_eof(&*old(krnl), &*krnl, container_ptr, process_ptr, alloc_ptr_2m, alloc_amount);
            }
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
        krnl.wunlock_allocator_quota_2m(alloc_ptr_2m, Tracked(&mut *lctx), quota_lock_perm);
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
        proof {
            if alloc_amount > 0 {
                let quota_before = steps.view();
                assert(kernel_process_quota_2m_changed(&steps.snapshot_k(), &*krnl, cpu_id, process_ptr, container_ptr, alloc_amount as int)) by {
                    reveal(kernel_process_quota_2m_changed);
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                    reveal(kernel_pagetable_nonlock_fields_unchanged);
                    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                    broadcast use kernel_endpoint_nonlock_fields_unchanged_transitive;
                };
                steps.end_kernel_step_process_quota_2m_changed(&*krnl, &*lctx, cpu_id, process_ptr, container_ptr, alloc_amount as int);
                assert(alloc_quota_2m_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount, RetValueType::Success)
                    && alloc_quota_2m_step_pre(steps.nonlock_view().last().old_u, cpu_id, alloc_amount)
                    && alloc_quota_2m_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, alloc_amount)) by {
                    alloc_quota_2m_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, alloc_amount);
                    alloc_quota_2m_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, process_ptr, container_ptr, alloc_amount);
                    alloc_quota_2m_trace_step(&*steps, quota_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount);
                };
            }
            if alloc_amount == 0 {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_process_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, alloc_amount, RetValueType::Success);
            }
        }
    }

    pub(super) fn commit_alloc_thread_quota_2m(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        process_ptr: RwLockProcessPtr,
        thread_ptr: RwLockThreadPtr,
        alloc_amount: usize,
        cpu_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        thread_lock_perm: Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
            old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread() is None,
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
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
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            0 < alloc_amount <= old(krnl).prc_mp.spec_index(process_ptr).view().quota_2m,
            alloc_amount <= usize::MAX - old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            alloc_thread_quota_2m_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, RetValueType::Success),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
            alloc_thread_quota_2m_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, alloc_amount),
            alloc_thread_quota_2m_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, alloc_amount),
    {
        proof {
            assert(
                krnl.prc_mp.perms_wf()
                && krnl.thr_mp.perms_wf()
                && krnl.prc_mp.spec_index(process_ptr).is_init()
                && krnl.thr_mp.spec_index(thread_ptr).is_init()
            ) by { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
        }
        let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm.borrow()));
        process_mut.quota_2m = process_mut.quota_2m - alloc_amount;
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm.borrow()));
        thread_mut.quota_2m = thread_mut.quota_2m + alloc_amount;

        proof {
            assert(commit_alloc_thread_quota_2m_eof_transition_framing(&*old(krnl), &*krnl, process_ptr, thread_ptr, alloc_amount)) by { reveal(commit_alloc_thread_quota_2m_eof_transition_framing); };
            commit_alloc_thread_quota_2m_eof(&*old(krnl), &*krnl, container_ptr, process_ptr, thread_ptr, alloc_amount);
        }
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), thread_lock_perm);
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
        proof {
            let quota_before = steps.view();
            assert(kernel_process2thread_quota_2m_changed(&steps.snapshot_k(), &*krnl, cpu_id, process_ptr, thread_ptr, alloc_amount as int)) by {
                reveal(kernel_process2thread_quota_2m_changed);
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            };
            steps.end_kernel_step_process2thread_quota_2m_changed(&*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, alloc_amount as int);
            assert(alloc_thread_quota_2m_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount, RetValueType::Success)
                && alloc_thread_quota_2m_step_pre(steps.nonlock_view().last().old_u, cpu_id, alloc_amount)
                && alloc_thread_quota_2m_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, alloc_amount)) by {
                alloc_thread_quota_2m_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, alloc_amount);
                alloc_thread_quota_2m_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, process_ptr, thread_ptr, alloc_amount);
                alloc_thread_quota_2m_trace_step(&*steps, quota_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount);
            };
        }
    }
}

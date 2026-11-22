#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_split_2m_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_split_2m_trace::*;

verus! {
pub fn syscall_split_2m(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, n: usize) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret is SuccessUsize ==> old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some,
        ret is SuccessUsize ==> old(krnl).thrd_mp.dom().contains(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0),
        ret is SuccessUsize ==> old(krnl).ctn_mp.dom().contains(old(krnl).thrd_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().owning_container),
        ret is SuccessUsize ==> ret->SuccessUsize_value == n,
        split_2m_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), cpu_id, n, ret),
        split_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, n, ret),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if n > usize::MAX / 512 {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            split_2m_empty_trace_implies_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), cpu_id, n, RetValueType::Error);
            split_2m_result_from_k(old(krnl), cpu_id, n, RetValueType::Error);
        }
        return RetValueType::Error;
    }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            split_2m_empty_trace_implies_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), cpu_id, n, RetValueType::CpuIdle);
            split_2m_result_from_k(old(krnl), cpu_id, n, RetValueType::CpuIdle);
        }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let locked = mmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    if locked.is_none() {
        proof {
            split_2m_empty_trace_implies_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), cpu_id, n, RetValueType::ErrorThreadKilled);
            split_2m_result_from_k(old(krnl), cpu_id, n, RetValueType::ErrorThreadKilled);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let (_prc_ptr, thrd_ptr, ctn_ptr, alloc_ptr_4k, _pagetable_ptr, _quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)) = locked.unwrap();
    proof { thread_perms_wf_map(krnl.thrd_mp); }
    let quota_2m = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm)).quota_2m;
    let ret = if quota_2m < n { RetValueType::ErrorNoQuota }
    else if n == 0 { RetValueType::SuccessUsize { value: 0 } }
    else {
        proof { container_perms_wf_at(krnl.ctn_mp, ctn_ptr); }
        let container_ro = krnl.ctn_mp.borrow_rodata(ctn_ptr);
        let alloc_ptr_2m = container_ro.borrow().allocator_ptr_2m;
        assert(krnl.allc_2m_mp.dom().contains(alloc_ptr_2m)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); };
        let Tracked(source_locks) = freeze_split_2m_sources(krnl, alloc_ptr_4k, alloc_ptr_2m, Tracked(&mut *lctx));
        let mut source = 0usize;
        let mut m = 0usize;
        proof {
            container_allocator_wf_at(steps.snapshot_k().ctn_mp, steps.snapshot_k().allc_4k_mp, steps.snapshot_k().allc_2m_mp, steps.snapshot_k().allc_1g_mp, ctn_ptr);
            let snap = steps.snapshot_k();
            allocator_free_page_ptrs_wf_implies_free_count_fold_bounded(snap.allc_4k_mp, alloc_ptr_4k);
            container_thread_wf_thread_at(snap.ctn_mp, snap.thrd_mp, thrd_ptr);
            container_allocator_4k_forward_wf_at(snap.ctn_mp, snap.allc_4k_mp, snap.allc_2m_mp, snap.allc_1g_mp, alloc_ptr_4k);
            container_process_allocator_quota_4k_wf_at(snap.ctn_mp, snap.prc_mp, snap.thrd_mp, snap.allc_4k_mp, ctn_ptr);
            container_thread_and_perms_wf_implies_4k_fold_sum_ge_thread_quota(snap.ctn_mp, snap.prc_mp, snap.thrd_mp, ctn_ptr, thrd_ptr);
            split_2m_empty_trace_implies_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), cpu_id, n, RetValueType::SuccessUsize { value: 0 });
        }
        while m < n
            invariant
                krnl.inv(),
                typed_lock_maps_aligned(krnl, lctx),
                krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
                krnl.allc_2m_mp.dom().contains(alloc_ptr_2m),
                forall|cpu: CpuId| #![trigger source_locks.cache.dom().contains(cpu)] source_locks.cache.dom().contains(cpu) <==> cpu < NUM_CPUS,
                forall|cpu: CpuId| #![trigger source_locks.cache[cpu]] cpu < NUM_CPUS ==> {
                    &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu), TypedLockMode::Write)
                    &&& source_locks.cache[cpu].state() is WriteLock
                    &&& source_locks.cache[cpu].thread_id() == lctx.thread_id()
                    &&& krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                    &&& source_locks.cache[cpu].lock_id() == krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                },
                forall|held: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(held)] lctx.allocator_cache_2m_lock_map().dom().contains(held) <==> held.0 == alloc_ptr_2m && held.1 < NUM_CPUS,
                lctx.allocator_global_pool_4k_lock_map().dom() =~= set![alloc_ptr_4k],
                lctx.allocator_global_pool_2m_lock_map().dom() =~= set![alloc_ptr_2m],
                typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write),
                typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedLockMode::Write),
                source_locks.pool4k.state() is WriteLock,
                source_locks.pool2m.state() is WriteLock,
                source_locks.pool4k.thread_id() == lctx.thread_id(),
                source_locks.pool2m.thread_id() == lctx.thread_id(),
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread() is Write,
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.locking_thread() is Write,
                source_locks.pool4k.lock_id() == krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
                source_locks.pool2m.lock_id() == krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.locking_thread()->Write_lock_id,
                index_valid(NUM_CPUS, cpu_id),
                lctx.cpu_id() == cpu_id,
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.cpu_lock_map().dom() == set![cpu_id],
                lctx.thread_lock_map().dom() == set![thrd_ptr],
                typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
                typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
                krnl.cpu_op.view().view()[cpu_id as int] is InStep,
                krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
                !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
                krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
                krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(cpu_id),
                cpu_lock_perm.state() is WriteLock,
                cpu_lock_perm.thread_id() == lctx.thread_id(),
                cpu_lock_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == (krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
                krnl.thrd_mp.dom().contains(thrd_ptr),
                !krnl.thrd_mp.spec_index(thrd_ptr).being_killed(),
                krnl.thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
                krnl.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
                krnl.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
                krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
                !krnl.thrd_mp.spec_index(thrd_ptr).view().exited.view(),
                krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
                krnl.thrd_mp.spec_index(thrd_ptr).wlocked_by_thread(cpu_id),
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == krnl.thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
                krnl.ctn_mp.dom().contains(ctn_ptr),
                krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
                !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
                old(krnl).thrd_mp.dom().contains(thrd_ptr),
                !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
                old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == quota_2m,
                old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
                old(krnl).ctn_mp.dom().contains(ctn_ptr),
                old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                steps.snapshot_k().inv(),
                steps.snapshot_k().thrd_mp.dom().contains(thrd_ptr),
                steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).view().quota_4k <= usize::MAX - 512,
                krnl.allc_4k_mp.dom() == steps.snapshot_k().allc_4k_mp.dom(),
                krnl.allc_2m_mp.dom() == steps.snapshot_k().allc_2m_mp.dom(),
                forall|allocator: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(allocator)] steps.snapshot_k().allc_4k_mp.dom().contains(allocator) ==>
                    krnl.allc_4k_mp.spec_index(allocator).quota == steps.snapshot_k().allc_4k_mp.spec_index(allocator).quota,
                forall|allocator: RwLockPageAllocatorPtr| #![trigger krnl.allc_2m_mp.spec_index(allocator)] steps.snapshot_k().allc_2m_mp.dom().contains(allocator) ==>
                    krnl.allc_2m_mp.spec_index(allocator).quota == steps.snapshot_k().allc_2m_mp.spec_index(allocator).quota,
                *krnl == (KernelK { pg_arr: krnl.pg_arr, allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp,
                    cpu_arr: krnl.cpu_arr, cpu_op: krnl.cpu_op, thrd_mp: krnl.thrd_mp, ..steps.snapshot_k() }),
                krnl.cpu_arr.entries_unchanged_except(&steps.snapshot_k().cpu_arr, cpu_id),
                krnl.cpu_arr.spec_index(cpu_id).view().view().view() == steps.snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
                krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == steps.snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed(),
                krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == steps.snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
                forall|other: CpuId| #![trigger krnl.cpu_op.view().view().spec_index(other as int)] index_valid(NUM_CPUS, other) && other != cpu_id ==>
                    krnl.cpu_op.view().view().spec_index(other as int) == steps.snapshot_k().cpu_op.view().view().spec_index(other as int),
                krnl.thrd_mp.unchanged_except(&steps.snapshot_k().thrd_mp, thrd_ptr),
                krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).being_killed(),
                krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { quota_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
                    quota_2m: krnl.thrd_mp.spec_index(thrd_ptr).view().quota_2m, ..steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).view() }),
                m < n || m == 0 ==> krnl.thrd_mp.spec_index(thrd_ptr).view().quota_4k == steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).view().quota_4k
                    && krnl.thrd_mp.spec_index(thrd_ptr).view().quota_2m == steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).view().quota_2m,
                m > 0 && m == n ==> krnl.thrd_mp.spec_index(thrd_ptr).view().quota_4k == steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).view().quota_4k + 512
                    && krnl.thrd_mp.spec_index(thrd_ptr).view().quota_2m + 1 == steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).view().quota_2m,
                old(steps).view().len() <= steps.view().len(),
                steps.view().len() == old(steps).view().len() + if m == n { m as int - 1 } else { m as int },
                steps.view().len() == old(steps).view().len() ==> steps.snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
                !(steps.snapshot_k().cpu_op.view().view()[cpu_id as int] is User),
                steps.view().len() == old(steps).view().len() ==> steps.snapshot_k().cpu_arr.spec_index(cpu_id).view().locking_thread() is None,
                steps.view().len() == old(steps).view().len() ==> steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).locking_thread() is None,
                steps.view().len() > old(steps).view().len() ==> steps.snapshot_k().cpu_op.view().view()[cpu_id as int] is InStep,
                steps.view().len() > old(steps).view().len() ==> steps.snapshot_k().cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(cpu_id),
                steps.view().len() > old(steps).view().len() ==> steps.snapshot_k().thrd_mp.spec_index(thrd_ptr).wlocked_by_thread(cpu_id),
                split_2m_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), cpu_id, n,
                    RetValueType::SuccessUsize { value: if m == n { (m - 1) as usize } else { m } }),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
                lctx.page_lock_map().dom().is_empty(),
                lctx.pcid_needflush_lock_map().dom().is_empty(),
                lctx.cpu_offline_flag_lock_map().dom().is_empty(),
                lctx.container_lock_map().dom().is_empty(),
                lctx.process_lock_map().dom().is_empty(),
                lctx.endpoint_lock_map().dom().is_empty(),
                lctx.scheduler_lock_map().dom().is_empty(),
                lctx.pcid_allocator_lock_map().dom().is_empty(),
                lctx.cpu_set_lock_map().dom().is_empty(),
                lctx.pagetable_lock_map().dom().is_empty(),
                lctx.pagetable_window_lock_map().dom().is_empty(),
                lctx.iommu_table_lock_map().dom().is_empty(),
                lctx.iommu_root_table_lock_map().dom().is_empty(),
                lctx.allocator_quota_4k_lock_map().dom().is_empty(),
                lctx.allocator_quota_2m_lock_map().dom().is_empty(),
                lctx.allocator_cache_4k_lock_map().dom().is_empty(),
                lctx.allocator_quota_1g_lock_map().dom().is_empty(),
                lctx.allocator_cache_1g_lock_map().dom().is_empty(),
                lctx.allocator_global_pool_1g_lock_map().dom().is_empty(),
                source <= NUM_CPUS,
                forall|s: usize| #![trigger krnl.allc_2m_mp.spec_index(alloc_ptr_2m).merge_2m_source_list(s)] s < source ==> {
                    &&& krnl.allc_2m_mp.spec_index(alloc_ptr_2m).merge_2m_source_list(s).length == 0
                    &&& krnl.allc_2m_mp.spec_index(alloc_ptr_2m).merge_2m_source_list(s).view().len() == 0
                },
                m <= n,
                n <= usize::MAX / 512,
                m < n ==> lctx.kernel_view_locking_state() is Acquire,
                krnl.thrd_mp.spec_index(thrd_ptr).view().quota_2m + m == quota_2m,
                quota_2m >= n,
            decreases n - m,
        {
            proof { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); }
            proof {
                container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
                container_allocator_2m_forward_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, alloc_ptr_2m);
                container_process_allocator_quota_2m_wf_at(krnl.ctn_mp, krnl.prc_mp, krnl.thrd_mp, krnl.allc_2m_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container);
                container_thread_and_perms_wf_implies_2m_fold_sum_ge_thread_quota(krnl.ctn_mp, krnl.prc_mp, krnl.thrd_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container, thrd_ptr);
            }
            let head = split_2m_select_source(krnl, alloc_ptr_2m, &mut source, Tracked(&*lctx), Tracked(&source_locks.cache), Tracked(&source_locks.pool2m));
            let Tracked(page_locks) = merge_2m_lock_block(krnl, head, Tracked(&mut *lctx));
            split_2m_commit(krnl, thrd_ptr, alloc_ptr_4k, alloc_ptr_2m, head, source, Tracked(&*lctx),
                Tracked(&source_locks.cache), Tracked(&source_locks.pool4k), Tracked(&source_locks.pool2m),
                Tracked(&thread_lock_perm), Tracked(&page_locks));
            merge_2m_unlock_block(krnl, head, Tracked(&mut *lctx), Tracked(page_locks));
            m += 1;
            if m < n {
                proof {
                    let before_trace = steps.view();
                    let before_business = steps.snapshot_k();
                    let after_business = *krnl;
                    split_2m_step_pre_from_k(&before_business, cpu_id, thrd_ptr);
                    split_2m_step_from_k(&before_business, &after_business, cpu_id, thrd_ptr);
                    krnl.kernel_step_boundary_free_2m_block_split(&mut *lctx, &mut *steps, thrd_ptr, alloc_ptr_4k, alloc_ptr_2m);
                    split_2m_recorded_step_implies_extended_trace(before_trace, steps.view(), old(steps).view().len() as int,
                        before_business, after_business, cpu_id, n, (m - 1) as usize);
                }
            }
        }
        thaw_split_2m_sources(krnl, alloc_ptr_4k, alloc_ptr_2m, Tracked(&mut *lctx), Tracked(source_locks));
        RetValueType::SuccessUsize { value: m }
    };
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let before_trace = steps.view();
        let before_business = steps.snapshot_k();
        let after_business = *krnl;
        let count = if ret is SuccessUsize { ret->SuccessUsize_value } else { 0usize };
        if count > 0 {
            split_2m_step_pre_from_k(&before_business, cpu_id, thrd_ptr);
            split_2m_step_from_k(&before_business, &after_business, cpu_id, thrd_ptr);
            steps.end_kernel_step_thread_quota_4k_changed(&*krnl, &*lctx, thrd_ptr);
            split_2m_recorded_step_implies_extended_trace(before_trace, steps.view(), old(steps).view().len() as int,
                before_business, after_business, cpu_id, n, (count - 1) as usize);
        } else {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            split_2m_empty_trace_implies_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), cpu_id, n, ret);
        }
        split_2m_result_from_k(old(krnl), cpu_id, n, ret);
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
    }
    ret
}
}

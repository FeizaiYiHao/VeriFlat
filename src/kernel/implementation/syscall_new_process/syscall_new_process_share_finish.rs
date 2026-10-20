use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_spec::*;
use super::syscall_new_process_trace::*;
use super::syscall_new_process_helpers::create_initial_thread_and_finish_new_process;

verus! {
/// Shares the caller's range into the published child and finishes the call: the share steps and the finish step
/// after the partial trace that starts at `start`.
pub(super) fn share_and_finish_new_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, source_range: &VaRange4K,
    container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr, allocator_ptr: RwLockPageAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot, target_pagetable_ptr: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, cpu_lock_perm: Tracked<LockPerm>,
    child_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<Option<LockPerm>>,
    source_pagetable_lock_perm: Tracked<LockPerm>, target_pagetable_lock_perm: Tracked<LockPerm>, iommu_table_lock_perm: Tracked<Option<LockPerm>>,
    initial_regs: &Registers, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        0 <= start <= old(steps).view().len(),
        new_process_trace_after_publish(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, *source_range, *initial_regs,
            if endpoint is Some { Some(endpoint_index) } else { None }, iommu_table is Some),
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        source_range.wf(),
        source_range.len > 0,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![child_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm.view() is Some
            &&& endpoint_lock_perm.view()->Some_0.state() is WriteLock
            &&& endpoint_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm.view()->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, target_pagetable_ptr],
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        iommu_table is None ==> old(lctx).iommu_table_lock_map().dom().is_empty(),
        iommu_table is Some ==> {
            let iommu_table_ptr = iommu_table->Some_0;
            &&& old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table_ptr]
            &&& old(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write)
            &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& iommu_table_lock_perm.view() is Some
            &&& iommu_table_lock_perm.view()->Some_0.state() is WriteLock
            &&& iommu_table_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& iommu_table_lock_perm.view()->Some_0.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).prc_mp.dom().contains(child_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_ptr).view().state.view() is Creating,
        !old(krnl).prc_mp.spec_index(child_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().pagetable == target_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        child_lock_perm.view().state() is WriteLock,
        child_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        parent_ptr != child_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: 0,
            origin: Share4kOrigin::NewProcess(NewProcessProgress {
                range: *source_range, regs: *initial_regs, endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, with_iommu: iommu_table is Some, child: Some(child_ptr),
            }),
        }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != target_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).leaves_present(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr)),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable_ptr, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).view().proc_ptr == child_ptr,
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).is_empty(),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, target_pagetable_ptr, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr)),
        target_pagetable_lock_perm.view().state() is WriteLock,
        target_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        old(steps).view().len() as int + source_range.len as int + 1 <= final(steps).view().len() as int <= old(steps).view().len() as int + 4 * source_range.len as int + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_process_commit_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, *source_range, *initial_regs,
            if endpoint is Some { Some(endpoint_index) } else { None }, iommu_table is Some),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        old(steps).nonlock_view().len() as int + source_range.len as int + 1 <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int + 1,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_u_new_thread_changed(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, child_ptr, current_thread_ptr, container_ptr, cpu_id,
            new_thread_ptr, *initial_regs, endpoint, None),
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        endpoint is Some ==> final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        endpoint is Some ==> final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == endpoint,
        iommu_table is Some ==> final(krnl).prc_mp.dom().contains(child_ptr) && final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().is_empty(),
{
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked target_pagetable_lock_perm = target_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let ghost endpoint_index_opt: Option<EndpointIdx> = if endpoint is Some { Some(endpoint_index) } else { None };
    proof {
        assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); };
        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable_ptr, container_ptr, source_range)) by {
            process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, parent_ptr);
            share_mapping_4k_range_owner_compatible_own_container(krnl, source_pagetable_ptr, container_ptr, source_range);
        };
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable_ptr).spec_mapping_4k_va_range_empty(source_range.start, source_range.view().spec_index((source_range.len - 1) as int))) by { reveal(PageTableC::spec_mapping_4k_va_range_empty); };
        assert({
            &&& share_4k_objects_k(*krnl, cpu_id).source_thread == current_thread_ptr && share_4k_objects_k(*krnl, cpu_id).quota_thread == current_thread_ptr
            &&& share_4k_objects_k(*krnl, cpu_id).target == child_ptr && share_4k_objects_k(*krnl, cpu_id).target_container == container_ptr
            &&& share_4k_objects_k(*krnl, cpu_id).transfer_source is None
        }) by { reveal(share_4k_objects_k); };
    }
    let ghost origin = Share4kOrigin::NewProcess(NewProcessProgress { range: *source_range, regs: *initial_regs, endpoint_index: endpoint_index_opt, with_iommu: iommu_table is Some, child: Some(child_ptr) });
    let ghost share_before = steps.view();
    share_mapping_4k_build_and_share(
        krnl, source_range, source_range, allocator_ptr, current_thread_ptr, current_thread_ptr, current_thread_ptr, child_ptr, container_ptr, cpu_id,
        source_pagetable_ptr, target_pagetable_ptr, None, Ghost(origin), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm),
        Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm), Tracked(None), Tracked(None),
    );
    proof {
        assert(new_process_trace_after_share(steps.view(), start, pre, cpu_id, *source_range, *initial_regs, endpoint_index_opt, iommu_table is Some)) by {
            new_process_trace_share_steps(&*steps, share_before, start, pre, cpu_id, *source_range, *initial_regs, endpoint_index_opt, iommu_table is Some);
        };
        assert(krnl.sched_mp.dom().contains(scheduler_ptr) && krnl.sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id).major == SCHEDULER_LOCK_MAJOR) by { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); };
    }
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        if let Some(endpoint_ptr) = endpoint {
            assert(krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
                && krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by {
                thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); thread_endpoint_ref_counter_wf_endpoint_at(krnl.thr_mp, krnl.ep_mp, endpoint_ptr, current_thread_ptr, endpoint_index);
            };
        }
        assert(krnl.prc_mp.spec_index(child_ptr).view().pagetable == target_pagetable_ptr) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, child_ptr); };
    }
    let ghost finish_before = steps.view();
    let new_thread_ptr = create_initial_thread_and_finish_new_process(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, scheduler_ptr,
        endpoint, endpoint_index, source_pagetable_ptr, target_pagetable_ptr, iommu_table, cpu_lock_perm,
        child_lock_perm, Tracked(current_thread_lock_perm), Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm),
        Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), iommu_table_lock_perm, initial_regs,
    );
    proof {
        assert(new_process_commit_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, *source_range, *initial_regs, endpoint_index_opt, iommu_table is Some)) by {
            new_process_trace_finish_step(&*steps, finish_before, start, pre, cpu_id, *source_range, *initial_regs, endpoint_index_opt, iommu_table is Some);
        };
    }
    new_thread_ptr
}
} // verus!

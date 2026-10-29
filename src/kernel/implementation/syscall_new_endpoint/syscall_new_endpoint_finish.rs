use vstd::prelude::*;
use crate::*;
use super::syscall_new_endpoint_spec::*;
use super::syscall_new_endpoint_trace::*;

verus! {
/// Creates the endpoint on the staged page, releases every held lock, and ends the finish step of the trace that starts at
/// `start` on `pre`.
pub(super) fn finish_new_endpoint_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, page_ptr: PagePtr,
    Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(container_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        0 <= start <= old(steps).view().len(),
        new_endpoint_trace_after_enter(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, endpoint_index),
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        edp_idx_valid(endpoint_index),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed() == false,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        container_lock_perm.state() is WriteLock && container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        process_lock_perm.state() is WriteLock && process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewEndpoint { slot: endpoint_index }),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(page_ptr),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock && page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
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
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        new_endpoint_syscall_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, true),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
{
    let page_index = page_ptr2page_index(page_ptr);
    proof { new_endpoint_finish_step_pre_from_k(&*krnl, &*lctx, cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index); }
    let Tracked(endpoint_lock_perm) = create_endpoint_from_staged_page(
        krnl, page_ptr, container_ptr, thread_ptr, endpoint_index, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(&container_lock_perm), Tracked(&thread_lock_perm),
    );
    krnl.wunlock_endpoint(page_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_lock_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost finish_k = steps.snapshot_k();
        let ghost finish_before = steps.view();
        assert(kernel_new_endpoint_fields(&finish_k, krnl, container_ptr, thread_ptr, endpoint_index, page_ptr, None)) by {
            reveal(kernel_new_endpoint_fields); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        };
        steps.end_kernel_step_new_endpoint(&*krnl, &*lctx, container_ptr, thread_ptr, endpoint_index, page_ptr);
        assert(new_endpoint_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, true)) by {
            kernel_new_endpoint_fields_and_unlocks_implies_u_step(&finish_k, &*krnl, cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index, page_ptr);
            new_endpoint_finish_step_from_u(kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index, page_ptr);
            new_endpoint_trace_finish_step(&*steps, finish_before, start, pre, kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index);
        };
    }
}
} // verus!

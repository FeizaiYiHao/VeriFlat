use vstd::prelude::*;
use crate::*;
use super::syscall_new_endpoint_spec::*;
use super::syscall_new_endpoint_trace::*;

verus! {
/// Commit path: allocate a 4K page, create the endpoint at `endpoint_index`, release all locks.
pub(super) fn commit_new_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
    container_lock_perm: Tracked<LockPerm>, process_lock_perm: Tracked<LockPerm>, thread_lock_perm: Tracked<LockPerm>, cpu_lock_perm: Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread() is None,
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        container_lock_perm.view().state() is WriteLock,
        container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed() == false,
        !old(krnl).ctn_mp.spec_index(container_ptr).view().zombie,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is None,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(steps).view().len() == old(steps).view().len() + 2,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 2,
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        new_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, true),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
{
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked thread_lock_perm = thread_lock_perm.get();
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::NewEndpoint { slot: endpoint_index })), Tracked(&*lctx), Tracked(&thread_lock_perm));
    proof {
        assert(steps.snapshot_k().thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        let ghost enter_lctx = *lctx;
        let ghost enter_before = steps.view();
        let ghost entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(new_endpoint_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index)) by {
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&old(steps).snapshot_k(), old(krnl), &enter_lctx, cpu_id, process_ptr, thread_ptr, None, true, Some(container_ptr), false, None);
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, thread_ptr);
            new_endpoint_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index);
            new_endpoint_trace_enter_step(&*steps, enter_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, endpoint_index);
        };
    }
    let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_lock_perm));
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
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost finish_k = steps.snapshot_k();
        let ghost finish_before = steps.view();
        assert(kernel_new_endpoint_fields(&finish_k, krnl, container_ptr, thread_ptr, endpoint_index, page_ptr, None)) by {
            reveal(kernel_new_endpoint_fields); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        };
        steps.end_kernel_step_new_endpoint(&*krnl, &*lctx, container_ptr, thread_ptr, endpoint_index, page_ptr);
        assert(new_endpoint_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, true)) by {
            kernel_new_endpoint_fields_and_unlocks_implies_u_step(&finish_k, &*krnl, cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index, page_ptr);
            new_endpoint_finish_step_from_u(kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index, page_ptr);
            new_endpoint_trace_finish_step(&*steps, finish_before, old(steps).view().len() as int, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(finish_k),
                kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index);
        };
    }
}
}

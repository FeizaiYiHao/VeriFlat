use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;

verus! {
/// Leaf step of the reclaim walk: clears the present user 4K leaf `va` of the write-locked page table `pagetable` of
/// `process_ptr` and pushes the leaf step onto the partial trace that starts at `start`; the held cpu, container, process,
/// thread, and IOMMU table stay unchanged.
pub(super) fn thread_exit_reclaim_clear_leaf(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Ghost(cpu_id): Ghost<CpuId>,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, Ghost(thread_ptr): Ghost<RwLockThreadPtr>,
    pagetable: RwLockPageTableRoot, va: VAddr, Ghost(iommu_table): Ghost<Option<RwLockPageTableRoot>>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).cpu_id() == cpu_id,
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        iommu_table is Some ==> old(lctx).iommu_table_lock_map().dom().contains(iommu_table->Some_0),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present,
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr) && final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr) && final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr) && final(krnl).thr_mp.spec_index(thread_ptr) == old(krnl).thr_mp.spec_index(thread_ptr),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().insert(va, MapEntry { present: false, ..old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va) }),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
{
    let ghost leaf_k = *krnl;
    let ghost leaf_lctx = *lctx;
    let ghost leaf_before = steps.view();
    clear_4k_mapping_present(krnl, pagetable, va, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    proof {
        let leaf_post = *krnl;
        assert(kernel_process_4k_mapping_changed(&leaf_k, &leaf_post, process_ptr, pagetable, va)) by { reveal(kernel_process_4k_mapping_changed); };
        krnl.kernel_step_boundary_process_4k_mapping_changed(&mut *lctx, &mut *steps, process_ptr, pagetable, va, process_ptr, pagetable, thread_ptr, thread_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
            thread_exit_leaf_step_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, va);
            kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(&leaf_k, &leaf_post, pagetable, va, thread_ptr);
            thread_exit_leaf_step_from_u(kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id, process_ptr, thread_ptr, va);
            thread_exit_trace_push(&*steps, leaf_before, start, pre, kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id);
        };
    }
}
} // verus!

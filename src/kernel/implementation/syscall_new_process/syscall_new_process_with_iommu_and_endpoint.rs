use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_spec::kernel_u_new_process_shared;
use super::syscall_new_process_common::syscall_new_process_common;

verus! {
#[verifier::spinoff_prover]
pub fn syscall_new_process_with_iommu_and_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    range: usize, endpoint_index: EndpointIdx, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessThreeUsize ==> {
            let parent_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
            let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let container_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
            let child_ptr = ret->SuccessThreeUsize_value1;
            let iommu_table_ptr = ret->SuccessThreeUsize_value2;
            let thread_ptr = ret->SuccessThreeUsize_value3;
            let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& range as int + 2 <= final(steps).nonlock_view().len() as int
            &&& final(steps).nonlock_view().len() as int <= 4 * range as int + 2
            &&& final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& source_range.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is Some
            &&& kernel_u_create_process_with_iommu_changed(
                final(steps).nonlock_view().spec_index(0).old_u, final(steps).nonlock_view().spec_index(0).new_u,
                parent_ptr, child_ptr, current_thread_ptr,
            )
            &&& kernel_u_new_process_shared(
                final(steps).nonlock_view().spec_index(0).new_u,
                final(steps).nonlock_view().spec_index((final(steps).nonlock_view().len() - 2) as int).new_u,
                parent_ptr, child_ptr, current_thread_ptr, &source_range,
            )
            &&& kernel_u_new_thread_changed(
                final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, child_ptr,
                current_thread_ptr, container_ptr, thread_ptr, *initial_regs,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index),
            )
            &&& final(krnl).prc_mp.dom().contains(child_ptr)
            &&& final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)
            &&& final(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index)
        },
        ret is SuccessThreeUsize || ret is Error || ret is ErrorContainerKilled || ret is ErrorNoPcid || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota,
{
    syscall_new_process_common(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, Some(endpoint_index), true, initial_regs)
}
}

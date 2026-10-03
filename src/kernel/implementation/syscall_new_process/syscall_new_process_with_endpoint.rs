use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_common::syscall_new_process_common;
use super::syscall_new_process_spec::*;

verus! {
#[verifier::spinoff_prover]
pub fn syscall_new_process_with_endpoint(
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
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_process_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, *initial_regs, Some(endpoint_index), false, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessPairUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessPairUsize ==> {
            let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let container_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
            let child_ptr = ret->SuccessPairUsize_value1;
            let thread_ptr = ret->SuccessPairUsize_value2;
            let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& range as int + 3 <= final(steps).nonlock_view().len() as int
            &&& final(steps).nonlock_view().len() as int <= 4 * range as int + 3
            &&& final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& source_range.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is Some
            &&& kernel_u_new_thread_changed(
                final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, child_ptr,
                current_thread_ptr, container_ptr, thread_ptr, *initial_regs,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index), None,
            )
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index)
        },
        (ret is SuccessPairUsize) == (new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, Some(endpoint_index), false) is Success),
        !(ret is SuccessPairUsize) ==> ret == new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, Some(endpoint_index), false),
{
    syscall_new_process_common(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, Some(endpoint_index), false, initial_regs)
}
}

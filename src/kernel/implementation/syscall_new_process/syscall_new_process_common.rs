use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_helpers::commit_new_process;
use super::syscall_new_process_with_iommu_helpers::commit_new_process_with_iommu_and_endpoint;
use super::syscall_new_process_spec::*;
use super::syscall_new_process_trace::*;

verus! {
/// Shared body of the new-process syscalls: `endpoint_index` seeds the child thread, `with_iommu` adds an empty IOMMU table.
#[verifier::spinoff_prover]
pub(super) fn syscall_new_process_common(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    range: usize, endpoint_index: Option<EndpointIdx>, with_iommu: bool, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        with_iommu ==> endpoint_index is Some,
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
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessPairUsize || ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessPairUsize ==> !with_iommu,
        ret is SuccessThreeUsize ==> with_iommu,
        ret is SuccessPairUsize || ret is SuccessThreeUsize ==> {
            let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let container_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
            let child_ptr = if with_iommu { ret->SuccessThreeUsize_value1 } else { ret->SuccessPairUsize_value1 };
            let thread_ptr = if with_iommu { ret->SuccessThreeUsize_value3 } else { ret->SuccessPairUsize_value2 };
            let descriptors = old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors;
            let endpoint = if endpoint_index is Some { descriptors.spec_index(endpoint_index->Some_0) } else { None };
            let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& range as int + 3 <= final(steps).nonlock_view().len() as int
            &&& final(steps).nonlock_view().len() as int <= 4 * range as int + 3
            &&& final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& source_range.wf()
            &&& endpoint_index is Some ==> descriptors.wf() && endpoint is Some
            &&& kernel_u_new_thread_changed(
                final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, child_ptr, current_thread_ptr, container_ptr,
                thread_ptr, *initial_regs, endpoint, None,
            )
            &&& with_iommu ==> final(krnl).prc_mp.dom().contains(child_ptr) && final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(ret->SuccessThreeUsize_value2)
            &&& with_iommu ==> final(krnl).it_mp.dom().contains(ret->SuccessThreeUsize_value2) && final(krnl).it_mp.spec_index(ret->SuccessThreeUsize_value2).view().is_empty()
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& endpoint_index is Some ==> final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& endpoint_index is Some ==> final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == endpoint
        },
        ret is SuccessPairUsize || ret is SuccessThreeUsize || ret is Error || ret is ErrorNoPcid || ret is ErrorProcessKilled
            || ret is ErrorThreadKilled || ret is ErrorNoQuota,
{
    proof { use_type_invariant(&*steps); }
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let base_quota: usize = if with_iommu { 6usize } else { 4usize };
    if range == 0
        || range > usize::MAX / 4096usize
        || range > (usize::MAX - base_quota) / 3usize
        || !va_4k_valid(va)
    {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::Error);
        }
        return RetValueType::Error;
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::Error);
        }
        return RetValueType::Error;
    }
    let source_range = VaRange4K::new(va, range);
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));

    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    proof {
        assert(krnl.prc_mp.dom().contains(parent_ptr) && krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr) by { reveal(process_cpu_wf); };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr
            &&& krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0
        }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr) by { reveal(container_process_wf); reveal(container_perms_wf); };
    }
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let pcid_allocator_ptr = container_rodata.borrow().pcid_allocator;
    let scheduler_ptr = container_rodata.borrow().scheduler;
    let allocator_ptr = container_rodata.borrow().allocator_ptr_4k;
    proof { assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().wf() && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr) by { reveal(container_pcid_allocator_wf); reveal(pcid_allocator_perms_wf); }; }
    let Tracked(pcid_allocator_lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));

    let pcid_allocator = krnl.pcid_allc_mp.borrow_typed(pcid_allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(&*lctx), Tracked(&pcid_allocator_lock_perm));
    let pcid = match pcid_allocator.find_lowest_free_nonzero() {
        Some(pcid) => pcid,
        None => {
            krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, Some(pcid_allocator_ptr));
                new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::ErrorNoPcid);
            }
            return RetValueType::ErrorNoPcid;
        },
    };
    let process_res = krnl.wlock_process_unless_killed(parent_ptr, Ghost(cpu_id), Tracked(&mut *lctx));

    if process_res.is_none() {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), None, None, None, Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::ErrorProcessKilled);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(parent_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));

    if thread_res.is_none() {
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), None, None, Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::ErrorThreadKilled);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(current_thread_lock_perm) = thread_res.unwrap();
    let thread_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    let endpoint_option = match endpoint_index { Some(index) => *thread_ref.endpoint_descriptors.get(index), None => None };
    let source_pagetable_ptr = thread_ref.proc_pagetable_ptr;
    let endpoint_missing = endpoint_index.is_some() && endpoint_option.is_none();
    if endpoint_missing || thread_ref.quota_4k < base_quota + 3 * range {
        let error = if endpoint_missing { RetValueType::Error } else { RetValueType::ErrorNoQuota };
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), None, None, Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, error);
        }
        return error;
    }
    let endpoint_ptr = match endpoint_option { Some(ptr) => ptr, None => 0 };
    let tracked mut endpoint_lock_perm_opt: Option<LockPerm> = None;
    if endpoint_index.is_some() {
        proof {
            assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index->Some_0))) by { reveal(thread_endpoint_ref_counter_wf); };
            assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, endpoint_ptr); };
            assert({
                ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
            }) by { reveal(container_thread_endpoint_wf); };
        }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
        proof { endpoint_lock_perm_opt = Some(endpoint_lock_perm); }
    }
    proof { assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)) by { reveal(process_thread_wf); reveal(process_pagetable_match); }; }
    let Tracked(source_pagetable_lock_perm) = krnl.wlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx));

    let source_start_indices = va2index(va);
    proof { assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); }; }
    let source_pt = krnl.pt_mp.borrow_typed(source_pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&source_pagetable_lock_perm));
    let source_ready = if source_start_indices.0 < source_pt.kernel_l4_end {
        false
    } else {
        share_mapping_4k_source_precheck(krnl, &source_range, source_pagetable_ptr, Tracked(&*lctx), Tracked(&source_pagetable_lock_perm))
    };
    if !source_ready {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        if endpoint_index.is_some() {
            let tracked endpoint_lock_perm = endpoint_lock_perm_opt.tracked_unwrap();
            krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        }
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), endpoint_option, Some(source_pagetable_ptr), Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::Error);
        }
        return RetValueType::Error;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    proof {
        assert({
            let pre = kernel_k_to_kernel_u(*old(krnl));
            &&& pre.cpu_array[cpu_id as int].current_process == Some(parent_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& pre.cpu_array[cpu_id as int].owning_container == container_ptr
            &&& pre.thread_map[current_thread_ptr].endpoint_descriptors == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()
        }) by { kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None); };
    }
    if with_iommu {
        let tracked endpoint_lock_perm = endpoint_lock_perm_opt.tracked_unwrap();
        let (child_ptr, iommu_table_ptr, thread_ptr) = commit_new_process_with_iommu_and_endpoint(
            krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr,
            allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint_ptr, endpoint_index.unwrap(), pcid, Tracked(cpu_lock_perm),
            Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(current_thread_lock_perm),
            Tracked(source_pagetable_lock_perm), Tracked(endpoint_lock_perm), initial_regs,
        );
        let ret = RetValueType::SuccessThreeUsize { value1: child_ptr, value2: iommu_table_ptr, value3: thread_ptr };
        proof { new_process_syscall_trace_from_commit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, ret); }
        ret
    } else {
        let (endpoint, index) = match endpoint_index { Some(index) => (Some(endpoint_ptr), index), None => (None, 0) };
        let (child_ptr, thread_ptr) = commit_new_process(
            krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr,
            allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint, index, pcid,
            Tracked(cpu_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(endpoint_lock_perm_opt), initial_regs,
        );
        let ret = RetValueType::SuccessPairUsize { value1: child_ptr, value2: thread_ptr };
        proof { new_process_syscall_trace_from_commit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, ret); }
        ret
    }
}
}

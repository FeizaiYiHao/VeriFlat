use vstd::prelude::*;
use crate::*;
use super::syscall_pci_attach_dma_eof::*;
use super::syscall_pci_spec::*;
use super::syscall_pci_trace::*;

verus! {
/// Attaches DMA translation of `(bus, device, function)`, a PCI function owned by the running process,
/// to that process's IOMMU table: the function's context entry in the root table now points at the
/// table's root. The trap layer validates the B/D/F.
pub fn syscall_pci_attach_dma(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, bus: usize, device: usize,
    function: usize,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        pci_bdf_valid(bus, device, function),
        old(krnl).inv(),
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
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        pci_attach_dma_syscall_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, bus, device, function, ret,
        ),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == pci_attach_dma_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
        ret is Success ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& pci_attach_dma_step_pre(step.old_u, cpu_id, bus, device, function)
            &&& pci_attach_dma_step(step.old_u, step.new_u, cpu_id, bus, device, function)
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            pci_attach_dma_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function, RetValueType::CpuIdle);
            pci_attach_dma_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::CpuIdle);
        }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        &&& cpu.current_process is Some
        &&& krnl.prc_mp.dom().contains(cpu.current_process.unwrap())
        &&& !krnl.prc_mp.spec_index(cpu.current_process.unwrap()).view().zombie
        &&& krnl.prc_mp.spec_index(cpu.current_process.unwrap()).view_rodata().view().owning_container == cpu.owning_container
    }) by { cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let process_ptr = cpu.current_process().unwrap();
    assert({
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
    }) by {
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
    };
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(lctx));
    if process_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), None, None, None, None);
            pci_attach_dma_trace_stutter(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function,
                RetValueType::ErrorProcessKilled,
            );
            pci_attach_dma_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::ErrorProcessKilled);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    proof { assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
    }; }
    let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(lctx));
    let owner = krnl.irt.borrow(Tracked(&irt_lock_perm)).owner(bus, device, function);
    let attached = krnl.irt.borrow(Tracked(&irt_lock_perm)).is_attached(bus, device, function);
    let iommu_cr3 = krnl.prc_mp.borrow_rodata(process_ptr).borrow().iommu_cr3;
    let result = if owner != process_ptr { RetValueType::ErrorPciOwnerMismatch }
        else if iommu_cr3.is_none() { RetValueType::ErrorPciNoIommuTable }
        else if attached { RetValueType::ErrorPciAlreadyAttached }
        else { RetValueType::Success };
    proof {
        assert(result == pci_attach_dma_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function)) by {
            reveal(process_pci_function_ownership_wf); process_iommu_table_match_process_at(old(krnl).prc_mp, old(krnl).it_mp, process_ptr);
            pci_attach_dma_result_from_k(&*old(krnl), cpu_id, bus, device, function, result);
        };
    }
    if owner != process_ptr || iommu_cr3.is_none() || attached {
        krnl.wunlock_iommu_root_table(Tracked(lctx), Tracked(irt_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            pci_attach_dma_trace_stutter(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function, result,
            );
        }
        return result;
    }
    let root = iommu_cr3.unwrap();
    proof {
        assert(old(krnl).prc_mp.spec_index(process_ptr).view_ghost().owned_pci_functions.view().contains((bus, device, function))) by { reveal(process_pci_function_ownership_wf); };
        assert(old(krnl).prc_mp.spec_index(process_ptr).view().iommu_table is Some && page_ptr_valid(root)) by {
            process_iommu_table_match_process_at(old(krnl).prc_mp, old(krnl).it_mp, process_ptr); iommu_table_perms_wf_at(old(krnl).it_mp, old(krnl).prc_mp.spec_index(process_ptr).view().iommu_table->Some_0);
            old(krnl).it_mp.spec_index(old(krnl).prc_mp.spec_index(process_ptr).view().iommu_table->Some_0).view().table_pages_wf_cr3_at();
        };
        let iommu_table = krnl.prc_mp.spec_index(process_ptr).view().iommu_table->Some_0;
        krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
        assert(!(krnl.it_mp.spec_index(iommu_table).locking_thread() is Write)) by {
            reveal(iommu_table_lock_wf); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr);
            if krnl.it_mp.spec_index(iommu_table).locking_thread() is Write {
                assert(lctx.iommu_table_lock_map().dom().contains(iommu_table)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        };
    }
    let ghost before_attach = *krnl;
    iommu_root_table_attach(&mut krnl.irt, bus, device, function, root, Tracked(&*lctx), Tracked(&irt_lock_perm));
    proof {
        pci_attach_dma_eof(before_attach, *krnl, process_ptr, bus, device, function, root);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&before_attach, &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&before_attach, &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    krnl.wunlock_iommu_root_table(Tracked(lctx), Tracked(irt_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let attach_before = steps.view();
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        steps.end_kernel_step_pci_attach(&*krnl, &*lctx, cpu_id, process_ptr, bus, device, function, root);

        assert({
            &&& pci_attach_dma_syscall_trace(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl),
                cpu_id, bus, device, function, RetValueType::Success,
            )
            &&& pci_attach_dma_step_pre(steps.nonlock_view().last().old_u, cpu_id, bus, device, function)
            &&& pci_attach_dma_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, bus, device, function)
        }) by {
            pci_attach_dma_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, bus, device, function);
            pci_attach_dma_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, process_ptr, bus, device, function);
            pci_attach_dma_trace_step(&*steps, attach_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, bus, device, function);
        };
    }
    RetValueType::Success
}
} // verus!

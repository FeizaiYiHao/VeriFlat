use vstd::prelude::*;
use crate::*;
use super::syscall_pci_spec::*;
use super::syscall_pci_trace::*;

verus! {
/// Claims the unowned PCI function `(bus, device, function)` for the running process, which must be the root process of
/// the root container: under its page table's write lock and then the root-table lock, the function takes a free entry of
/// the page table's PCI function array with no BAR mapping and the process becomes its owner. The trap layer validates the
/// B/D/F.
pub fn syscall_pci_claim(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, bus: usize, device: usize,
    function: usize,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        pci_bdf_valid(bus, device, function),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        pci_claim_syscall_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, bus, device, function, ret,
        ),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == pci_claim_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            pci_claim_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function, RetValueType::CpuIdle);
            pci_claim_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::CpuIdle);
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
    let prc_ptr = cpu.current_process().unwrap();
    assert({
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth
    }) by {
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
    };
    let process_res = krnl.wlock_process_unless_killed(prc_ptr, Ghost(cpu_id), Tracked(lctx));
    if process_res.is_none() {
        krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), None, None, None, None);
            pci_claim_trace_stutter(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function,
                RetValueType::ErrorProcessKilled,
            );
            pci_claim_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::ErrorProcessKilled);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    proof {
        assert(krnl.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() != 0) by {
            thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
        };
        process_perms_wf_at(krnl.prc_mp, prc_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr); container_perms_wf_at(krnl.ctn_mp, krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container);
    }
    let process_ro = krnl.prc_mp.borrow_rodata(prc_ptr).borrow();
    let pagetable_ptr = process_ro.pagetable;
    let root = process_ro.parent.is_none() && krnl.ctn_mp.borrow_rodata(process_ro.owning_container).borrow().parent.is_none();
    if !root {
        krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            pci_claim_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::ErrorPciNotRootProcess);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            pci_claim_trace_stutter(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function,
                RetValueType::ErrorPciNotRootProcess,
            );
        }
        return RetValueType::ErrorPciNotRootProcess;
    }
    let Tracked(pagetable_lock_perm) = krnl.wlock_pagetable(pagetable_ptr, Tracked(lctx));
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); }
    let free = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).higher.pci.free_entry();
    if free.is_none() {
        krnl.wunlock_pagetable(pagetable_ptr, Tracked(lctx), Tracked(pagetable_lock_perm));
        krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            pci_claim_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::ErrorPciFunctionArrayFull);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            pci_claim_trace_stutter(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function,
                RetValueType::ErrorPciFunctionArrayFull,
            );
        }
        return RetValueType::ErrorPciFunctionArrayFull;
    }
    let index = free.unwrap();
    let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(lctx));
    if krnl.irt.borrow(Tracked(&irt_lock_perm)).is_owned(bus, device, function) {
        krnl.wunlock_iommu_root_table(Tracked(lctx), Tracked(irt_lock_perm));
        krnl.wunlock_pagetable(pagetable_ptr, Tracked(lctx), Tracked(pagetable_lock_perm));
        krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            pci_claim_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::ErrorPciAlreadyOwned);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            pci_claim_trace_stutter(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, bus, device, function,
                RetValueType::ErrorPciAlreadyOwned,
            );
        }
        return RetValueType::ErrorPciAlreadyOwned;
    }
    proof { pci_claim_result_from_k(&*old(krnl), cpu_id, bus, device, function, RetValueType::Success); }
    let ghost locked = *krnl;
    krnl.update_pci_entry(pagetable_ptr, index, PciEntryUpdate::Claim { bus, device, function }, Tracked(&*lctx), Tracked(&pagetable_lock_perm), Tracked(&irt_lock_perm));
    let ghost claimed = *krnl;
    proof {
        assert({
            let before = whole_pagetable(locked.pt_mp, locked.pt_lower.view(), pagetable_ptr);
            let after = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            &&& after.lower == before.lower
            &&& after.mapping_4k() == before.mapping_4k()
            &&& after.mapping_2m() == before.mapping_2m()
            &&& after.mapping_1g() == before.mapping_1g()
        });
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&locked, &claimed)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    krnl.wunlock_iommu_root_table(Tracked(lctx), Tracked(irt_lock_perm));
    krnl.wunlock_pagetable(pagetable_ptr, Tracked(lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let claim_before = steps.view();
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &locked)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&claimed, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert({
            &&& kernel_cpu_nonlock_fields_unchanged(steps.snapshot_k().cpu_arr, krnl.cpu_arr)
            &&& kernel_process_nonlock_fields_unchanged(steps.snapshot_k().prc_mp, krnl.prc_mp)
            &&& kernel_thread_nonlock_fields_unchanged(steps.snapshot_k().thrd_mp, krnl.thrd_mp)
            &&& kernel_iommu_table_nonlock_fields_unchanged(steps.snapshot_k().it_mp, krnl.it_mp)
            &&& krnl.dflt_pt == steps.snapshot_k().dflt_pt
            &&& krnl.pci_bars == steps.snapshot_k().pci_bars
        }) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_pci_claim(&*krnl, &*lctx, cpu_id, prc_ptr, bus, device, function, index as int);
        assert({
            &&& pci_claim_syscall_trace(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl),
                cpu_id, bus, device, function, RetValueType::Success,
            )
        }) by {
            pci_claim_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, prc_ptr, bus, device, function);
            pci_claim_trace_step(&*steps, claim_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, bus, device, function);
        };
    }
    RetValueType::Success
}
} // verus!

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Every cpu slot of the user projection, without unfolding the other projected maps.
pub proof fn kernel_u_cpu_array_projection(krnl: &KernelK)
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        forall|c: CpuId| #![trigger kernel_k_to_kernel_u(*krnl).cpu_array[c as int]] index_valid(NUM_CPUS, c) ==> kernel_k_to_kernel_u(*krnl).cpu_array[c as int] == (CpuU {
            lock_state: krnl.cpu_arr.spec_index(c).value.lock_state_u(), owning_container: krnl.cpu_arr.spec_index(c).value.view().view().owning_container,
            state: krnl.cpu_arr.spec_index(c).value.view().view().state, current_process: krnl.cpu_arr.spec_index(c).value.view().view().current_process,
            current_thread: krnl.cpu_arr.spec_index(c).value.view().view().current_thread, killed: krnl.cpu_arr.spec_index(c).value.being_killed(),
            op: krnl.cpu_op.view().view()[c as int],
        }),
{ reveal(kernel_k_to_kernel_u); }

/// The stored U snapshot is the projection of every state that keeps the snapshot's non-lock fields and observable lock
/// modes.
pub proof fn kernel_snapshot_nonlock_fields_and_lock_states_unchanged_implies_u_eq(tracked steps: &KernelSteps, krnl: &KernelK)
    requires
        process_pagetable_wf(krnl.prc_mp, krnl.pt_mp),
        process_iommu_table_wf(krnl.prc_mp, krnl.it_mp),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
        kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
        krnl.irt.view().owners() == steps.snapshot_k().irt.view().owners(),
        krnl.irt.view().iommu_roots() == steps.snapshot_k().irt.view().iommu_roots(),
        krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
        krnl.cpu_op.view().view() == steps.snapshot_k().cpu_op.view().view(),
        krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
        forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
            krnl.ctn_mp.dom().contains(p) && steps.snapshot_k().ctn_mp.dom().contains(p) ==> {
                &&& krnl.ctn_mp.spec_index(p).lock_state_u() == steps.snapshot_k().ctn_mp.spec_index(p).lock_state_u()
                &&& krnl.ctn_mp.spec_index(p).lock_process_owner_u() == steps.snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u()
            },
        forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
            krnl.prc_mp.dom().contains(p) && steps.snapshot_k().prc_mp.dom().contains(p) ==> krnl.prc_mp.spec_index(p).lock_state_u() == steps.snapshot_k().prc_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
            krnl.pt_mp.dom().contains(p) && steps.snapshot_k().pt_mp.dom().contains(p) ==> {
                &&& krnl.pt_mp.spec_index(p).lock_state_u() == steps.snapshot_k().pt_mp.spec_index(p).lock_state_u()
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), p).lower.pagetable_window_locks == whole_pagetable(steps.snapshot_k().pt_mp, steps.snapshot_k().pt_lower.view(), p).lower.pagetable_window_locks
            },
        forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
            krnl.it_mp.dom().contains(p) && steps.snapshot_k().it_mp.dom().contains(p) ==> krnl.it_mp.spec_index(p).lock_state_u() == steps.snapshot_k().it_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockThreadPtr| #![trigger krnl.thrd_mp.spec_index(p)]
            krnl.thrd_mp.dom().contains(p) && steps.snapshot_k().thrd_mp.dom().contains(p) ==> krnl.thrd_mp.spec_index(p).lock_state_u() == steps.snapshot_k().thrd_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
            krnl.ep_mp.dom().contains(p) && steps.snapshot_k().ep_mp.dom().contains(p) ==> krnl.ep_mp.spec_index(p).lock_state_u() == steps.snapshot_k().ep_mp.spec_index(p).lock_state_u(),
        forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> krnl.cpu_arr.spec_index(i).value.lock_state_u() == steps.snapshot_k().cpu_arr.spec_index(i).value.lock_state_u(),
    ensures
        steps.snapshot_u() == kernel_k_to_kernel_u(*krnl),
{
    use_type_invariant(steps);
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), krnl);
}
}

use vstd::prelude::*;
use vstd::assert_seqs_equal;
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
        }),
{ reveal(kernel_k_to_kernel_u); }

/// Every B/D/F slot of the user projection's root table: its attached flag and its owner.
pub proof fn kernel_iommu_root_table_projection(krnl: &KernelK)
    ensures
        forall|b: usize, d: usize, f: usize|
            #![trigger kernel_k_to_kernel_u(*krnl).iommu_root_table.attached[b as int][d as int][f as int]]
            #![trigger krnl.irt.view().spec_index_iommu_root(b, d, f)]
            pci_bdf_valid(b, d, f) ==> {
                &&& kernel_k_to_kernel_u(*krnl).iommu_root_table.attached[b as int][d as int][f as int] == (krnl.irt.view().spec_index_iommu_root(b, d, f) is Some)
                &&& kernel_k_to_kernel_u(*krnl).iommu_root_table.owners[b as int][d as int][f as int] == krnl.irt.view().spec_index_owner(b, d, f)
            },
{ reveal(kernel_k_to_kernel_u); reveal(IommuRootTable::user_view); }

/// The stored U snapshot is the projection of every state that keeps the snapshot's non-lock fields and observable lock
/// modes.
pub proof fn kernel_snapshot_nonlock_fields_and_lock_states_unchanged_implies_u_eq(tracked steps: &KernelSteps, krnl: &KernelK)
    requires
        process_pagetable_match(krnl.prc_mp, krnl.pt_mp),
        process_iommu_table_match(krnl.prc_mp, krnl.it_mp),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
        kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
        krnl.irt.view().owners() == steps.snapshot_k().irt.view().owners(),
        krnl.irt.view().iommu_roots() == steps.snapshot_k().irt.view().iommu_roots(),
        krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
        krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
        forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
            krnl.ctn_mp.dom().contains(p) && steps.snapshot_k().ctn_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().ctn_mp.spec_index(p).locking_thread();
                let after = krnl.ctn_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
            krnl.prc_mp.dom().contains(p) && steps.snapshot_k().prc_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().prc_mp.spec_index(p).locking_thread();
                let after = krnl.prc_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
            krnl.pt_mp.dom().contains(p) && steps.snapshot_k().pt_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().pt_mp.spec_index(p).locking_thread();
                let after = krnl.pt_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
            krnl.it_mp.dom().contains(p) && steps.snapshot_k().it_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().it_mp.spec_index(p).locking_thread();
                let after = krnl.it_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockThreadPtr| #![trigger krnl.thr_mp.spec_index(p)]
            krnl.thr_mp.dom().contains(p) && steps.snapshot_k().thr_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().thr_mp.spec_index(p).locking_thread();
                let after = krnl.thr_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
            krnl.ep_mp.dom().contains(p) && steps.snapshot_k().ep_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().ep_mp.spec_index(p).locking_thread();
                let after = krnl.ep_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> {
                let before = steps.snapshot_k().cpu_arr.spec_index(i).value.locking_thread();
                let after = krnl.cpu_arr.spec_index(i).value.locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures
        steps.snapshot_u() == kernel_k_to_kernel_u(*krnl),
{
    use_type_invariant(steps);
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), krnl);
}

/// Detaching in the root table every PCI function owned by `process`, and emptying the IOTLB domain of each detached
/// function, clears exactly those functions' attached flags in the projected root table, keeps its owners, and empties
/// exactly their projected IOTLB domains.
pub proof fn kernel_iommu_root_table_process_detached_implies_u(pre: &KernelK, post: &KernelK, process: RwLockProcessPtr)
    requires
        post.irt.view().owners() == pre.irt.view().owners(),
        forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
            ==> post.irt.view().spec_index_iommu_root(b, d, f) == if pre.irt.view().spec_index_owner(b, d, f) == process { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) },
        post.iommu_tlb.view().dom() == pre.iommu_tlb.view().dom(),
        forall|b: usize, d: usize, f: usize| #![trigger post.iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
            ==> post.iommu_tlb.view()[pci_bdf_did(b, d, f)] == if pre.irt.view().spec_index_owner(b, d, f) == process && pre.irt.view().spec_index_iommu_root(b, d, f) is Some {
                SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
            } else { pre.iommu_tlb.view()[pci_bdf_did(b, d, f)] },
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre).iommu_root_table;
            kernel_k_to_kernel_u(*post).iommu_root_table == (IommuRootTableU {
                attached: Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
                    Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| a.attached[bus][device][function] && a.owners[bus][device][function] != process))),
                ..a
            })
        }),
        kernel_k_to_kernel_u(*post).iommu_tlb.dom() == kernel_k_to_kernel_u(*pre).iommu_tlb.dom(),
        forall|b: usize, d: usize, f: usize| #![trigger kernel_k_to_kernel_u(*post).iommu_tlb[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
            ==> kernel_k_to_kernel_u(*post).iommu_tlb[pci_bdf_did(b, d, f)] == if kernel_k_to_kernel_u(*pre).iommu_root_table.attached[b as int][d as int][f as int]
                && kernel_k_to_kernel_u(*pre).iommu_root_table.owners[b as int][d as int][f as int] == process {
                SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
            } else { kernel_k_to_kernel_u(*pre).iommu_tlb[pci_bdf_did(b, d, f)] },
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_iommu_root_table_projection(pre); kernel_iommu_root_table_projection(post);
    pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold();
    let a = kernel_k_to_kernel_u(*pre).iommu_root_table;
    let attached = kernel_k_to_kernel_u(*post).iommu_root_table.attached;
    let expected = Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| a.attached[bus][device][function] && a.owners[bus][device][function] != process)));
    assert_seqs_equal!(attached, expected, bus => {
        assert_seqs_equal!(attached[bus], expected[bus], device => {
            assert_seqs_equal!(attached[bus][device], expected[bus][device], function => {});
        });
    });
}
}

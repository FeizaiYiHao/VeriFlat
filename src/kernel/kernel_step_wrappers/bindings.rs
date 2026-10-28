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
        krnl.cpu_op.view().view() == steps.snapshot_k().cpu_op.view().view(),
        krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
        forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
            krnl.ctn_mp.dom().contains(p) && steps.snapshot_k().ctn_mp.dom().contains(p) ==> {
                let before = steps.snapshot_k().ctn_mp.spec_index(p).locking_thread();
                let after = krnl.ctn_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
                &&& krnl.ctn_mp.spec_index(p).lock_process_owner_u() == steps.snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u()
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

/// Clearing in the root table every context entry that the owner `process` of the IOMMU table `iommu_table` owns, owners
/// untouched, dropping the table's DID, and emptying the IOTLB domain `did` the table carried, if any, clears exactly those
/// functions' attached flags, empties only that projected IOTLB domain, and drops the DID of `process`'s projected IOMMU
/// table; nothing else in the complete projection changes.
pub proof fn kernel_iommu_root_table_process_detached_implies_u_step(pre: &KernelK, post: &KernelK, iommu_table: RwLockPageTableRoot, did: Option<VtdDomainId>)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        pre.it_mp.dom().contains(iommu_table),
        pre.it_mp.spec_index(iommu_table).view().did == did,
        *post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, it_mp: post.it_mp, ..*pre }),
        post.irt.view().owners() == pre.irt.view().owners(),
        forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> post.irt.view().spec_index_iommu_root(b, d, f)
            == if pre.irt.view().spec_index_owner(b, d, f) == pre.it_mp.spec_index(iommu_table).view().proc_ptr { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) },
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).view() == (PageTable { did: None, ..pre.it_mp.spec_index(iommu_table).view() }),
        did matches Some(d) ==> post.iommu_tlb.view() == pre.iommu_tlb.view().insert(d, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        did is None ==> post.iommu_tlb.view() == pre.iommu_tlb.view(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
            let p = a.process_map[process];
            &&& a.process_map.dom().contains(process)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(process, ProcessU { iommu_table: match p.iommu_table { Some(t) => Some(PageTableU { did: None, ..t }), None => None }, ..p }),
                iommu_root_table: IommuRootTableU {
                    attached: Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
                        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| a.iommu_root_table.attached[bus][device][function] && a.iommu_root_table.owners[bus][device][function] != process))),
                    ..a.iommu_root_table
                },
                iommu_tlb: match did { Some(d) => a.iommu_tlb.insert(d, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }), None => a.iommu_tlb },
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_iommu_table_match);
    kernel_iommu_root_table_projection(pre); kernel_iommu_root_table_projection(post);
    pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold();
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
    let p = a.process_map[process];
    kernel_process_projection_at(pre, process); kernel_process_projection_at(post, process);
    assert_maps_equal!(b.process_map, a.process_map.insert(process, ProcessU { iommu_table: match p.iommu_table { Some(t) => Some(PageTableU { did: None, ..t }), None => None }, ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    let attached = b.iommu_root_table.attached;
    let expected = Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| a.iommu_root_table.attached[bus][device][function] && a.iommu_root_table.owners[bus][device][function] != process)));
    assert_seqs_equal!(attached, expected, bus => {
        assert_seqs_equal!(attached[bus], expected[bus], device => {
            assert_seqs_equal!(attached[bus][device], expected[bus][device], function => {});
        });
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}
}

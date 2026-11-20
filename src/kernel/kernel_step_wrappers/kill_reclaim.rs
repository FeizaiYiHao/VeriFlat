use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Updating entry `index` of the PCI function array of page table `root`, whose process `p` is live, together with the
/// root-table owner of the updated function changes in the complete projection only `p`'s page-table PCI functions and that
/// function's owner: a `Claim` adds the function with no BAR mapping and makes `p` its owner, a `Release` drops it and leaves
/// it unowned.
pub proof fn kernel_pci_entry_updated_implies_u_step(pre: &KernelK, post: &KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        pre.pt_mp.dom().contains(root),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(root).view().higher.proc_ptr).view().zombie,
        *post == (KernelK { irt: post.irt, pt_mp: post.pt_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, root),
        post.pt_mp.spec_index(root).locking_thread() == pre.pt_mp.spec_index(root).locking_thread(),
        post.pt_mp.spec_index(root).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(root).view().higher.pci, ..pre.pt_mp.spec_index(root).view().higher }),
        post.pt_mp.spec_index(root).view().higher.pci.view() == pci_entry_update_view(pre.pt_mp.spec_index(root).view().higher.pci, index, update),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.irt.view().owners() == ({
            let bdf = pci_entry_update_bdf(pre.pt_mp.spec_index(root).view().higher.pci, index, update);
            seq3_update(pre.irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, if update is Claim { Some(pre.pt_mp.spec_index(root).view().higher.proc_ptr) } else { None })
        }),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let prc_ptr = pre.pt_mp.spec_index(root).view().higher.proc_ptr;
            let p = a.process_map[prc_ptr];
            let t = p.pagetable->Some_0;
            let bdf = pci_entry_update_bdf(pre.pt_mp.spec_index(root).view().higher.pci, index, update);
            let functions = if update is Claim { t.pci_functions.insert(bdf, 0) } else { t.pci_functions.remove(bdf) };
            let owner = if update is Claim { Some(prc_ptr) } else { None };
            &&& a.process_map.dom().contains(prc_ptr)
            &&& p.pagetable is Some
            &&& t.pci_functions == pre.pt_mp.spec_index(root).view().higher.pci.mapping_counts()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { pci_functions: functions, ..t }), ..p }),
                iommu_root_table: IommuRootTableU { owners: seq3_update(a.iommu_root_table.owners, bdf.0 as int, bdf.1 as int, bdf.2 as int, owner), ..a.iommu_root_table },
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    pre.irt.view().user_view_eq_owners_and_attached(); post.irt.view().user_view_eq_owners_and_attached();
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(root).view().higher.proc_ptr;
    let pci = pre.pt_mp.spec_index(root).view().higher.pci;
    let bdf = pci_entry_update_bdf(pci, index, update);
    let owner = if update is Claim { Some(prc_ptr) } else { None };
    process_pagetable_wf_pagetable_at(pre.prc_mp, pre.pt_mp, root);
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let functions = if update is Claim { t.pci_functions.insert(bdf, 0) } else { t.pci_functions.remove(bdf) };
    assert(post.pt_mp.spec_index(root).view().higher.pci.mapping_counts() =~= functions);
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { pci_functions: functions, ..t }), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Write-locking the page table `pagetable` of the live process `prc_ptr` on cpu `cpu_id` and changing only the progress of the
/// thread `thrd_ptr` changes in the complete projection only that page table's lock state and that thread's progress.
pub proof fn kernel_pagetable_write_locked_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        typed_lock_maps_aligned(post, lctx),
        lctx.cpu_id() == cpu_id,
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        *post == (KernelK { pt_mp: post.pt_mp, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> {
            &&& post.pt_mp.spec_index(p).view().higher == pre.pt_mp.spec_index(p).view().higher
            &&& p != pagetable ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
        },
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[prc_ptr];
            &&& a.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..process.pagetable->Some_0 }), ..process
                }),
                thread_map: a.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..a.thread_map[thrd_ptr] }),
                ..a
            })
        }),
{
    hide(Map::filter_keys);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_thread_progress_changed_implies_u_thread_map(pre, post, thrd_ptr);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let process = a.process_map[prc_ptr];
    kernel_process_projection_at(pre, prc_ptr); process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, prc_ptr);
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, ..process.pagetable->Some_0 }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, p);
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Releasing the PCI functions of the write-held page table `pagetable` of the live process `prc_ptr` on cpu `cpu_id`: a
/// process with the IOMMU table `iommu_table` write-locks it, every function of the array is detached as in `detached`, and
/// the table drops its DID, whose IOTLB domain alone is emptied; every function of the array becomes unowned and the array
/// empties. In the complete projection the process's page table loses its PCI functions, its IOMMU table is write-locked
/// without a DID, and the root table releases and detaches those functions.
pub proof fn kernel_pci_functions_released_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, detached: IommuRootTable,
)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_iommu_table_wf(pre.prc_mp, pre.it_mp),
        typed_lock_maps_aligned(post, lctx),
        lctx.cpu_id() == cpu_id,
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.prc_mp.spec_index(prc_ptr).view().iommu_table == iommu_table,
        *post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, it_mp: post.it_mp, pt_mp: post.pt_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(pagetable).view().higher.pci, ..pre.pt_mp.spec_index(pagetable).view().higher }),
        post.pt_mp.spec_index(pagetable).view().higher.pci.view() == Map::<PciBdf, Set<PciBarMapping>>::empty(),
        post.irt.view().owners() == if pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty() { pre.irt.view().owners() }
            else { pci_owners_released(pre.irt.view().owners(), pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom()) },
        iommu_table is None ==> post.irt.view().iommu_roots() == pre.irt.view().iommu_roots() && post.it_mp == pre.it_mp && post.iommu_tlb.view() == pre.iommu_tlb.view(),
        iommu_table matches Some(it) ==> {
            let table = pre.it_mp.spec_index(it);
            &&& table.locking_thread() is None
            &&& forall|b: usize, d: usize, f: usize| #![trigger detached.spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> detached.spec_index_iommu_root(b, d, f)
                == if pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains((b, d, f)) { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
            &&& post.irt.view().iommu_roots() == detached.iommu_roots()
            &&& post.it_mp.unchanged_except(&pre.it_mp, it)
            &&& typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), it, TypedLockMode::Write)
            &&& post.it_mp.spec_index(it).view() == (IommuTable { did: None, ..table.view() })
            &&& table.view().did matches Some(did) ==> post.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            &&& table.view().did is None ==> post.iommu_tlb.view() == pre.iommu_tlb.view()
        },
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let p = a.process_map[prc_ptr];
            let t = p.pagetable->Some_0;
            let functions = t.pci_functions.dom();
            let table = a.iommu_root_table;
            &&& a.process_map.dom().contains(prc_ptr)
            &&& p.pagetable is Some
            &&& functions == pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom()
            &&& (p.iommu_table is Some) == (iommu_table is Some)
            &&& p.iommu_table is Some ==> p.iommu_table->Some_0.lock_state is Unlocked
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { pci_functions: Map::empty(), ..t }),
                    iommu_table: match p.iommu_table { Some(i) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, did: None, ..i }), None => None },
                    ..p
                }),
                iommu_root_table: IommuRootTableU {
                    owners: if functions == Set::<PciBdf>::empty() { table.owners } else { pci_owners_released(table.owners, functions) },
                    attached: if p.iommu_table is Some {
                        Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int| Seq::new(PCI_FUNCTION_COUNT as nat,
                            |function: int| table.attached[bus][device][function] && !functions.contains((bus as usize, device as usize, function as usize)))))
                    } else { table.attached },
                },
                iommu_tlb: if p.iommu_table is Some && p.iommu_table->Some_0.did is Some {
                    a.iommu_tlb.insert(p.iommu_table->Some_0.did->Some_0, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
                } else { a.iommu_tlb },
                ..a
            })
            &&& iommu_table is Some || functions != Set::<PciBdf>::empty() ==> a != kernel_k_to_kernel_u(*post)
        }),
{
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, prc_ptr);
    if let Some(it) = iommu_table {
        process_iommu_table_wf_process_at(pre.prc_mp, pre.it_mp, prc_ptr);
        post.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), it);
    }
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let functions = t.pci_functions.dom();
    assert(post.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts() =~= Map::<PciBdf, nat>::empty());
    let new_p = ProcessU {
        pagetable: Some(PageTableU { pci_functions: Map::empty(), ..t }),
        iommu_table: match p.iommu_table { Some(i) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, did: None, ..i }), None => None },
        ..p
    };
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, new_p), q => {
        if pre.prc_mp.dom().contains(q) {
            kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, q);
            process_iommu_table_wf_process_at(pre.prc_mp, pre.it_mp, q);
        }
    });
    pre.irt.view().user_view_eq_owners_and_attached(); post.irt.view().user_view_eq_owners_and_attached();
    if iommu_table is Some {
        let attached = Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int| Seq::new(PCI_FUNCTION_COUNT as nat,
            |function: int| a.iommu_root_table.attached[bus][device][function] && !functions.contains((bus as usize, device as usize, function as usize)))));
        assert_seqs_equal!(b.iommu_root_table.attached, attached, bus => {
            assert_seqs_equal!(b.iommu_root_table.attached[bus], attached[bus], device => {
                assert_seqs_equal!(b.iommu_root_table.attached[bus][device], attached[bus][device], function => {
                    kernel_iommu_root_table_projection_at(pre, bus as usize, device as usize, function as usize);
                    kernel_iommu_root_table_projection_at(post, bus as usize, device as usize, function as usize);
                    assert(post.irt.view().spec_index_iommu_root(bus as usize, device as usize, function as usize) == detached.spec_index_iommu_root(bus as usize, device as usize, function as usize));
                });
            });
        });
    }
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(iommu_table is Some || functions != Set::<PciBdf>::empty() ==> a != b) by {
        if iommu_table is Some { assert(a.process_map[prc_ptr].iommu_table != b.process_map[prc_ptr].iommu_table); }
        else if functions != Set::<PciBdf>::empty() { assert(a.process_map[prc_ptr].pagetable->Some_0.pci_functions.dom() != b.process_map[prc_ptr].pagetable->Some_0.pci_functions.dom()); }
    };
}

/// Returning the whole `size` quota of the process `prc_ptr` to the `size` allocator of its container grows only that
/// container's `size` quota and clears only that process's `size` quota in the complete projection.
pub proof fn kernel_process_quota_returned_implies_u_step(pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, size: PageSize)
    requires
        pre.prc_mp.dom().contains(prc_ptr),
        pre.ctn_mp.dom().contains(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container),
        *post == (KernelK { prc_mp: post.prc_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != prc_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p),
        post.prc_mp.spec_index(prc_ptr).view() == match size {
            PageSize::SZ4k => Process { quota_4k: 0, ..pre.prc_mp.spec_index(prc_ptr).view() },
            PageSize::SZ2m => Process { quota_2m: 0, ..pre.prc_mp.spec_index(prc_ptr).view() },
            PageSize::SZ1g => Process { quota_1g: 0, ..pre.prc_mp.spec_index(prc_ptr).view() },
        },
        post.prc_mp.spec_index(prc_ptr).view_rodata() == pre.prc_mp.spec_index(prc_ptr).view_rodata(),
        post.prc_mp.spec_index(prc_ptr).view_ghost() == pre.prc_mp.spec_index(prc_ptr).view_ghost(),
        post.prc_mp.spec_index(prc_ptr).locking_thread() == pre.prc_mp.spec_index(prc_ptr).locking_thread(),
        post.prc_mp.spec_index(prc_ptr).being_killed() == pre.prc_mp.spec_index(prc_ptr).being_killed(),
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        ({
            let container = pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view();
            let process = pre.prc_mp.spec_index(prc_ptr).view();
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(a)]
                pre.allc_4k_mp.dom().contains(a) && a != container.allocator_ptr_4k ==> post.allc_4k_mp.spec_index(a).quota.view().view() == pre.allc_4k_mp.spec_index(a).quota.view().view()
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_2m_mp.spec_index(a)]
                pre.allc_2m_mp.dom().contains(a) && a != container.allocator_ptr_2m ==> post.allc_2m_mp.spec_index(a).quota.view().view() == pre.allc_2m_mp.spec_index(a).quota.view().view()
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_1g_mp.spec_index(a)]
                pre.allc_1g_mp.dom().contains(a) && a != container.allocator_ptr_1g ==> post.allc_1g_mp.spec_index(a).quota.view().view() == pre.allc_1g_mp.spec_index(a).quota.view().view()
            &&& post.allc_4k_mp.spec_index(container.allocator_ptr_4k).quota.view().view() as int
                == pre.allc_4k_mp.spec_index(container.allocator_ptr_4k).quota.view().view() as int + if size is SZ4k { process.quota_4k as int } else { 0 }
            &&& post.allc_2m_mp.spec_index(container.allocator_ptr_2m).quota.view().view() as int
                == pre.allc_2m_mp.spec_index(container.allocator_ptr_2m).quota.view().view() as int + if size is SZ2m { process.quota_2m as int } else { 0 }
            &&& post.allc_1g_mp.spec_index(container.allocator_ptr_1g).quota.view().view() as int
                == pre.allc_1g_mp.spec_index(container.allocator_ptr_1g).quota.view().view() as int + if size is SZ1g { process.quota_1g as int } else { 0 }
        }),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[prc_ptr];
            let container = a.container_map[process.owning_container];
            &&& a.process_map.dom().contains(prc_ptr)
            &&& process.owning_container == pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
            &&& a.container_map.dom().contains(process.owning_container)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(process.owning_container, match size {
                    PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k) as usize, ..container },
                    PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m) as usize, ..container },
                    PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g) as usize, ..container },
                }),
                process_map: a.process_map.insert(prc_ptr, match size {
                    PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                    PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                    PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_process_projection_at(pre, prc_ptr); kernel_container_projection_at(pre, pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container);
    kernel_process_quota_returned_implies_u_container_map(pre, post, prc_ptr, size);
    kernel_process_quota_returned_implies_u_process_map(pre, post, prc_ptr, size);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Making the live process `prc_ptr` a zombie, while its container's PCID allocator `allc_ptr` releases its PCID,
/// hides its tables in the process projection and adds the PCID to its container's free PCIDs.
pub proof fn kernel_process_zombified_implies_u_step(pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, allc_ptr: RwLockPcidAllocatorPtr)
    requires
        pre.prc_mp.dom().contains(prc_ptr),
        pre.ctn_mp.dom().contains(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container),
        container_pcid_allocator_wf(pre.ctn_mp, pre.pcid_allc_mp),
        pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().pcid_allocator == allc_ptr,
        pre.pcid_allc_mp.dom().contains(allc_ptr),
        pre.pcid_allc_mp.spec_index(allc_ptr).view().ref_counters.wf(),
        pcid_valid(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid != KERNEL_DEFAULT_PCID,
        *post == (KernelK { prc_mp: post.prc_mp, pcid_allc_mp: post.pcid_allc_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != prc_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p),
        post.prc_mp.spec_index(prc_ptr).view() == (Process { zombie: true, state: post.prc_mp.spec_index(prc_ptr).view().state, ..pre.prc_mp.spec_index(prc_ptr).view() }),
        post.prc_mp.spec_index(prc_ptr).view_rodata() == pre.prc_mp.spec_index(prc_ptr).view_rodata(),
        post.prc_mp.spec_index(prc_ptr).view_ghost() == pre.prc_mp.spec_index(prc_ptr).view_ghost(),
        post.prc_mp.spec_index(prc_ptr).locking_thread() == pre.prc_mp.spec_index(prc_ptr).locking_thread(),
        post.prc_mp.spec_index(prc_ptr).being_killed() == pre.prc_mp.spec_index(prc_ptr).being_killed(),
        post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, allc_ptr),
        post.pcid_allc_mp.spec_index(allc_ptr).view().release_ensures(&pre.pcid_allc_mp.spec_index(allc_ptr).view(), prc_ptr, pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid),
        post.pcid_allc_mp.spec_index(allc_ptr).lock_state_u() == pre.pcid_allc_mp.spec_index(allc_ptr).lock_state_u(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[prc_ptr];
            let container = a.container_map[process.owning_container];
            &&& a.process_map.dom().contains(prc_ptr)
            &&& process.owning_container == pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
            &&& a.container_map.dom().contains(process.owning_container)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(process.owning_container, ContainerU { free_pcids: container.free_pcids.insert(process.pcid), ..container }),
                process_map: a.process_map.insert(prc_ptr, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..process }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_process_projection_at(pre, prc_ptr); kernel_container_projection_at(pre, pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container);
    kernel_process_zombified_implies_u_container_map(pre, post, prc_ptr, allc_ptr);
    kernel_process_zombified_implies_u_process_map(pre, post, prc_ptr);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}
} // verus!

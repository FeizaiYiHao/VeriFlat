use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
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

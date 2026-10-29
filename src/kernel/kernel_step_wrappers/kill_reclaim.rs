use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
/// Handing every PCI function of the process `target` to the process `owner`, detached, dropping the DID of `target`'s IOMMU
/// table `iommu_table`, if any, and emptying the IOTLB domain `did` that table carried, if any, moves those functions in the
/// process projection, drops the DID of `target`'s projected IOMMU table, hands `target`'s root-table slots detached to
/// `owner`, and empties only that projected IOTLB domain; with any function moved, the projection changes.
pub proof fn kernel_process_functions_reassigned_implies_u_step(
    pre: &KernelK, post: &KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr, iommu_table: Option<RwLockPageTableRoot>, did: Option<VtdDomainId>,
)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        *post == (KernelK { prc_mp: post.prc_mp, irt: post.irt, iommu_tlb: post.iommu_tlb, it_mp: post.it_mp, ..*pre }),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.dom().contains(owner),
        target != owner,
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) ==> {
            let before = pre.prc_mp.spec_index(p);
            let after = post.prc_mp.spec_index(p);
            let pci = before.view_ghost().owned_pci_functions.view();
            &&& after.view() == before.view()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.being_killed() == before.being_killed()
            &&& after.view_ghost().uppertree_seq == before.view_ghost().uppertree_seq
            &&& after.view_ghost().subtree_set == before.view_ghost().subtree_set
            &&& after.view_ghost().owned_pci_functions.view() == if p == target { Set::empty() } else if p == owner { pci.union(pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view()) } else { pci }
        },
        forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& post.irt.view().spec_index_owner(b, d, f) == if pre.irt.view().spec_index_owner(b, d, f) == target { owner } else { pre.irt.view().spec_index_owner(b, d, f) }
            &&& post.irt.view().spec_index_iommu_root(b, d, f) == if pre.irt.view().spec_index_owner(b, d, f) == target { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
        },
        pre.prc_mp.spec_index(target).view().iommu_table == iommu_table,
        iommu_table is None ==> post.it_mp == pre.it_mp && did is None,
        iommu_table matches Some(t) ==> {
            &&& pre.it_mp.spec_index(t).view().did == did
            &&& post.it_mp.unchanged_except(&pre.it_mp, t)
            &&& post.it_mp.spec_index(t).locking_thread() == pre.it_mp.spec_index(t).locking_thread()
            &&& post.it_mp.spec_index(t).view() == (PageTable { did: None, ..pre.it_mp.spec_index(t).view() })
        },
        did matches Some(d) ==> post.iommu_tlb.view() == pre.iommu_tlb.view().insert(d, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        did is None ==> post.iommu_tlb.view() == pre.iommu_tlb.view(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let t = a.process_map[target];
            let o = a.process_map[owner];
            &&& a.process_map.dom().contains(target)
            &&& a.process_map.dom().contains(owner)
            &&& t.owned_pci_functions == pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(target, ProcessU {
                    owned_pci_functions: Set::empty(), iommu_table: match t.iommu_table { Some(x) => Some(PageTableU { did: None, ..x }), None => None }, ..t
                }).insert(owner, ProcessU { owned_pci_functions: o.owned_pci_functions.union(t.owned_pci_functions), ..o }),
                iommu_root_table: post.irt.view().user_view(),
                iommu_tlb: match did { Some(d) => a.iommu_tlb.insert(d, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }), None => a.iommu_tlb },
                ..a
            })
        }),
        forall|b: usize, d: usize, f: usize| #![trigger kernel_k_to_kernel_u(*post).iommu_root_table.attached[b as int][d as int][f as int]]
            #![trigger kernel_k_to_kernel_u(*post).iommu_root_table.owners[b as int][d as int][f as int]] pci_bdf_valid(b, d, f) ==> {
            let r = kernel_k_to_kernel_u(*pre).iommu_root_table;
            let s = kernel_k_to_kernel_u(*post).iommu_root_table;
            &&& s.attached[b as int][d as int][f as int] == (r.attached[b as int][d as int][f as int] && r.owners[b as int][d as int][f as int] != target)
            &&& s.owners[b as int][d as int][f as int] == if r.owners[b as int][d as int][f as int] == target { owner } else { r.owners[b as int][d as int][f as int] }
        },
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() != Set::<PciBdf>::empty() ==> {
            &&& kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post)
        },
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_iommu_table_match);
    kernel_iommu_root_table_projection(pre); kernel_iommu_root_table_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_process_projection_at(pre, target); kernel_process_projection_at(post, target);
    kernel_process_projection_at(pre, owner); kernel_process_projection_at(post, owner);
    let t = a.process_map[target];
    let o = a.process_map[owner];
    assert_maps_equal!(b.process_map, a.process_map.insert(target, ProcessU {
        owned_pci_functions: Set::empty(), iommu_table: match t.iommu_table { Some(x) => Some(PageTableU { did: None, ..x }), None => None }, ..t
    }).insert(owner, ProcessU { owned_pci_functions: o.owned_pci_functions.union(t.owned_pci_functions), ..o }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Returning the whole `size` quota of the process `process_ptr` to the `size` allocator of its container grows only that
/// container's `size` quota and clears only that process's `size` quota in the complete projection.
pub proof fn kernel_process_quota_returned_implies_u_step(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, size: PageSize)
    requires
        pre.prc_mp.dom().contains(process_ptr),
        pre.ctn_mp.dom().contains(pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container),
        *post == (KernelK { prc_mp: post.prc_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != process_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p),
        post.prc_mp.spec_index(process_ptr).view() == match size {
            PageSize::SZ4k => Process { quota_4k: 0, ..pre.prc_mp.spec_index(process_ptr).view() },
            PageSize::SZ2m => Process { quota_2m: 0, ..pre.prc_mp.spec_index(process_ptr).view() },
            PageSize::SZ1g => Process { quota_1g: 0, ..pre.prc_mp.spec_index(process_ptr).view() },
        },
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).locking_thread() == pre.prc_mp.spec_index(process_ptr).locking_thread(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        ({
            let container = pre.ctn_mp.spec_index(pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container).view_rodata().view();
            let process = pre.prc_mp.spec_index(process_ptr).view();
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
            let process = a.process_map[process_ptr];
            let container = a.container_map[process.owning_container];
            &&& a.process_map.dom().contains(process_ptr)
            &&& process.owning_container == pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container
            &&& a.container_map.dom().contains(process.owning_container)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(process.owning_container, match size {
                    PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k) as usize, ..container },
                    PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m) as usize, ..container },
                    PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g) as usize, ..container },
                }),
                process_map: a.process_map.insert(process_ptr, match size {
                    PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                    PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                    PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_process_projection_at(pre, process_ptr); kernel_container_projection_at(pre, pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container);
    kernel_process_quota_returned_implies_u_container_map(pre, post, process_ptr, size);
    kernel_process_quota_returned_implies_u_process_map(pre, post, process_ptr, size);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Making the live process `process_ptr` a zombie, while its container's PCID allocator `allocator_ptr` releases its PCID,
/// hides its tables in the process projection and adds the PCID to its container's free PCIDs.
pub proof fn kernel_process_zombified_implies_u_step(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        pre.prc_mp.dom().contains(process_ptr),
        pre.ctn_mp.dom().contains(pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container),
        container_pcid_allocator_wf(pre.ctn_mp, pre.pcid_allc_mp),
        pre.ctn_mp.spec_index(pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container).view_rodata().view().pcid_allocator == allocator_ptr,
        pre.pcid_allc_mp.dom().contains(allocator_ptr),
        pre.pcid_allc_mp.spec_index(allocator_ptr).view().ref_counters.wf(),
        pcid_valid(pre.prc_mp.spec_index(process_ptr).view_rodata().view().pcid),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pcid != KERNEL_DEFAULT_PCID,
        *post == (KernelK { prc_mp: post.prc_mp, pcid_allc_mp: post.pcid_allc_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != process_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p),
        post.prc_mp.spec_index(process_ptr).view() == (Process { zombie: true, state: post.prc_mp.spec_index(process_ptr).view().state, ..pre.prc_mp.spec_index(process_ptr).view() }),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).locking_thread() == pre.prc_mp.spec_index(process_ptr).locking_thread(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, allocator_ptr),
        post.pcid_allc_mp.spec_index(allocator_ptr).view().release_ensures(&pre.pcid_allc_mp.spec_index(allocator_ptr).view(), process_ptr, pre.prc_mp.spec_index(process_ptr).view_rodata().view().pcid),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[process_ptr];
            let container = a.container_map[process.owning_container];
            &&& a.process_map.dom().contains(process_ptr)
            &&& process.owning_container == pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container
            &&& a.container_map.dom().contains(process.owning_container)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(process.owning_container, ContainerU { free_pcids: container.free_pcids.insert(process.pcid), ..container }),
                process_map: a.process_map.insert(process_ptr, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..process }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_process_projection_at(pre, process_ptr); kernel_container_projection_at(pre, pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container);
    kernel_process_zombified_implies_u_container_map(pre, post, process_ptr, allocator_ptr);
    kernel_process_zombified_implies_u_process_map(pre, post, process_ptr);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}
} // verus!

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;

verus! {
/// Handing every PCI function of the process `target` to the process `owner` moves those functions in the process
/// projection and replaces the root table and the IOTLB, emptying the IOTLB domain of each function `target` owned; with
/// any function moved, both projections change.
pub proof fn kernel_process_functions_reassigned_implies_u_step(pre: &KernelK, post: &KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr)
    requires
        *post == (KernelK { prc_mp: post.prc_mp, irt: post.irt, iommu_tlb: post.iommu_tlb, ..*pre }),
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
        forall|b: usize, d: usize, f: usize| #![trigger post.iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
            ==> post.iommu_tlb.view()[pci_bdf_did(b, d, f)] == if pre.irt.view().spec_index_owner(b, d, f) == target { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { pre.iommu_tlb.view()[pci_bdf_did(b, d, f)] },
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let t = a.process_map[target];
            let o = a.process_map[owner];
            &&& a.process_map.dom().contains(target)
            &&& a.process_map.dom().contains(owner)
            &&& t.owned_pci_functions == pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view()
            &&& a.iommu_root_table == pre.irt.view().user_view()
            &&& a.iommu_tlb == pre.iommu_tlb.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(target, ProcessU { owned_pci_functions: Set::empty(), ..t }) .insert(owner, ProcessU { owned_pci_functions: o.owned_pci_functions.union(t.owned_pci_functions), ..o }),
                iommu_root_table: post.irt.view().user_view(),
                iommu_tlb: post.iommu_tlb.view(),
                ..a
            })
        }),
        forall|b: usize, d: usize, f: usize| #![trigger kernel_k_to_kernel_u(*post).iommu_tlb[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
            ==> kernel_k_to_kernel_u(*post).iommu_tlb[pci_bdf_did(b, d, f)] == if kernel_k_to_kernel_u(*pre).iommu_root_table.owners[b as int][d as int][f as int] == target { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } }
            else { kernel_k_to_kernel_u(*pre).iommu_tlb[pci_bdf_did(b, d, f)] },
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() != Set::<PciBdf>::empty() ==> {
            &&& kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post)
            &&& kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post)
        },
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_process_projection_at(pre, target); kernel_process_projection_at(post, target);
    kernel_process_projection_at(pre, owner); kernel_process_projection_at(post, owner);
    let t = a.process_map[target];
    let o = a.process_map[owner];
    assert_maps_equal!(b.process_map, a.process_map.insert(target, ProcessU { owned_pci_functions: Set::empty(), ..t }) .insert(owner, ProcessU { owned_pci_functions: o.owned_pci_functions.union(t.owned_pci_functions), ..o }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.container_map, a.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(b.thread_map, a.thread_map, x => {
        if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); }
    });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); }
    });
    reveal(kernel_k_to_kernel_u); pre.irt.view().user_view_unfold();
    if t.owned_pci_functions != Set::<PciBdf>::empty() { kernel_process_nonlock_projection_at(pre, target); kernel_process_nonlock_projection_at(post, target); }
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
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let container_ptr = pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container;
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    kernel_container_projection_at(pre, container_ptr); kernel_container_projection_at(post, container_ptr);
    let process = a.process_map[process_ptr];
    let container = a.container_map[container_ptr];
    assert_maps_equal!(b.container_map, a.container_map.insert(container_ptr, match size {
        PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k) as usize, ..container },
        PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m) as usize, ..container },
        PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g) as usize, ..container },
    }), c => {
        if pre.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c);
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr);
        }
    });
    assert_maps_equal!(b.process_map, a.process_map.insert(process_ptr, match size {
        PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
        PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
        PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.thread_map, a.thread_map, x => {
        if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); }
    });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); }
    });
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
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let container_ptr = pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container;
    kernel_process_projection_at(pre, process_ptr);
    kernel_container_projection_at(pre, container_ptr);
    let process = a.process_map[process_ptr];
    let container = a.container_map[container_ptr];
    assert_maps_equal!(b.container_map, a.container_map.insert(container_ptr, ContainerU { free_pcids: container.free_pcids.insert(process.pcid), ..container }), c => {
        if pre.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c);
            if c == container_ptr {
                assert_sets_equal!(PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(allocator_ptr).view().ref_counters.view()), PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(allocator_ptr).view().ref_counters.view()).insert(process.pcid));
            } else {
                let a = pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator;
                assert(pre.pcid_allc_mp.dom().contains(a) && a != allocator_ptr) by { reveal(container_pcid_allocator_wf); };
            }
        }
    });
    assert_maps_equal!(b.process_map, a.process_map.insert(process_ptr, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.thread_map, a.thread_map, x => {
        if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); }
    });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); }
    });
}
} // verus!

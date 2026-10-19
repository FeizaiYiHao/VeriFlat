use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;

verus! {
/// An unchanged cpu array projects to an unchanged cpu array.
pub proof fn kernel_cpu_array_unchanged_implies_u_cpu_array(pre: &KernelK, post: &KernelK)
    requires post.cpu_arr == pre.cpu_arr,
    ensures kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert_seqs_equal!(kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array, i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
}

/// Unchanged containers, cpu sets, offline flags, schedulers, PCID allocators, and page allocators project to an unchanged
/// container map.
pub proof fn kernel_container_maps_unchanged_implies_u_container_map(pre: &KernelK, post: &KernelK)
    requires
        post.ctn_mp == pre.ctn_mp,
        post.cpu_set_mp == pre.cpu_set_mp,
        post.cpu_offline_mp == pre.cpu_offline_mp,
        post.sched_mp == pre.sched_mp,
        post.pcid_allc_mp == pre.pcid_allc_mp,
        post.allc_4k_mp == pre.allc_4k_mp,
        post.allc_2m_mp == pre.allc_2m_mp,
        post.allc_1g_mp == pre.allc_1g_mp,
    ensures kernel_k_to_kernel_u(*post).container_map == kernel_k_to_kernel_u(*pre).container_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).container_map, kernel_k_to_kernel_u(*pre).container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); }
    });
}

/// Unchanged processes and tables project to an unchanged process map.
pub proof fn kernel_process_maps_unchanged_implies_u_process_map(pre: &KernelK, post: &KernelK)
    requires
        post.prc_mp == pre.prc_mp,
        post.pt_mp == pre.pt_mp,
        post.it_mp == pre.it_mp,
    ensures kernel_k_to_kernel_u(*post).process_map == kernel_k_to_kernel_u(*pre).process_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).process_map, kernel_k_to_kernel_u(*pre).process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

/// An unchanged thread map projects to an unchanged thread map.
pub proof fn kernel_thread_map_unchanged_implies_u_thread_map(pre: &KernelK, post: &KernelK)
    requires post.thr_mp == pre.thr_mp,
    ensures kernel_k_to_kernel_u(*post).thread_map == kernel_k_to_kernel_u(*pre).thread_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).thread_map, kernel_k_to_kernel_u(*pre).thread_map, t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); kernel_thread_projection_at(post, t); }
    });
}

/// An unchanged endpoint map projects to an unchanged endpoint map.
pub proof fn kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre: &KernelK, post: &KernelK)
    requires post.ep_mp == pre.ep_mp,
    ensures kernel_k_to_kernel_u(*post).endpoint_map == kernel_k_to_kernel_u(*pre).endpoint_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).endpoint_map, kernel_k_to_kernel_u(*pre).endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); }
    });
}

/// Retiring the zombie process `process_ptr` drops it from the processes of its container `container_ptr` and sets that
/// container's 4K quota to the new quota of its 4K allocator `allocator_ptr` in the container projection.
pub proof fn kernel_zombie_process_retired_implies_u_container_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        *post == (KernelK { prc_mp: post.prc_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != container_ptr ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_processes: Ghost(pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(process_ptr)), ..pre.ctn_mp.spec_index(container_ptr).view_ghost() }),
        post.ctn_mp.spec_index(container_ptr).locking_thread() == pre.ctn_mp.spec_index(container_ptr).locking_thread(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(a)]
            pre.allc_4k_mp.dom().contains(a) && a != allocator_ptr ==> post.allc_4k_mp.spec_index(a).quota.view() == pre.allc_4k_mp.spec_index(a).quota.view(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let container = a.container_map[container_ptr];
            kernel_k_to_kernel_u(*post).container_map == a.container_map.insert(container_ptr, ContainerU {
                owned_processes: container.owned_processes.remove(process_ptr), quota_4k: post.allc_4k_mp.spec_index(allocator_ptr).quota.view().view(), ..container })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let quota = post.allc_4k_mp.spec_index(allocator_ptr).quota.view().view();
    kernel_container_projection_at(pre, container_ptr); kernel_container_projection_at(post, container_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr);
    let container = a.container_map[container_ptr];
    assert_maps_equal!(b.container_map, a.container_map.insert(container_ptr, ContainerU { owned_processes: container.owned_processes.remove(process_ptr), quota_4k: quota, ..container }), c => {
        if pre.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c);
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c);
        }
    });
}

/// Retiring the zombie process `process_ptr`, whose parent is `parent_ptr`, drops it from the process projection, from its
/// parent's children, and from its ancestors' subtrees; every remaining process keeps its tables.
pub proof fn kernel_zombie_process_retired_implies_u_process_map(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, parent_ptr: RwLockProcessPtr)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(process_ptr).view_ghost().uppertree_seq.view().contains(parent_ptr),
        *post == (KernelK { prc_mp: post.prc_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom().remove(process_ptr),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] post.prc_mp.dom().contains(p) ==> {
            let old_p = pre.prc_mp.spec_index(p);
            let new_p = post.prc_mp.spec_index(p);
            &&& new_p.view() == if p == parent_ptr { Process { children: new_p.view().children, ..old_p.view() } } else { old_p.view() }
            &&& new_p.view_ghost() == if pre.prc_mp.spec_index(process_ptr).view_ghost().uppertree_seq.view().contains(p) {
                ProcessGhost { subtree_set: Ghost(old_p.view_ghost().subtree_set.view().remove(process_ptr)), ..old_p.view_ghost() }
            } else { old_p.view_ghost() }
            &&& new_p.view_rodata() == old_p.view_rodata()
            &&& new_p.locking_thread() == old_p.locking_thread()
            &&& new_p.being_killed() == old_p.being_killed()
        },
        post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(process_ptr),
        post.pt_mp.dom() == pre.pt_mp.dom().remove(pre.prc_mp.spec_index(process_ptr).view().pagetable),
        forall|t: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(t)] post.pt_mp.dom().contains(t) ==> post.pt_mp.spec_index(t) == pre.pt_mp.spec_index(t),
        post.it_mp.dom() == match pre.prc_mp.spec_index(process_ptr).view().iommu_table { Some(it) => pre.it_mp.dom().remove(it), None => pre.it_mp.dom() },
        forall|t: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(t)] post.it_mp.dom().contains(t) ==> post.it_mp.spec_index(t) == pre.it_mp.spec_index(t),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[process_ptr];
            kernel_k_to_kernel_u(*post).process_map == Map::new(a.process_map.dom().remove(process_ptr), |p: RwLockProcessPtr| {
                let q = a.process_map[p];
                if process.uppertree_seq.contains(p) {
                    ProcessU { children: if p == parent_ptr { q.children.remove_value(process_ptr) } else { q.children }, subtree_set: q.subtree_set.remove(process_ptr), ..q }
                } else { q }
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_process_projection_at(pre, process_ptr);
    let process = a.process_map[process_ptr];
    let retired = Map::new(a.process_map.dom().remove(process_ptr), |p: RwLockProcessPtr| {
        let q = a.process_map[p];
        if process.uppertree_seq.contains(p) {
            ProcessU { children: if p == parent_ptr { q.children.remove_value(process_ptr) } else { q.children }, subtree_set: q.subtree_set.remove(process_ptr), ..q }
        } else { q }
    });
    assert_maps_equal!(b.process_map, retired, p => {
        if post.prc_mp.dom().contains(p) {
            kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p);
            let old_p = pre.prc_mp.spec_index(p).view();
            if !old_p.zombie {
                process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, p); process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, process_ptr);
                if old_p.iommu_table is Some {
                    process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, p); process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, process_ptr);
                }
            }
        }
    });
}

/// Returning the whole `size` quota of the process `process_ptr` to the `size` allocator of its container grows only that
/// container's `size` quota in the container projection.
pub proof fn kernel_process_quota_returned_implies_u_container_map(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, size: PageSize)
    requires
        pre.prc_mp.dom().contains(process_ptr),
        pre.ctn_mp.dom().contains(pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container),
        *post == (KernelK { prc_mp: post.prc_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre }),
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
            kernel_k_to_kernel_u(*post).container_map == a.container_map.insert(process.owning_container, match size {
                PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k) as usize, ..container },
                PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m) as usize, ..container },
                PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g) as usize, ..container },
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let container_ptr = pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container;
    kernel_process_projection_at(pre, process_ptr);
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
}

/// Returning the whole `size` quota of the process `process_ptr` clears only that process's `size` quota in the process
/// projection.
pub proof fn kernel_process_quota_returned_implies_u_process_map(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, size: PageSize)
    requires
        pre.prc_mp.dom().contains(process_ptr),
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
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[process_ptr];
            kernel_k_to_kernel_u(*post).process_map == a.process_map.insert(process_ptr, match size {
                PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    let process = a.process_map[process_ptr];
    assert_maps_equal!(b.process_map, a.process_map.insert(process_ptr, match size {
        PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
        PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
        PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

/// The PCID allocator `allocator_ptr` releasing the PCID of the process `process_ptr` adds that PCID to its container's
/// free PCIDs in the container projection.
pub proof fn kernel_process_zombified_implies_u_container_map(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, allocator_ptr: RwLockPcidAllocatorPtr)
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
        post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, allocator_ptr),
        post.pcid_allc_mp.spec_index(allocator_ptr).view().release_ensures(&pre.pcid_allc_mp.spec_index(allocator_ptr).view(), process_ptr, pre.prc_mp.spec_index(process_ptr).view_rodata().view().pcid),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[process_ptr];
            let container = a.container_map[process.owning_container];
            kernel_k_to_kernel_u(*post).container_map == a.container_map.insert(process.owning_container, ContainerU { free_pcids: container.free_pcids.insert(process.pcid), ..container })
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
}

/// Making the live process `process_ptr` a zombie hides its tables in the process projection.
pub proof fn kernel_process_zombified_implies_u_process_map(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr)
    requires
        pre.prc_mp.dom().contains(process_ptr),
        *post == (KernelK { prc_mp: post.prc_mp, pcid_allc_mp: post.pcid_allc_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != process_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p),
        post.prc_mp.spec_index(process_ptr).view() == (Process { zombie: true, state: post.prc_mp.spec_index(process_ptr).view().state, ..pre.prc_mp.spec_index(process_ptr).view() }),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).locking_thread() == pre.prc_mp.spec_index(process_ptr).locking_thread(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post).process_map == a.process_map.insert(process_ptr, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..a.process_map[process_ptr] })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_process_projection_at(pre, process_ptr);
    let process = a.process_map[process_ptr];
    assert_maps_equal!(b.process_map, a.process_map.insert(process_ptr, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}
} // verus!

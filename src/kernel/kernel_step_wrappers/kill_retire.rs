use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Retiring the zombie process `process_ptr`, whose parent is `parent_ptr`, drops it from the process projection, from
/// its parent's children, and from its ancestors' subtrees, drops it from the processes of its container `container_ptr`,
/// and sets that container's 4K quota to the new quota of its 4K allocator `allocator_ptr`. Its tables leave their maps
/// and the pages it frees are not projected; every remaining process keeps its tables.
pub proof fn kernel_zombie_process_retired_implies_u_step(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(process_ptr).view_ghost().uppertree_seq.view().contains(parent_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
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
        post.pt_mp.dom() == pre.pt_mp.dom().remove(pre.prc_mp.spec_index(process_ptr).view().pagetable),
        forall|t: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(t)] post.pt_mp.dom().contains(t) ==> post.pt_mp.spec_index(t) == pre.pt_mp.spec_index(t),
        post.it_mp.dom() == match pre.prc_mp.spec_index(process_ptr).view().iommu_table { Some(it) => pre.it_mp.dom().remove(it), None => pre.it_mp.dom() },
        forall|t: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(t)] post.it_mp.dom().contains(t) ==> post.it_mp.spec_index(t) == pre.it_mp.spec_index(t),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process = a.process_map[process_ptr];
            let container = a.container_map[container_ptr];
            &&& a.process_map.dom().contains(process_ptr)
            &&& process.owning_container == container_ptr
            &&& a.container_map.dom().contains(container_ptr)
            &&& container.quota_4k == pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(container_ptr, ContainerU {
                    owned_processes: container.owned_processes.remove(process_ptr), quota_4k: post.allc_4k_mp.spec_index(allocator_ptr).quota.view().view(), ..container }),
                process_map: Map::new(a.process_map.dom().remove(process_ptr), |p: RwLockProcessPtr| {
                    let q = a.process_map[p];
                    if process.uppertree_seq.contains(p) {
                        ProcessU { children: if p == parent_ptr { q.children.remove_value(process_ptr) } else { q.children }, subtree_set: q.subtree_set.remove(process_ptr), ..q }
                    } else { q }
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let quota = post.allc_4k_mp.spec_index(allocator_ptr).quota.view().view();
    kernel_process_projection_at(pre, process_ptr);
    kernel_container_projection_at(pre, container_ptr); kernel_container_projection_at(post, container_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr);
    let process = a.process_map[process_ptr];
    let container = a.container_map[container_ptr];
    assert_maps_equal!(b.container_map, a.container_map.insert(container_ptr, ContainerU { owned_processes: container.owned_processes.remove(process_ptr), quota_4k: quota, ..container }), c => {
        if pre.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c);
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c);
        }
    });
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
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.thread_map, a.thread_map, x => { if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); } });
    reveal(kernel_k_to_kernel_u);
}
} // verus!

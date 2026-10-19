use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Retiring the container `container_ptr` with parent `parent_ptr` drops it with its scheduler, cpu set, offline
/// request table, PCID allocator, and allocators from the projection, drops it from its parent's children and from the
/// subtree of every container in its upper tree, gives its pages to `owner_ptr`, and raises the 4K and 2M quota of
/// `owner_ptr`'s allocators. Pages are not projected; every process, thread, cpu, and endpoint keeps its state.
pub proof fn kernel_container_retired_implies_u_step(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr)
    requires
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        container_scheduler_wf(pre.ctn_mp, pre.sched_mp),
        container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp),
        container_cpu_offline_flags_wf(pre.ctn_mp, pre.cpu_offline_mp),
        container_pcid_allocator_wf(pre.ctn_mp, pre.pcid_allc_mp),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.dom().contains(owner_ptr),
        owner_ptr != container_ptr,
        *post == (KernelK { ctn_mp: post.ctn_mp, sched_mp: post.sched_mp, cpu_set_mp: post.cpu_set_mp, pcid_allc_mp: post.pcid_allc_mp, cpu_offline_mp: post.cpu_offline_mp,
            allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, pg_arr: post.pg_arr, ..*pre }),
        post.ctn_mp.dom() == pre.ctn_mp.dom().remove(container_ptr),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] post.ctn_mp.dom().contains(c) ==> {
            let old_c = pre.ctn_mp.spec_index(c);
            let new_c = post.ctn_mp.spec_index(c);
            let target = pre.ctn_mp.spec_index(container_ptr);
            &&& new_c.view_rodata() == old_c.view_rodata()
            &&& new_c.locking_thread() == old_c.locking_thread()
            &&& new_c.being_killed() == old_c.being_killed()
            &&& new_c.view().zombie == old_c.view().zombie
            &&& new_c.view().root_process == old_c.view().root_process
            &&& new_c.view().children.view() == if c == parent_ptr { old_c.view().children.view().remove_value(container_ptr) } else { old_c.view().children.view() }
            &&& new_c.view().owned_pages.view() == if c == owner_ptr { old_c.view().owned_pages.view().union(target.view().owned_pages.view()) } else { old_c.view().owned_pages.view() }
            &&& new_c.view_ghost().uppertree_seq == old_c.view_ghost().uppertree_seq
            &&& new_c.view_ghost().subtree_set.view() == if target.view_ghost().uppertree_seq.view().contains(c) {
                old_c.view_ghost().subtree_set.view().remove(container_ptr)
            } else { old_c.view_ghost().subtree_set.view() }
            &&& new_c.view_ghost().owned_processes == old_c.view_ghost().owned_processes
            &&& new_c.view_ghost().owned_threads == old_c.view_ghost().owned_threads
            &&& new_c.view_ghost().owned_endpoints == old_c.view_ghost().owned_endpoints
        },
        post.sched_mp.dom() == pre.sched_mp.dom().remove(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler),
        forall|s: RwLockSchedulerPtr| #![trigger post.sched_mp.spec_index(s)] post.sched_mp.dom().contains(s) ==> post.sched_mp.spec_index(s) == pre.sched_mp.spec_index(s),
        post.cpu_set_mp.dom() == pre.cpu_set_mp.dom().remove(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set),
        forall|s: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(s)] post.cpu_set_mp.dom().contains(s) ==> post.cpu_set_mp.spec_index(s) == pre.cpu_set_mp.spec_index(s),
        post.cpu_offline_mp.dom() == pre.cpu_offline_mp.dom().remove(cpu_offline_flags_ptr(container_ptr)),
        forall|f: RwLockCpuOfflineFlagsPtr| #![trigger post.cpu_offline_mp.spec_index(f)] post.cpu_offline_mp.dom().contains(f) ==> post.cpu_offline_mp.spec_index(f) == pre.cpu_offline_mp.spec_index(f),
        post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom().remove(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
        forall|a: RwLockPcidAllocatorPtr| #![trigger post.pcid_allc_mp.spec_index(a)] post.pcid_allc_mp.dom().contains(a) ==> post.pcid_allc_mp.spec_index(a) == pre.pcid_allc_mp.spec_index(a),
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom().remove(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(a)]
            post.allc_4k_mp.dom().contains(a) && a != pre.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_4k ==> post.allc_4k_mp.spec_index(a).quota.view() == pre.allc_4k_mp.spec_index(a).quota.view(),
        pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
            < post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view(),
        post.allc_2m_mp.dom() == pre.allc_2m_mp.dom().remove(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_2m_mp.spec_index(a)]
            post.allc_2m_mp.dom().contains(a) && a != pre.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_2m ==> post.allc_2m_mp.spec_index(a).quota.view() == pre.allc_2m_mp.spec_index(a).quota.view(),
        pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
            < post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view(),
        post.allc_1g_mp.dom() == pre.allc_1g_mp.dom().remove(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_1g_mp.spec_index(a)] post.allc_1g_mp.dom().contains(a) ==> post.allc_1g_mp.spec_index(a).quota.view() == pre.allc_1g_mp.spec_index(a).quota.view(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let target = a.container_map[container_ptr];
            let owner_ro = pre.ctn_mp.spec_index(owner_ptr).view_rodata().view();
            let quota_4k = post.allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k).quota.view().view();
            let quota_2m = post.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).quota.view().view();
            &&& a.container_map.dom().contains(container_ptr)
            &&& a.container_map.dom().contains(owner_ptr)
            &&& a.container_map[owner_ptr].quota_4k < quota_4k
            &&& a.container_map[owner_ptr].quota_2m < quota_2m
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: Map::new(a.container_map.dom().remove(container_ptr), |c: RwLockContainerPtr| {
                    let container = a.container_map[c];
                    ContainerU {
                        children: if c == parent_ptr { container.children.remove_value(container_ptr) } else { container.children },
                        subtree_set: if target.uppertree_seq.contains(c) { container.subtree_set.remove(container_ptr) } else { container.subtree_set },
                        owned_pages: if c == owner_ptr { container.owned_pages.union(target.owned_pages) } else { container.owned_pages },
                        quota_4k: if c == owner_ptr { quota_4k } else { container.quota_4k },
                        quota_2m: if c == owner_ptr { quota_2m } else { container.quota_2m },
                        ..container
                    }
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let target = a.container_map[container_ptr];
    let owner_ro = pre.ctn_mp.spec_index(owner_ptr).view_rodata().view();
    let quota_4k = post.allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k).quota.view().view();
    let quota_2m = post.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).quota.view().view();
    kernel_container_projection_at(pre, container_ptr); kernel_container_projection_at(pre, owner_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr); container_scheduler_wf_at(pre.ctn_mp, pre.sched_mp, container_ptr);
    container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, container_ptr); container_cpu_offline_flags_wf_container_at(pre.ctn_mp, pre.cpu_offline_mp, container_ptr);
    container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, container_ptr); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, owner_ptr);
    assert_maps_equal!(b.container_map, Map::new(a.container_map.dom().remove(container_ptr), |c: RwLockContainerPtr| {
        let container = a.container_map[c];
        ContainerU {
            children: if c == parent_ptr { container.children.remove_value(container_ptr) } else { container.children },
            subtree_set: if target.uppertree_seq.contains(c) { container.subtree_set.remove(container_ptr) } else { container.subtree_set },
            owned_pages: if c == owner_ptr { container.owned_pages.union(target.owned_pages) } else { container.owned_pages },
            quota_4k: if c == owner_ptr { quota_4k } else { container.quota_4k },
            quota_2m: if c == owner_ptr { quota_2m } else { container.quota_2m },
            ..container
        }
    }), c => {
        if post.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c);
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c); container_scheduler_wf_at(pre.ctn_mp, pre.sched_mp, c);
            container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, c); container_cpu_offline_flags_wf_container_at(pre.ctn_mp, pre.cpu_offline_mp, c);
            container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, c);
        }
    });
    assert_maps_equal!(b.process_map, a.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); } });
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.thread_map, a.thread_map, x => { if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); } });
    reveal(kernel_k_to_kernel_u);
}
}

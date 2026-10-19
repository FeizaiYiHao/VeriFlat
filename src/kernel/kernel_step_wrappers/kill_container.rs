use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Freeing a page of the container `owner`, `origin` or one of its ancestors, to the 4K allocator `allocator_ptr` of
/// `owner` while crediting that allocator's quota by one grows only the 4K quota of `owner` in the complete projection,
/// so both projections change: the hidden leaf or table page that leaves `table` and the freed page are not projected.
pub proof fn kernel_page_freed_to_owner_quota_implies_u_step(
    pre: &KernelK, post: &KernelK, iommu: bool, table: RwLockPageTableRoot, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, origin: RwLockContainerPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        *post == (KernelK { pt_mp: post.pt_mp, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        !iommu ==> post.it_mp == pre.it_mp && post.pt_mp.unchanged_except(&pre.pt_mp, table) && post.pt_mp.spec_index(table).locking_thread() == pre.pt_mp.spec_index(table).locking_thread(),
        iommu ==> post.pt_mp == pre.pt_mp && post.it_mp.unchanged_except(&pre.it_mp, table) && post.it_mp.spec_index(table).locking_thread() == pre.it_mp.spec_index(table).locking_thread(),
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.dom().contains(origin),
        owner == origin || pre.ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(a)]
            pre.allc_4k_mp.dom().contains(a) && a != allocator_ptr ==> post.allc_4k_mp.spec_index(a).quota.view().view() == pre.allc_4k_mp.spec_index(a).quota.view().view(),
        post.allc_4k_mp.spec_index(allocator_ptr).quota.view().view() == pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().view() + 1,
    ensures
        kernel_u_container_quota_4k_increased(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), origin),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    let mid = KernelK { allc_4k_mp: pre.allc_4k_mp, ..*post };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, mid.ep_mp);
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(pre, &mid)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, &mid);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, owner);
    assert(kernel_container_quota_4k_changed(&mid, post, owner, 1)) by { reveal(kernel_container_quota_4k_changed); reveal(kernel_thread_nonlock_fields_unchanged); reveal(container_allocator_wf); };
    kernel_container_quota_4k_changed_implies_u_step(&mid, post, owner, 1);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_u_domains_projection(pre); kernel_container_projection_at(pre, origin);
    let changed = a.container_map.dom().filter(|c: RwLockContainerPtr| a.container_map[c] != b.container_map[c]);
    assert(b.container_map[owner] != a.container_map[owner]);
    assert(changed =~= set![owner]);
    assert(changed.len() == 1);
    assert(b.container_map.dom() == a.container_map.dom());
    assert(b == (KernelU { container_map: b.container_map, ..a }));
    assert(b.container_map[owner] == (ContainerU { quota_4k: b.container_map[owner].quota_4k, ..a.container_map[owner] }));
    assert(b.container_map[owner].quota_4k > a.container_map[owner].quota_4k);
    assert(owner == origin || a.container_map[origin].uppertree_seq.contains(owner));
    assert(kernel_u_container_quota_4k_increased(a, b, origin)) by { reveal(kernel_u_container_quota_4k_increased); };
    kernel_nonlock_projection_is_u_nonlock_fields(*pre); kernel_nonlock_projection_is_u_nonlock_fields(*post);
    assert(kernel_u_nonlock_fields(b).container_map[owner].quota_4k != kernel_u_nonlock_fields(a).container_map[owner].quota_4k) by { reveal(kernel_u_nonlock_fields); };
}

/// Retiring the zombie root process `process_ptr` of the container `container_ptr` drops it from the process projection and
/// from the container's processes, clears that container's zombie flag, and sets its 4K quota to the new quota of its 4K
/// allocator `allocator_ptr`. Its tables leave their maps and the pages it frees are not projected; every remaining process
/// keeps its state and its tables.
pub proof fn kernel_zombie_root_process_retired_implies_u_step(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        *post == (KernelK { prc_mp: post.prc_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.prc_mp.dom() == pre.prc_mp.dom().remove(process_ptr),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != container_ptr ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c),
        post.ctn_mp.spec_index(container_ptr).view() == (Container { zombie: false, ..pre.ctn_mp.spec_index(container_ptr).view() }),
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
            let container = a.container_map[container_ptr];
            &&& a.process_map.dom().contains(process_ptr)
            &&& a.process_map[process_ptr].owning_container == container_ptr
            &&& a.container_map.dom().contains(container_ptr)
            &&& container.quota_4k == pre.allc_4k_mp.spec_index(allocator_ptr).quota.view().view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(container_ptr, ContainerU {
                    zombie: false, owned_processes: container.owned_processes.remove(process_ptr), quota_4k: post.allc_4k_mp.spec_index(allocator_ptr).quota.view().view(), ..container }),
                process_map: a.process_map.remove(process_ptr),
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
    let container = a.container_map[container_ptr];
    assert_maps_equal!(b.container_map, a.container_map.insert(container_ptr, ContainerU { zombie: false, owned_processes: container.owned_processes.remove(process_ptr), quota_4k: quota, ..container }), c => {
        if pre.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c);
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c);
        }
    });
    assert_maps_equal!(b.process_map, a.process_map.remove(process_ptr), p => {
        if post.prc_mp.dom().contains(p) {
            kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p);
            if !pre.prc_mp.spec_index(p).view().zombie {
                process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, p); process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, process_ptr);
                if pre.prc_mp.spec_index(p).view().iommu_table is Some {
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
}

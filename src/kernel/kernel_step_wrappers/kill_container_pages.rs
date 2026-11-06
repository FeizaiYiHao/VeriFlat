use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
/// Moving a free 4K page, which spans the pages `moved` of the container `src`, from `src` to the container `dst`
/// while one page of 4K quota moves from the 4K allocator of `src` to that of `dst` changes only those two containers'
/// pages and 4K quota in the projection. Pages and allocators are not projected.
pub proof fn kernel_container_free_4k_page_moved_implies_u_step(pre: &KernelK, post: &KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, moved: Set<PagePtr>)
    requires
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        src != dst,
        pre.ctn_mp.dom().contains(src),
        pre.ctn_mp.dom().contains(dst),
        *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != src && c != dst ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
            c == src || c == dst ==> {
                &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                &&& post.ctn_mp.spec_index(c).control() == pre.ctn_mp.spec_index(c).control()
                &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            },
        moved.subset_of(pre.ctn_mp.spec_index(src).view().owned_pages.view()),
        post.ctn_mp.spec_index(src).view().owned_pages.view() == pre.ctn_mp.spec_index(src).view().owned_pages.view().difference(moved),
        post.ctn_mp.spec_index(dst).view().owned_pages.view() == pre.ctn_mp.spec_index(dst).view().owned_pages.view().union(moved),
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(a)]
            pre.allc_4k_mp.dom().contains(a) && a != pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_4k && a != pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_4k
                ==> post.allc_4k_mp.spec_index(a) == pre.allc_4k_mp.spec_index(a),
        0 < pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_4k).quota.view().value,
        post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_4k).quota.view().value
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_4k).quota.view().value - 1,
        post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_4k).quota.view().value
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_4k).quota.view().value + 1,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let target = a.container_map[src];
            let owner = a.container_map[dst];
            &&& a.container_map.dom().contains(src)
            &&& a.container_map.dom().contains(dst)
            &&& 0 < target.quota_4k
            &&& moved.subset_of(target.owned_pages)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(src, ContainerU { owned_pages: target.owned_pages.difference(moved), quota_4k: (target.quota_4k - 1) as usize, ..target })
                    .insert(dst, ContainerU { owned_pages: owner.owned_pages.union(moved), quota_4k: (owner.quota_4k + 1) as usize, ..owner }),
                ..a
            })
        }),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let target = a.container_map[src];
    let owner = a.container_map[dst];
    let x = ContainerU { owned_pages: target.owned_pages.difference(moved), quota_4k: (target.quota_4k - 1) as usize, ..target };
    let y = ContainerU { owned_pages: owner.owned_pages.union(moved), quota_4k: (owner.quota_4k + 1) as usize, ..owner };
    let expected = a.container_map.insert(src, x).insert(dst, y);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, src); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, dst);
    kernel_container_projection_at(pre, src); kernel_container_projection_at(pre, dst);
    assert(b.container_map[src] == x) by { kernel_container_projection_at(post, src); };
    assert(b.container_map[dst] == y) by { kernel_container_projection_at(post, dst); };
    assert_maps_equal!(b.container_map, expected, c => {
        if pre.ctn_mp.dom().contains(c) && c != src && c != dst {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c);
        }
    });
    kernel_process_maps_unchanged_implies_u_process_map(pre, post); kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(b.container_map[src].quota_4k != a.container_map[src].quota_4k);
}

/// Moving a free 2M page, which spans the pages `moved` of the container `src`, from `src` to the container `dst`
/// while one page of 2M quota moves from the 2M allocator of `src` to that of `dst` changes only those two containers'
/// pages and 2M quota in the projection. Pages and allocators are not projected.
pub proof fn kernel_container_free_2m_page_moved_implies_u_step(pre: &KernelK, post: &KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, moved: Set<PagePtr>)
    requires
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        src != dst,
        pre.ctn_mp.dom().contains(src),
        pre.ctn_mp.dom().contains(dst),
        *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, allc_2m_mp: post.allc_2m_mp, ..*pre }),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != src && c != dst ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
            c == src || c == dst ==> {
                &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                &&& post.ctn_mp.spec_index(c).control() == pre.ctn_mp.spec_index(c).control()
                &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            },
        moved.subset_of(pre.ctn_mp.spec_index(src).view().owned_pages.view()),
        post.ctn_mp.spec_index(src).view().owned_pages.view() == pre.ctn_mp.spec_index(src).view().owned_pages.view().difference(moved),
        post.ctn_mp.spec_index(dst).view().owned_pages.view() == pre.ctn_mp.spec_index(dst).view().owned_pages.view().union(moved),
        post.allc_2m_mp.dom() == pre.allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_2m_mp.spec_index(a)]
            pre.allc_2m_mp.dom().contains(a) && a != pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_2m && a != pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_2m
                ==> post.allc_2m_mp.spec_index(a) == pre.allc_2m_mp.spec_index(a),
        0 < pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_2m).quota.view().value,
        post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_2m).quota.view().value
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_2m).quota.view().value - 1,
        post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_2m).quota.view().value
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_2m).quota.view().value + 1,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let target = a.container_map[src];
            let owner = a.container_map[dst];
            &&& a.container_map.dom().contains(src)
            &&& a.container_map.dom().contains(dst)
            &&& 0 < target.quota_2m
            &&& moved.subset_of(target.owned_pages)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(src, ContainerU { owned_pages: target.owned_pages.difference(moved), quota_2m: (target.quota_2m - 1) as usize, ..target })
                    .insert(dst, ContainerU { owned_pages: owner.owned_pages.union(moved), quota_2m: (owner.quota_2m + 1) as usize, ..owner }),
                ..a
            })
        }),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let target = a.container_map[src];
    let owner = a.container_map[dst];
    let x = ContainerU { owned_pages: target.owned_pages.difference(moved), quota_2m: (target.quota_2m - 1) as usize, ..target };
    let y = ContainerU { owned_pages: owner.owned_pages.union(moved), quota_2m: (owner.quota_2m + 1) as usize, ..owner };
    let expected = a.container_map.insert(src, x).insert(dst, y);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, src); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, dst);
    kernel_container_projection_at(pre, src); kernel_container_projection_at(pre, dst);
    assert(b.container_map[src] == x) by { kernel_container_projection_at(post, src); };
    assert(b.container_map[dst] == y) by { kernel_container_projection_at(post, dst); };
    assert_maps_equal!(b.container_map, expected, c => {
        if pre.ctn_mp.dom().contains(c) && c != src && c != dst {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c);
        }
    });
    kernel_process_maps_unchanged_implies_u_process_map(pre, post); kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(b.container_map[src].quota_2m != a.container_map[src].quota_2m);
}

/// Moving a free 1G page, which spans the pages `moved` of the container `src`, from `src` to the container `dst` while one page of 1G quota moves from the 1G allocator of `src` to that of `dst` changes only those two containers' pages and 1G quota in the projection. Pages and allocators
/// are not projected.
pub proof fn kernel_container_free_1g_page_moved_implies_u_step(pre: &KernelK, post: &KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, moved: Set<PagePtr>)
    requires
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        src != dst,
        pre.ctn_mp.dom().contains(src),
        pre.ctn_mp.dom().contains(dst),
        *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, allc_1g_mp: post.allc_1g_mp, ..*pre }),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != src && c != dst ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
            c == src || c == dst ==> {
                &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                &&& post.ctn_mp.spec_index(c).control() == pre.ctn_mp.spec_index(c).control()
                &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            },
        moved.subset_of(pre.ctn_mp.spec_index(src).view().owned_pages.view()),
        post.ctn_mp.spec_index(src).view().owned_pages.view() == pre.ctn_mp.spec_index(src).view().owned_pages.view().difference(moved),
        post.ctn_mp.spec_index(dst).view().owned_pages.view() == pre.ctn_mp.spec_index(dst).view().owned_pages.view().union(moved),
        post.allc_1g_mp.dom() == pre.allc_1g_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_1g_mp.spec_index(a)]
            pre.allc_1g_mp.dom().contains(a) && a != pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_1g && a != pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_1g
                ==> post.allc_1g_mp.spec_index(a) == pre.allc_1g_mp.spec_index(a),
        0 < pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_1g).quota.view().value,
        post.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_1g).quota.view().value
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_1g).quota.view().value - 1,
        post.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_1g).quota.view().value
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_1g).quota.view().value + 1,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let target = a.container_map[src];
            let owner = a.container_map[dst];
            &&& a.container_map.dom().contains(src)
            &&& a.container_map.dom().contains(dst)
            &&& 0 < target.quota_1g
            &&& moved.subset_of(target.owned_pages)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(src, ContainerU { owned_pages: target.owned_pages.difference(moved), quota_1g: (target.quota_1g - 1) as usize, ..target })
                    .insert(dst, ContainerU { owned_pages: owner.owned_pages.union(moved), quota_1g: (owner.quota_1g + 1) as usize, ..owner }),
                ..a
            })
        }),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let target = a.container_map[src];
    let owner = a.container_map[dst];
    let x = ContainerU { owned_pages: target.owned_pages.difference(moved), quota_1g: (target.quota_1g - 1) as usize, ..target };
    let y = ContainerU { owned_pages: owner.owned_pages.union(moved), quota_1g: (owner.quota_1g + 1) as usize, ..owner };
    let expected = a.container_map.insert(src, x).insert(dst, y);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, src); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, dst);
    kernel_container_projection_at(pre, src); kernel_container_projection_at(pre, dst);
    assert(b.container_map[src] == x) by { kernel_container_projection_at(post, src); };
    assert(b.container_map[dst] == y) by { kernel_container_projection_at(post, dst); };
    assert_maps_equal!(b.container_map, expected, c => {
        if pre.ctn_mp.dom().contains(c) && c != src && c != dst {
            kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c);
        }
    });
    kernel_process_maps_unchanged_implies_u_process_map(pre, post); kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// A container whose 4K and 2M allocators hold no quota, whose 1G allocator holds exactly its free pages as quota, and whose 1G global pool is empty has no quota of any size in the projection; no 1G cpu cache holds a page.
pub proof fn kernel_container_quotas_zero_projection(krnl: &KernelK, ctn_ptr: RwLockContainerPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(ctn_ptr),
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value == 0,
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value == 0,
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value
            == krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view(),
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g).global_pool.view().view().len() == 0,
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(ctn_ptr),
        kernel_k_to_kernel_u(*krnl).container_map[ctn_ptr].quota_4k == 0,
        kernel_k_to_kernel_u(*krnl).container_map[ctn_ptr].quota_2m == 0,
        kernel_k_to_kernel_u(*krnl).container_map[ctn_ptr].quota_1g == 0,
        ({
            let allocator = krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g);
            &&& allocator.quota.view().value == 0
            &&& forall|i: CpuId| #![trigger allocator.cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) ==> allocator.cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }),
{
    let allc_ptr = krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g;
    let allocator = krnl.allc_1g_mp.spec_index(allc_ptr);
    kernel_container_projection_at(krnl, ctn_ptr); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr);
    allocator_perms_wf_map(krnl.allc_1g_mp); allocator_perms_wf_at(krnl.allc_1g_mp, allc_ptr); allocator.global_pool.view().linked_list.wf_implies_view_len_eq_len();
    assert(forall|i: CpuId| #![trigger allocator.cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) ==> allocator.cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0) by {
        reveal(allocator_1g_cpu_caches_empty_wf);
    };
    allocator.cpu_caches.view_index_eq_element_value(); lemma_cache_len_fold_all_zero(allocator.cpu_caches.view());
}
} // verus!

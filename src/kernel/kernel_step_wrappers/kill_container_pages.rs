use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
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
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
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
    assert_maps_equal!(b.process_map, a.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); } });
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.thread_map, a.thread_map, x => { if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); } });
    assert(b.container_map[src].quota_4k != a.container_map[src].quota_4k);
    kernel_nonlock_projection_is_u_nonlock_fields(*pre); kernel_nonlock_projection_is_u_nonlock_fields(*post);
    assert(kernel_u_nonlock_fields(b).container_map[src].quota_4k != kernel_u_nonlock_fields(a).container_map[src].quota_4k) by { reveal(kernel_u_nonlock_fields); };
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
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
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
    assert_maps_equal!(b.process_map, a.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); } });
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.thread_map, a.thread_map, x => { if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); } });
    assert(b.container_map[src].quota_2m != a.container_map[src].quota_2m);
    kernel_nonlock_projection_is_u_nonlock_fields(*pre); kernel_nonlock_projection_is_u_nonlock_fields(*post);
    assert(kernel_u_nonlock_fields(b).container_map[src].quota_2m != kernel_u_nonlock_fields(a).container_map[src].quota_2m) by { reveal(kernel_u_nonlock_fields); };
}

/// A container whose 4K and 2M allocators hold no quota and whose 1G allocator holds exactly its free pages as quota has
/// no quota of any size in the projection: a free 1G page could only start at page index 0, the only 1G-aligned page,
/// and would then merge the page that holds the container's 1G allocator.
pub proof fn kernel_container_quotas_zero_projection(krnl: &KernelK, container_ptr: RwLockContainerPtr)
    requires
        krnl.inv(),
        krnl.ctn_mp.dom().contains(container_ptr),
        krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value == 0,
        krnl.allc_2m_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value == 0,
        krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value
            == krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view(),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(container_ptr),
        kernel_k_to_kernel_u(*krnl).container_map[container_ptr].quota_4k == 0,
        kernel_k_to_kernel_u(*krnl).container_map[container_ptr].quota_2m == 0,
        kernel_k_to_kernel_u(*krnl).container_map[container_ptr].quota_1g == 0,
        ({
            let allocator = krnl.allc_1g_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g);
            &&& allocator.quota.view().value == 0
            &&& forall|i: CpuId| #![trigger allocator.cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) ==> allocator.cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }),
{
    let allocator_ptr = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g;
    let allocator = krnl.allc_1g_mp.spec_index(allocator_ptr);
    let pool = allocator.global_pool.view().view();
    kernel_container_projection_at(krnl, container_ptr); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
    allocator_perms_wf_map(krnl.allc_1g_mp); allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr); allocator.global_pool.view().linked_list.lemma_len_view();
    assert(pool.len() == 0) by {
        if pool.len() > 0 {
            let page_ptr = pool[0];
            let i = page_ptr2page_index(page_ptr);
            let j = page_ptr2page_index(allocator_ptr);
            assert(pool.contains(page_ptr));
            allocator_free_page_ptrs_wf_global_at(krnl.allc_1g_mp, allocator_ptr, page_ptr); container_allocator_free_1g_page_wf_global_at(krnl.allc_1g_mp, krnl.pg_arr, allocator_ptr, page_ptr);
            page_ptr_valid_imply_page_index_valid(); allocator_1g_pages_wf_at(krnl.pg_arr, krnl.allc_1g_mp, allocator_ptr);
            hugepage_1g_wf_head_at(krnl.pg_arr, i); hugepage_1g_wf_tail_forward_at(krnl.pg_arr, i, j);
        }
    };
    lemma_free_1g_cache_len_fold_zero(krnl, allocator_ptr, NUM_CPUS as int);
    assert(allocator.cpu_caches.view().take(NUM_CPUS as int) =~= allocator.cpu_caches.view());
}

/// The first `n` 1G caches of the 1G allocator `allocator_ptr` hold no page: a free 1G page could only start at page index
/// 0, the only 1G-aligned page, and would then merge the page that holds the allocator itself.
proof fn lemma_free_1g_cache_len_fold_zero(krnl: &KernelK, allocator_ptr: RwLockPageAllocatorPtr, n: int)
    requires
        krnl.inv(),
        krnl.allc_1g_mp.dom().contains(allocator_ptr),
        0 <= n <= NUM_CPUS,
    ensures
        krnl.allc_1g_mp.spec_index(allocator_ptr).cpu_caches.view().take(n)
            .fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache<ALLOCATOR_SIZE_1G>, (), (), NO_KILL_STATE>| { sum + cpu_rw_lock.view().linked_list.len() }) == 0,
        forall|i: CpuId| #![trigger krnl.allc_1g_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i)]
            i < n ==> krnl.allc_1g_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0,
    decreases n,
{
    let caches = krnl.allc_1g_mp.spec_index(allocator_ptr).cpu_caches;
    if n > 0 {
        lemma_free_1g_cache_len_fold_zero(krnl, allocator_ptr, n - 1);
        allocator_perms_wf_map(krnl.allc_1g_mp); allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr);
        assert(caches.view().take(n).drop_last() =~= caches.view().take(n - 1));
        caches.lemma_view_index();
        let cache = caches.spec_index((n - 1) as usize).view().view();
        cache.linked_list.lemma_len_view();
        assert(cache.view().len() == 0) by {
            if cache.view().len() > 0 {
                let page_ptr = cache.view()[0];
                let i = page_ptr2page_index(page_ptr);
                let j = page_ptr2page_index(allocator_ptr);
                assert(caches.spec_index((n - 1) as usize).view().view().view().contains(page_ptr));
                allocator_free_page_ptrs_wf_cache_at(krnl.allc_1g_mp, allocator_ptr, (n - 1) as usize, page_ptr);
                container_allocator_free_1g_page_wf_cache_at(krnl.allc_1g_mp, krnl.pg_arr, allocator_ptr, (n - 1) as usize, page_ptr);
                page_ptr_valid_imply_page_index_valid(); allocator_1g_pages_wf_at(krnl.pg_arr, krnl.allc_1g_mp, allocator_ptr);
                hugepage_1g_wf_head_at(krnl.pg_arr, i); hugepage_1g_wf_tail_forward_at(krnl.pg_arr, i, j);
            }
        };
    }
}
} // verus!

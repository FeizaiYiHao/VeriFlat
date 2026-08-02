use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Semantic allocator fields read by kernel invariants.  Internal quota,
/// cache, and global-pool lock owners are deliberately excluded.
#[verifier::opaque]
pub open spec fn allocator_4k_invariant_fields_unchanged(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|a_ptr: RwLockPageAllocatorPtr|
        #![trigger post.spec_index(a_ptr).owning_container]
        pre.dom().contains(a_ptr) ==>
        {
            &&& post.spec_index(a_ptr).owning_container
                == pre.spec_index(a_ptr).owning_container
            &&& post.spec_index(a_ptr).total_free_pages
                == pre.spec_index(a_ptr).total_free_pages
            &&& post.spec_index(a_ptr).quota.view()
                == pre.spec_index(a_ptr).quota.view()
            &&& post.spec_index(a_ptr).global_pool.view()
                == pre.spec_index(a_ptr).global_pool.view()
            &&& forall|cpu_id: CpuId|
                #![trigger post.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()]
                cpu_id_valid(cpu_id) ==>
                    post.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
                    == pre.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view()
        }
}

pub proof fn allocator_4k_cache_lock_op_preserves_invariant_fields(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    changed_allocator: RwLockPageAllocatorPtr,
    changed_cpu: CpuId,
)
    requires
        pre.dom() =~= post.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(a_ptr)]
            pre.dom().contains(a_ptr)
                && a_ptr != changed_allocator ==>
                post.spec_index(a_ptr) == pre.spec_index(a_ptr),
        post.spec_index(changed_allocator).owning_container
            == pre.spec_index(changed_allocator).owning_container,
        post.spec_index(changed_allocator).total_free_pages
            == pre.spec_index(changed_allocator).total_free_pages,
        post.spec_index(changed_allocator).quota
            == pre.spec_index(changed_allocator).quota,
        post.spec_index(changed_allocator).global_pool
            == pre.spec_index(changed_allocator).global_pool,
        post.spec_index(changed_allocator).cpu_caches.unchanged_except(
            &pre.spec_index(changed_allocator).cpu_caches,
            changed_cpu,
        ),
        post.spec_index(changed_allocator).cpu_caches
            .spec_index(changed_cpu).view().view()
        == pre.spec_index(changed_allocator).cpu_caches
            .spec_index(changed_cpu).view().view(),
    ensures
        allocator_4k_invariant_fields_unchanged(pre, post),
{
    reveal(allocator_4k_invariant_fields_unchanged);
    reveal(LockedArray::unchanged_except);
}

pub proof fn allocator_4k_quota_lock_op_preserves_invariant_fields(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    changed: RwLockPageAllocatorPtr,
)
    requires
        pre.dom() =~= post.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(a_ptr)]
            pre.dom().contains(a_ptr) && a_ptr != changed ==>
                post.spec_index(a_ptr) == pre.spec_index(a_ptr),
        post.spec_index(changed).owning_container
            == pre.spec_index(changed).owning_container,
        post.spec_index(changed).total_free_pages
            == pre.spec_index(changed).total_free_pages,
        post.spec_index(changed).cpu_caches
            == pre.spec_index(changed).cpu_caches,
        post.spec_index(changed).global_pool
            == pre.spec_index(changed).global_pool,
        post.spec_index(changed).quota.view()
            == pre.spec_index(changed).quota.view(),
    ensures
        allocator_4k_invariant_fields_unchanged(pre, post),
{
    reveal(allocator_4k_invariant_fields_unchanged);
}

pub proof fn allocator_4k_global_pool_lock_op_preserves_invariant_fields(
    pre: PageAllocatorUnLockedMap,
    post: PageAllocatorUnLockedMap,
    changed: RwLockPageAllocatorPtr,
)
    requires
        pre.dom() =~= post.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.spec_index(a_ptr)]
            pre.dom().contains(a_ptr) && a_ptr != changed ==>
                post.spec_index(a_ptr) == pre.spec_index(a_ptr),
        post.spec_index(changed).owning_container
            == pre.spec_index(changed).owning_container,
        post.spec_index(changed).total_free_pages
            == pre.spec_index(changed).total_free_pages,
        post.spec_index(changed).cpu_caches
            == pre.spec_index(changed).cpu_caches,
        post.spec_index(changed).quota
            == pre.spec_index(changed).quota,
        post.spec_index(changed).global_pool.view()
            == pre.spec_index(changed).global_pool.view(),
    ensures
        allocator_4k_invariant_fields_unchanged(pre, post),
{
    reveal(allocator_4k_invariant_fields_unchanged);
}

pub proof fn kernel_inv_preserved_for_allocator_4k_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.inv(),
        allocator_perms_wf(post.allocator_4k_map),
        allocator_4k_invariant_fields_unchanged(
            pre.allocator_4k_map,
            post.allocator_4k_map,
        ),
        post.pagetable_map == pre.pagetable_map,
        post.iommu_table_map == pre.iommu_table_map,
        post.iommu_root_table == pre.iommu_root_table,
        post.page_array == pre.page_array,
        post.cpu_array == pre.cpu_array,
        post.cpu_tlb == pre.cpu_tlb,
        post.iommu_tlb == pre.iommu_tlb,
        post.root_container == pre.root_container,
        post.container_map == pre.container_map,
        post.scheduler_map == pre.scheduler_map,
        post.pcid_allocator_map == pre.pcid_allocator_map,
        post.process_map == pre.process_map,
        post.thread_map == pre.thread_map,
        post.endpoint_map == pre.endpoint_map,
        post.allocator_2m_map == pre.allocator_2m_map,
        post.allocator_1g_map == pre.allocator_1g_map,
        post.default_pagetable == pre.default_pagetable,
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(
            post.page_array,
            post.allocator_4k_map,
            post.allocator_2m_map,
            post.allocator_1g_map,
        )) by {
            reveal(allocator_4k_invariant_fields_unchanged);
            reveal(allocator_4k_pages_wf);
            reveal(allocator_2m_pages_wf);
            reveal(allocator_1g_pages_wf);
        };
        assert(container_process_allocator_quota_4k_wf(
            post.container_map,
            post.process_map,
            post.thread_map,
            post.allocator_4k_map,
        )) by {
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr)
                    .view_rodata().view().allocator_ptr_4k]
                post.container_map.dom().contains(c_ptr)
            implies {
                let alloc_ptr = post.container_map.spec_index(c_ptr)
                    .view_rodata().view().allocator_ptr_4k;
                &&& post.allocator_4k_map.spec_index(alloc_ptr).quota.view()
                    == pre.allocator_4k_map.spec_index(alloc_ptr).quota.view()
                &&& post.allocator_4k_map.spec_index(alloc_ptr).total_free_pages
                    == pre.allocator_4k_map.spec_index(alloc_ptr).total_free_pages
            } by {
                assert(pre.allocator_4k_map.dom().contains(
                    post.container_map.spec_index(c_ptr)
                        .view_rodata().view().allocator_ptr_4k,
                )) by {
                    reveal(container_allocator_wf);
                };
                assert(post.allocator_4k_map.spec_index(
                    post.container_map.spec_index(c_ptr)
                        .view_rodata().view().allocator_ptr_4k,
                ).owning_container
                    == pre.allocator_4k_map.spec_index(
                        post.container_map.spec_index(c_ptr)
                            .view_rodata().view().allocator_ptr_4k,
                    ).owning_container) by {
                    reveal(allocator_4k_invariant_fields_unchanged);
                };
                reveal(allocator_4k_invariant_fields_unchanged);
            };
            reveal(allocator_4k_invariant_fields_unchanged);
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_allocator_wf);
        };
        assert(container_allocator_wf(
            post.container_map,
            post.allocator_4k_map,
            post.allocator_2m_map,
            post.allocator_1g_map,
        )) by {
            reveal(allocator_4k_invariant_fields_unchanged);
            reveal(container_allocator_wf);
        };
        assert(allocator_free_page_ptrs_wf(
            post.allocator_4k_map,
        )) by {
            assert forall|a_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
                #![trigger post.allocator_4k_map.spec_index(a_ptr)
                    .global_pool.view().view().contains(page_ptr)]
                post.allocator_4k_map.dom().contains(a_ptr)
                    && post.allocator_4k_map.spec_index(a_ptr)
                        .global_pool.view().view().contains(page_ptr)
            implies
                page_ptr_valid(page_ptr)
            by {
                assert(post.allocator_4k_map.spec_index(a_ptr).owning_container
                    == pre.allocator_4k_map.spec_index(a_ptr).owning_container) by {
                    reveal(allocator_4k_invariant_fields_unchanged);
                };
                reveal(allocator_4k_invariant_fields_unchanged);
                reveal(allocator_free_page_ptrs_wf);
            };
            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, page_ptr: PagePtr|
                #![trigger post.allocator_4k_map.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view().view().contains(page_ptr)]
                post.allocator_4k_map.dom().contains(a_ptr)
                    && cpu_id_valid(cpu_id)
                    && post.allocator_4k_map.spec_index(a_ptr).cpu_caches
                        .spec_index(cpu_id).view().view().view().contains(page_ptr)
            implies
                page_ptr_valid(page_ptr)
            by {
                assert(post.allocator_4k_map.spec_index(a_ptr).owning_container
                    == pre.allocator_4k_map.spec_index(a_ptr).owning_container) by {
                    reveal(allocator_4k_invariant_fields_unchanged);
                };
                reveal(allocator_4k_invariant_fields_unchanged);
                reveal(allocator_free_page_ptrs_wf);
            };
            reveal(allocator_4k_invariant_fields_unchanged);
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_allocator_free_4k_page_wf(
            post.container_map,
            post.allocator_4k_map,
            post.page_array,
        )) by {
            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                #![trigger post.allocator_4k_map.spec_index(a_ptr)
                    .cpu_caches.spec_index(cpu_id).view().view()]
                post.allocator_4k_map.dom().contains(a_ptr)
                    && cpu_id_valid(cpu_id)
            implies
                post.allocator_4k_map.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()
                == pre.allocator_4k_map.spec_index(a_ptr).cpu_caches
                    .spec_index(cpu_id).view().view()
            by {
                assert(post.allocator_4k_map.spec_index(a_ptr).owning_container
                    == pre.allocator_4k_map.spec_index(a_ptr).owning_container) by {
                    reveal(allocator_4k_invariant_fields_unchanged);
                };
                reveal(allocator_4k_invariant_fields_unchanged);
            };
            reveal(allocator_4k_invariant_fields_unchanged);
            lemma_no_change_imply_container_allocator_free_4k_page_wf_forall();
        };
    };
    assert(post.inv()) by {
        reveal(KernelK::inv);
    };
}

pub open spec fn allocator_4k_kernel_lock_fields_framed(
    pre: KernelK,
    post: KernelK,
) -> bool {
    &&& pre.inv()
    &&& allocator_perms_wf(post.allocator_4k_map)
    &&& allocator_4k_invariant_fields_unchanged(
        pre.allocator_4k_map,
        post.allocator_4k_map,
    )
    &&& post.pagetable_map == pre.pagetable_map
    &&& post.iommu_table_map == pre.iommu_table_map
    &&& post.iommu_root_table == pre.iommu_root_table
    &&& post.page_array == pre.page_array
    &&& post.cpu_array == pre.cpu_array
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.root_container == pre.root_container
    &&& post.container_map == pre.container_map
    &&& post.scheduler_map == pre.scheduler_map
    &&& post.pcid_allocator_map == pre.pcid_allocator_map
    &&& post.process_map == pre.process_map
    &&& post.thread_map == pre.thread_map
    &&& post.endpoint_map == pre.endpoint_map
    &&& post.allocator_2m_map == pre.allocator_2m_map
    &&& post.allocator_1g_map == pre.allocator_1g_map
    &&& post.default_pagetable == pre.default_pagetable
}

pub proof fn lemma_no_change_imply_kernel_inv_for_allocator_4k_lock_fields_forall()
    ensures
        forall|pre: KernelK, post: KernelK|
            #![trigger pre.inv(), post.inv()]
            allocator_4k_kernel_lock_fields_framed(pre, post)
                ==> post.inv(),
{
    assert forall|pre: KernelK, post: KernelK| #![auto]
        allocator_4k_kernel_lock_fields_framed(pre, post)
    implies
        post.inv()
    by {
        kernel_inv_preserved_for_allocator_4k_lock_op(pre, post);
    };
}

pub proof fn lemma_no_change_imply_kernel_inv_for_allocator_4k_quota_lock_op_forall()
    ensures
        forall|pre: KernelK, post: KernelK, changed: RwLockPageAllocatorPtr|
            #![trigger
                allocator_4k_kernel_lock_fields_framed(pre, post),
                post.allocator_4k_map.spec_index(changed).quota
            ]
            pre.inv()
            && pre.allocator_4k_map.dom().contains(changed)
            && post.allocator_4k_map.perms_wf()
            && post.allocator_4k_map.spec_index(changed).wf()
            && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
            && (forall|a_ptr: RwLockPageAllocatorPtr|
                #![trigger post.allocator_4k_map.spec_index(a_ptr)]
                pre.allocator_4k_map.dom().contains(a_ptr)
                    && a_ptr != changed ==>
                    post.allocator_4k_map.spec_index(a_ptr)
                        == pre.allocator_4k_map.spec_index(a_ptr))
            && post.allocator_4k_map.spec_index(changed).owning_container
                == pre.allocator_4k_map.spec_index(changed).owning_container
            && post.allocator_4k_map.spec_index(changed).total_free_pages
                == pre.allocator_4k_map.spec_index(changed).total_free_pages
            && post.allocator_4k_map.spec_index(changed).cpu_caches
                == pre.allocator_4k_map.spec_index(changed).cpu_caches
            && post.allocator_4k_map.spec_index(changed).global_pool
                == pre.allocator_4k_map.spec_index(changed).global_pool
            && post.allocator_4k_map.spec_index(changed).quota.view()
                == pre.allocator_4k_map.spec_index(changed).quota.view()
            && post.pagetable_map == pre.pagetable_map
            && post.iommu_table_map == pre.iommu_table_map
            && post.iommu_root_table == pre.iommu_root_table
            && post.page_array == pre.page_array
            && post.cpu_array == pre.cpu_array
            && post.cpu_tlb == pre.cpu_tlb
            && post.iommu_tlb == pre.iommu_tlb
            && post.root_container == pre.root_container
            && post.container_map == pre.container_map
            && post.scheduler_map == pre.scheduler_map
            && post.pcid_allocator_map == pre.pcid_allocator_map
            && post.process_map == pre.process_map
            && post.thread_map == pre.thread_map
            && post.endpoint_map == pre.endpoint_map
            && post.allocator_2m_map == pre.allocator_2m_map
            && post.allocator_1g_map == pre.allocator_1g_map
            && post.default_pagetable == pre.default_pagetable
            ==> allocator_4k_kernel_lock_fields_framed(pre, post),
        forall|pre: KernelK, post: KernelK|
            #![trigger pre.inv(), post.inv()]
            allocator_4k_kernel_lock_fields_framed(pre, post)
                ==> post.inv(),
{
    assert forall|pre: KernelK, post: KernelK, changed: RwLockPageAllocatorPtr| #![auto]
        pre.inv()
        && pre.allocator_4k_map.dom().contains(changed)
        && post.allocator_4k_map.perms_wf()
        && post.allocator_4k_map.spec_index(changed).wf()
        && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
        && (forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a_ptr)]
            pre.allocator_4k_map.dom().contains(a_ptr)
                && a_ptr != changed ==>
                post.allocator_4k_map.spec_index(a_ptr)
                    == pre.allocator_4k_map.spec_index(a_ptr))
        && post.allocator_4k_map.spec_index(changed).owning_container
            == pre.allocator_4k_map.spec_index(changed).owning_container
        && post.allocator_4k_map.spec_index(changed).total_free_pages
            == pre.allocator_4k_map.spec_index(changed).total_free_pages
        && post.allocator_4k_map.spec_index(changed).cpu_caches
            == pre.allocator_4k_map.spec_index(changed).cpu_caches
        && post.allocator_4k_map.spec_index(changed).global_pool
            == pre.allocator_4k_map.spec_index(changed).global_pool
        && post.allocator_4k_map.spec_index(changed).quota.view()
            == pre.allocator_4k_map.spec_index(changed).quota.view()
        && post.pagetable_map == pre.pagetable_map
        && post.iommu_table_map == pre.iommu_table_map
        && post.iommu_root_table == pre.iommu_root_table
        && post.page_array == pre.page_array
        && post.cpu_array == pre.cpu_array
        && post.cpu_tlb == pre.cpu_tlb
        && post.iommu_tlb == pre.iommu_tlb
        && post.root_container == pre.root_container
        && post.container_map == pre.container_map
        && post.scheduler_map == pre.scheduler_map
        && post.pcid_allocator_map == pre.pcid_allocator_map
        && post.process_map == pre.process_map
        && post.thread_map == pre.thread_map
        && post.endpoint_map == pre.endpoint_map
        && post.allocator_2m_map == pre.allocator_2m_map
        && post.allocator_1g_map == pre.allocator_1g_map
        && post.default_pagetable == pre.default_pagetable
    implies
        allocator_4k_kernel_lock_fields_framed(pre, post)
    by {
        assert(allocator_perms_wf(post.allocator_4k_map)) by {
            reveal(allocator_perms_wf);
        };
        allocator_4k_quota_lock_op_preserves_invariant_fields(
            pre.allocator_4k_map,
            post.allocator_4k_map,
            changed,
        );
    };
    lemma_no_change_imply_kernel_inv_for_allocator_4k_lock_fields_forall();
}

pub proof fn lemma_no_change_imply_kernel_inv_for_allocator_4k_cache_lock_op_forall()
    ensures
        forall|pre: KernelK,
            post: KernelK,
            changed_allocator: RwLockPageAllocatorPtr,
            changed_cpu: CpuId|
            #![trigger
                allocator_4k_kernel_lock_fields_framed(pre, post),
                post.allocator_4k_map.spec_index(changed_allocator)
                    .cpu_caches.spec_index(changed_cpu)
            ]
            pre.inv()
            && pre.allocator_4k_map.dom().contains(changed_allocator)
            && post.allocator_4k_map.perms_wf()
            && post.allocator_4k_map.spec_index(changed_allocator).wf()
            && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
            && (forall|a_ptr: RwLockPageAllocatorPtr|
                #![trigger post.allocator_4k_map.spec_index(a_ptr)]
                pre.allocator_4k_map.dom().contains(a_ptr)
                    && a_ptr != changed_allocator ==>
                    post.allocator_4k_map.spec_index(a_ptr)
                        == pre.allocator_4k_map.spec_index(a_ptr))
            && post.allocator_4k_map.spec_index(changed_allocator)
                .owning_container
                == pre.allocator_4k_map.spec_index(changed_allocator)
                    .owning_container
            && post.allocator_4k_map.spec_index(changed_allocator)
                .total_free_pages
                == pre.allocator_4k_map.spec_index(changed_allocator)
                    .total_free_pages
            && post.allocator_4k_map.spec_index(changed_allocator).quota
                == pre.allocator_4k_map.spec_index(changed_allocator).quota
            && post.allocator_4k_map.spec_index(changed_allocator).global_pool
                == pre.allocator_4k_map.spec_index(changed_allocator).global_pool
            && post.allocator_4k_map.spec_index(changed_allocator)
                .cpu_caches.unchanged_except(
                    &pre.allocator_4k_map.spec_index(changed_allocator)
                        .cpu_caches,
                    changed_cpu,
                )
            && post.allocator_4k_map.spec_index(changed_allocator)
                .cpu_caches.spec_index(changed_cpu).view().view()
                == pre.allocator_4k_map.spec_index(changed_allocator)
                    .cpu_caches.spec_index(changed_cpu).view().view()
            && post.pagetable_map == pre.pagetable_map
            && post.iommu_table_map == pre.iommu_table_map
            && post.iommu_root_table == pre.iommu_root_table
            && post.page_array == pre.page_array
            && post.cpu_array == pre.cpu_array
            && post.cpu_tlb == pre.cpu_tlb
            && post.iommu_tlb == pre.iommu_tlb
            && post.root_container == pre.root_container
            && post.container_map == pre.container_map
            && post.scheduler_map == pre.scheduler_map
            && post.pcid_allocator_map == pre.pcid_allocator_map
            && post.process_map == pre.process_map
            && post.thread_map == pre.thread_map
            && post.endpoint_map == pre.endpoint_map
            && post.allocator_2m_map == pre.allocator_2m_map
            && post.allocator_1g_map == pre.allocator_1g_map
            && post.default_pagetable == pre.default_pagetable
            ==> allocator_4k_kernel_lock_fields_framed(pre, post),
        forall|pre: KernelK, post: KernelK|
            #![trigger pre.inv(), post.inv()]
            allocator_4k_kernel_lock_fields_framed(pre, post)
                ==> post.inv(),
{
    assert forall|pre: KernelK,
        post: KernelK,
        changed_allocator: RwLockPageAllocatorPtr,
        changed_cpu: CpuId| #![auto]
        pre.inv()
        && pre.allocator_4k_map.dom().contains(changed_allocator)
        && post.allocator_4k_map.perms_wf()
        && post.allocator_4k_map.spec_index(changed_allocator).wf()
        && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
        && (forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a_ptr)]
            pre.allocator_4k_map.dom().contains(a_ptr)
                && a_ptr != changed_allocator ==>
                post.allocator_4k_map.spec_index(a_ptr)
                    == pre.allocator_4k_map.spec_index(a_ptr))
        && post.allocator_4k_map.spec_index(changed_allocator)
            .owning_container
            == pre.allocator_4k_map.spec_index(changed_allocator)
                .owning_container
        && post.allocator_4k_map.spec_index(changed_allocator)
            .total_free_pages
            == pre.allocator_4k_map.spec_index(changed_allocator)
                .total_free_pages
        && post.allocator_4k_map.spec_index(changed_allocator).quota
            == pre.allocator_4k_map.spec_index(changed_allocator).quota
        && post.allocator_4k_map.spec_index(changed_allocator).global_pool
            == pre.allocator_4k_map.spec_index(changed_allocator).global_pool
        && post.allocator_4k_map.spec_index(changed_allocator)
            .cpu_caches.unchanged_except(
                &pre.allocator_4k_map.spec_index(changed_allocator).cpu_caches,
                changed_cpu,
            )
        && post.allocator_4k_map.spec_index(changed_allocator)
            .cpu_caches.spec_index(changed_cpu).view().view()
            == pre.allocator_4k_map.spec_index(changed_allocator)
                .cpu_caches.spec_index(changed_cpu).view().view()
        && post.pagetable_map == pre.pagetable_map
        && post.iommu_table_map == pre.iommu_table_map
        && post.iommu_root_table == pre.iommu_root_table
        && post.page_array == pre.page_array
        && post.cpu_array == pre.cpu_array
        && post.cpu_tlb == pre.cpu_tlb
        && post.iommu_tlb == pre.iommu_tlb
        && post.root_container == pre.root_container
        && post.container_map == pre.container_map
        && post.scheduler_map == pre.scheduler_map
        && post.pcid_allocator_map == pre.pcid_allocator_map
        && post.process_map == pre.process_map
        && post.thread_map == pre.thread_map
        && post.endpoint_map == pre.endpoint_map
        && post.allocator_2m_map == pre.allocator_2m_map
        && post.allocator_1g_map == pre.allocator_1g_map
        && post.default_pagetable == pre.default_pagetable
    implies
        allocator_4k_kernel_lock_fields_framed(pre, post)
    by {
        assert(allocator_perms_wf(post.allocator_4k_map)) by {
            reveal(allocator_perms_wf);
        };
        allocator_4k_cache_lock_op_preserves_invariant_fields(
            pre.allocator_4k_map,
            post.allocator_4k_map,
            changed_allocator,
            changed_cpu,
        );
    };
    lemma_no_change_imply_kernel_inv_for_allocator_4k_lock_fields_forall();
}

pub proof fn lemma_no_change_imply_kernel_inv_for_allocator_4k_global_pool_lock_op_forall()
    ensures
        forall|pre: KernelK, post: KernelK, changed: RwLockPageAllocatorPtr|
            #![trigger
                allocator_4k_kernel_lock_fields_framed(pre, post),
                post.allocator_4k_map.spec_index(changed).global_pool
            ]
            pre.inv()
            && pre.allocator_4k_map.dom().contains(changed)
            && post.allocator_4k_map.perms_wf()
            && post.allocator_4k_map.spec_index(changed).wf()
            && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
            && (forall|a_ptr: RwLockPageAllocatorPtr|
                #![trigger post.allocator_4k_map.spec_index(a_ptr)]
                pre.allocator_4k_map.dom().contains(a_ptr)
                    && a_ptr != changed ==>
                    post.allocator_4k_map.spec_index(a_ptr)
                        == pre.allocator_4k_map.spec_index(a_ptr))
            && post.allocator_4k_map.spec_index(changed).owning_container
                == pre.allocator_4k_map.spec_index(changed).owning_container
            && post.allocator_4k_map.spec_index(changed).total_free_pages
                == pre.allocator_4k_map.spec_index(changed).total_free_pages
            && post.allocator_4k_map.spec_index(changed).cpu_caches
                == pre.allocator_4k_map.spec_index(changed).cpu_caches
            && post.allocator_4k_map.spec_index(changed).quota
                == pre.allocator_4k_map.spec_index(changed).quota
            && post.allocator_4k_map.spec_index(changed).global_pool.view()
                == pre.allocator_4k_map.spec_index(changed).global_pool.view()
            && post.pagetable_map == pre.pagetable_map
            && post.iommu_table_map == pre.iommu_table_map
            && post.iommu_root_table == pre.iommu_root_table
            && post.page_array == pre.page_array
            && post.cpu_array == pre.cpu_array
            && post.cpu_tlb == pre.cpu_tlb
            && post.iommu_tlb == pre.iommu_tlb
            && post.root_container == pre.root_container
            && post.container_map == pre.container_map
            && post.scheduler_map == pre.scheduler_map
            && post.pcid_allocator_map == pre.pcid_allocator_map
            && post.process_map == pre.process_map
            && post.thread_map == pre.thread_map
            && post.endpoint_map == pre.endpoint_map
            && post.allocator_2m_map == pre.allocator_2m_map
            && post.allocator_1g_map == pre.allocator_1g_map
            && post.default_pagetable == pre.default_pagetable
            ==> allocator_4k_kernel_lock_fields_framed(pre, post),
        forall|pre: KernelK, post: KernelK|
            #![trigger pre.inv(), post.inv()]
            allocator_4k_kernel_lock_fields_framed(pre, post)
                ==> post.inv(),
{
    assert forall|pre: KernelK, post: KernelK, changed: RwLockPageAllocatorPtr| #![auto]
        pre.inv()
        && pre.allocator_4k_map.dom().contains(changed)
        && post.allocator_4k_map.perms_wf()
        && post.allocator_4k_map.spec_index(changed).wf()
        && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
        && (forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a_ptr)]
            pre.allocator_4k_map.dom().contains(a_ptr)
                && a_ptr != changed ==>
                post.allocator_4k_map.spec_index(a_ptr)
                    == pre.allocator_4k_map.spec_index(a_ptr))
        && post.allocator_4k_map.spec_index(changed).owning_container
            == pre.allocator_4k_map.spec_index(changed).owning_container
        && post.allocator_4k_map.spec_index(changed).total_free_pages
            == pre.allocator_4k_map.spec_index(changed).total_free_pages
        && post.allocator_4k_map.spec_index(changed).cpu_caches
            == pre.allocator_4k_map.spec_index(changed).cpu_caches
        && post.allocator_4k_map.spec_index(changed).quota
            == pre.allocator_4k_map.spec_index(changed).quota
        && post.allocator_4k_map.spec_index(changed).global_pool.view()
            == pre.allocator_4k_map.spec_index(changed).global_pool.view()
        && post.pagetable_map == pre.pagetable_map
        && post.iommu_table_map == pre.iommu_table_map
        && post.iommu_root_table == pre.iommu_root_table
        && post.page_array == pre.page_array
        && post.cpu_array == pre.cpu_array
        && post.cpu_tlb == pre.cpu_tlb
        && post.iommu_tlb == pre.iommu_tlb
        && post.root_container == pre.root_container
        && post.container_map == pre.container_map
        && post.scheduler_map == pre.scheduler_map
        && post.pcid_allocator_map == pre.pcid_allocator_map
        && post.process_map == pre.process_map
        && post.thread_map == pre.thread_map
        && post.endpoint_map == pre.endpoint_map
        && post.allocator_2m_map == pre.allocator_2m_map
        && post.allocator_1g_map == pre.allocator_1g_map
        && post.default_pagetable == pre.default_pagetable
    implies
        allocator_4k_kernel_lock_fields_framed(pre, post)
    by {
        assert(allocator_perms_wf(post.allocator_4k_map)) by {
            reveal(allocator_perms_wf);
        };
        allocator_4k_global_pool_lock_op_preserves_invariant_fields(
            pre.allocator_4k_map,
            post.allocator_4k_map,
            changed,
        );
    };
    lemma_no_change_imply_kernel_inv_for_allocator_4k_lock_fields_forall();
}

}

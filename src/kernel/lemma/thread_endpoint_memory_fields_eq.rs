use vstd::prelude::*;
use crate::*;

verus! {

/// Fields read by memory-management invariants when an operation changes only
/// thread/endpoint protocol state. Thread and endpoint domains remain semantic
/// memory-management inputs; scheduler, CPU, lock, queue, descriptor, and
/// reference-counter fields are deliberately outside this relation.
pub open spec fn thread_endpoint_memory_management_fields_unchanged(
    pre: KernelK,
    post: KernelK,
) -> bool {
    &&& post.pagetable_map == pre.pagetable_map
    &&& post.iommu_table_map == pre.iommu_table_map
    &&& post.page_array == pre.page_array
    &&& post.container_map == pre.container_map
    &&& post.pcid_allocator_map == pre.pcid_allocator_map
    &&& post.process_map == pre.process_map
    &&& post.allocator_4k_map == pre.allocator_4k_map
    &&& post.allocator_2m_map == pre.allocator_2m_map
    &&& post.allocator_1g_map == pre.allocator_1g_map
    &&& post.thread_map.dom() =~= pre.thread_map.dom()
    &&& post.endpoint_map.dom() =~= pre.endpoint_map.dom()
    &&& forall|thread_ptr: RwLockThreadPtr|
        #![trigger pre.thread_map.spec_index(thread_ptr)]
        #![trigger post.thread_map.spec_index(thread_ptr)]
        pre.thread_map.dom().contains(thread_ptr) ==>
        {
            &&& thread_effective_quota_4k(
                post.thread_map.spec_index(thread_ptr),
            ) == thread_effective_quota_4k(
                pre.thread_map.spec_index(thread_ptr),
            )
            &&& thread_effective_quota_2m(
                post.thread_map.spec_index(thread_ptr),
            ) == thread_effective_quota_2m(
                pre.thread_map.spec_index(thread_ptr),
            )
            &&& thread_effective_quota_1g(
                post.thread_map.spec_index(thread_ptr),
            ) == thread_effective_quota_1g(
                pre.thread_map.spec_index(thread_ptr),
            )
            &&& post.thread_map.spec_index(thread_ptr).view()
                .direct_free_quota_pending_4k
                == pre.thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_4k
            &&& post.thread_map.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_4k
                == pre.thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_4k
            &&& post.thread_map.spec_index(thread_ptr).view()
                .direct_free_quota_pending_2m
                == pre.thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_2m
            &&& post.thread_map.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_2m
                == pre.thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_2m
            &&& post.thread_map.spec_index(thread_ptr).view()
                .direct_free_quota_pending_1g
                == pre.thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_1g
            &&& post.thread_map.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_1g
                == pre.thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_1g
            &&& post.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
                == pre.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
            &&& post.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == pre.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
            &&& post.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == pre.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
        }
}

pub proof fn thread_endpoint_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_thread_wf(pre.container_map, pre.thread_map),
        thread_endpoint_memory_management_fields_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(thread_pages_wf(post.thread_map, post.page_array)) by {
        reveal(thread_pages_wf);
    };
    assert(endpoint_pages_wf(post.endpoint_map, post.page_array)) by {
        reveal(endpoint_pages_wf);
    };
    assert(thread_staged_pages_wf(post.thread_map, post.page_array)) by {
        thread_staged_pages_4k_wf_preserved_for_eq(
            pre.thread_map,
            post.thread_map,
            pre.page_array,
            post.page_array,
        );
        thread_staged_pages_2m_wf_preserved_for_eq(
            pre.thread_map,
            post.thread_map,
            pre.page_array,
            post.page_array,
        );
        thread_staged_pages_1g_wf_preserved_for_eq(
            pre.thread_map,
            post.thread_map,
            pre.page_array,
            post.page_array,
        );
    };
    assert(container_process_allocator_quota_wf(
        post.container_map,
        post.process_map,
        post.thread_map,
        post.allocator_4k_map,
        post.allocator_2m_map,
        post.allocator_1g_map,
    )) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
            post.container_map,
            post.process_map,
            pre.thread_map,
            post.thread_map,
            post.allocator_4k_map,
        );
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
            post.container_map,
            post.process_map,
            pre.thread_map,
            post.thread_map,
            post.allocator_2m_map,
        );
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
            post.container_map,
            post.process_map,
            pre.thread_map,
            post.thread_map,
            post.allocator_1g_map,
        );
    };
}

}

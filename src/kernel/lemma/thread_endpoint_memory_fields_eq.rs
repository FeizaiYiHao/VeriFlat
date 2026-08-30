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
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.pg_arr == pre.pg_arr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.prc_mp == pre.prc_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.thr_mp.dom() =~= pre.thr_mp.dom()
    &&& post.ep_mp.dom() =~= pre.ep_mp.dom()
    &&& forall|thread_ptr: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(thread_ptr)]
        #![trigger post.thr_mp.spec_index(thread_ptr)]
        pre.thr_mp.dom().contains(thread_ptr) ==>
        {
            &&& thread_effective_quota_4k(
                post.thr_mp.spec_index(thread_ptr),
            ) == thread_effective_quota_4k(
                pre.thr_mp.spec_index(thread_ptr),
            )
            &&& thread_effective_quota_2m(
                post.thr_mp.spec_index(thread_ptr),
            ) == thread_effective_quota_2m(
                pre.thr_mp.spec_index(thread_ptr),
            )
            &&& thread_effective_quota_1g(
                post.thr_mp.spec_index(thread_ptr),
            ) == thread_effective_quota_1g(
                pre.thr_mp.spec_index(thread_ptr),
            )
            &&& post.thr_mp.spec_index(thread_ptr).view()
                .direct_free_quota_pending_4k
                == pre.thr_mp.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_4k
            &&& post.thr_mp.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_4k
                == pre.thr_mp.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_4k
            &&& post.thr_mp.spec_index(thread_ptr).view()
                .direct_free_quota_pending_2m
                == pre.thr_mp.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_2m
            &&& post.thr_mp.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_2m
                == pre.thr_mp.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_2m
            &&& post.thr_mp.spec_index(thread_ptr).view()
                .direct_free_quota_pending_1g
                == pre.thr_mp.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_1g
            &&& post.thr_mp.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_1g
                == pre.thr_mp.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_1g
            &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k
                == pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k
            &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m
            &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g
        }
}

pub proof fn thread_endpoint_no_change_imply_memory_management_inv(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        container_thread_wf(pre.ctn_mp, pre.thr_mp),
        thread_endpoint_memory_management_fields_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_pages_wf);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by {
        reveal(endpoint_pages_wf);
    };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        thread_staged_pages_4k_wf_preserved_for_eq(
            pre.thr_mp,
            post.thr_mp,
            pre.pg_arr,
            post.pg_arr,
        );
        thread_staged_pages_2m_wf_preserved_for_eq(
            pre.thr_mp,
            post.thr_mp,
            pre.pg_arr,
            post.pg_arr,
        );
        thread_staged_pages_1g_wf_preserved_for_eq(
            pre.thr_mp,
            post.thr_mp,
            pre.pg_arr,
            post.pg_arr,
        );
    };
    assert(container_process_allocator_quota_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
            post.ctn_mp,
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
            post.allc_4k_mp,
        );
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
            post.ctn_mp,
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
            post.allc_2m_mp,
        );
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
            post.ctn_mp,
            post.prc_mp,
            pre.thr_mp,
            post.thr_mp,
            post.allc_1g_mp,
        );
    };
}

}

use vstd::prelude::*;
use crate::*;

verus! {
/// Releasing page locks and then one pcid-allocator lock, with no other field changed, leaves the projection unchanged.
pub proof fn kernel_page_then_pcid_allocator_unlocks_implies_u_eq(pre: &KernelK, post: &KernelK)
    requires
        post.inv(),
        *post == (KernelK { pg_arr: post.pg_arr, pcid_allc_mp: post.pcid_allc_mp, ..*pre }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&KernelK { pg_arr: post.pg_arr, ..*pre }, post),
    ensures
        kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
    let mid = KernelK { pg_arr: post.pg_arr, ..*pre };
    assert(kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre)) by {
        reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, post);
    };
}
} // verus!

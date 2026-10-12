use vstd::prelude::*;
use crate::*;

verus! {
pub broadcast proof fn kernel_pagetable_nonlock_fields_unchanged_for_equal<const TABLE_TYPE: PTType>(pre: PageTableLockedMapOf<TABLE_TYPE>, post: PageTableLockedMapOf<TABLE_TYPE>)
    requires pre == post,
    ensures #[trigger] kernel_pagetable_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_pagetable_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_pagetable_nonlock_fields_unchanged_transitive<const TABLE_TYPE: PTType>(pre: PageTableLockedMapOf<TABLE_TYPE>, middle: PageTableLockedMapOf<TABLE_TYPE>, post: PageTableLockedMapOf<TABLE_TYPE>)
    requires
        #[trigger] kernel_pagetable_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_pagetable_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_pagetable_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_pagetable_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_cpu_nonlock_fields_unchanged_for_equal(pre: CpuLockedArray, post: CpuLockedArray)
    requires pre == post,
    ensures #[trigger] kernel_cpu_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_cpu_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_cpu_nonlock_fields_unchanged_transitive(pre: CpuLockedArray, middle: CpuLockedArray, post: CpuLockedArray)
    requires
        #[trigger] kernel_cpu_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_cpu_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_cpu_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_cpu_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_process_nonlock_fields_unchanged_for_equal(pre: ProcessLockedMap, post: ProcessLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_process_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_process_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_process_nonlock_fields_unchanged_transitive(pre: ProcessLockedMap, middle: ProcessLockedMap, post: ProcessLockedMap)
    requires
        #[trigger] kernel_process_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_process_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_process_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_process_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_thread_nonlock_fields_unchanged_for_equal(pre: ThreadLockedMap, post: ThreadLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_thread_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_thread_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_thread_nonlock_fields_unchanged_transitive(pre: ThreadLockedMap, middle: ThreadLockedMap, post: ThreadLockedMap)
    requires
        #[trigger] kernel_thread_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_thread_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_thread_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_thread_nonlock_fields_unchanged); }

pub broadcast group group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive {
    kernel_pagetable_nonlock_fields_unchanged_for_equal,
    kernel_pagetable_nonlock_fields_unchanged_transitive,
    kernel_cpu_nonlock_fields_unchanged_for_equal,
    kernel_cpu_nonlock_fields_unchanged_transitive,
    kernel_process_nonlock_fields_unchanged_for_equal,
    kernel_process_nonlock_fields_unchanged_transitive,
    kernel_thread_nonlock_fields_unchanged_for_equal,
    kernel_thread_nonlock_fields_unchanged_transitive,
}

pub broadcast proof fn kernel_endpoint_nonlock_fields_unchanged_for_equal(pre: EndpointLockedMap, post: EndpointLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_endpoint_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_endpoint_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_endpoint_nonlock_fields_unchanged_transitive(pre: EndpointLockedMap, middle: EndpointLockedMap, post: EndpointLockedMap)
    requires
        #[trigger] kernel_endpoint_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_endpoint_nonlock_fields_unchanged(middle, post),
    ensures kernel_endpoint_nonlock_fields_unchanged(pre, post),
{ reveal(kernel_endpoint_nonlock_fields_unchanged); }

pub broadcast group group_kernel_endpoint_nonlock_fields_unchanged_transitive {
    kernel_endpoint_nonlock_fields_unchanged_for_equal,
    kernel_endpoint_nonlock_fields_unchanged_transitive,
}

pub proof fn kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(steps: &KernelSteps, krnl: &KernelK)
    requires steps.snapshot_k() == *krnl,
    ensures kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl), kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp), kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
{
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
}

pub broadcast proof fn kernel_cpu_process_thread_nonlock_fields_unchanged_transitive(pre: &KernelK, middle: &KernelK, post: &KernelK)
    requires
        #[trigger] kernel_cpu_process_thread_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_cpu_process_thread_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
{ broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); }

pub broadcast proof fn kernel_container_nonlock_fields_and_quotas_unchanged_transitive(pre: &KernelK, middle: &KernelK, post: &KernelK)
    requires
        #[trigger] kernel_container_nonlock_fields_and_quotas_unchanged(pre, middle),
        #[trigger] kernel_container_nonlock_fields_and_quotas_unchanged(middle, post),
    ensures
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
{ reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }
} // verus!

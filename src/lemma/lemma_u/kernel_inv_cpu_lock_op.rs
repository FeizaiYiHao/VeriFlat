use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// CPU lock operations preserve every CPU payload.  Kernel invariants that
/// mention `cpu_array` read those payloads, never the current lock owner.
pub proof fn kernel_inv_preserved_for_cpu_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.inv(),
        cpu_array_wf(
            post.cpu_array,
            post.default_pagetable.view(),
        ),
        post.cpu_array.payloads_unchanged(&pre.cpu_array),
        post.pagetable_map == pre.pagetable_map,
        post.iommu_table_map == pre.iommu_table_map,
        post.iommu_root_table == pre.iommu_root_table,
        post.page_array == pre.page_array,
        post.cpu_tlb == pre.cpu_tlb,
        post.iommu_tlb == pre.iommu_tlb,
        post.root_container == pre.root_container,
        post.container_map == pre.container_map,
        post.scheduler_map == pre.scheduler_map,
        post.pcid_allocator_map == pre.pcid_allocator_map,
        post.process_map == pre.process_map,
        post.thread_map == pre.thread_map,
        post.endpoint_map == pre.endpoint_map,
        post.allocator_4k_map == pre.allocator_4k_map,
        post.allocator_2m_map == pre.allocator_2m_map,
        post.allocator_1g_map == pre.allocator_1g_map,
        post.default_pagetable == pre.default_pagetable,
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.process_management_inv()) by {
        assert(container_cpu_wf(
            post.container_map,
            post.cpu_array,
        )) by {
            reveal(LockedArray::payloads_unchanged);
            reveal(container_perms_wf);
            reveal(container_cpu_wf);
        };
        assert(process_cpu_wf(
            post.process_map,
            post.cpu_array,
        )) by {
            reveal(LockedArray::payloads_unchanged);
            reveal(process_cpu_wf);
        };
        assert(thread_cpu_wf(
            post.thread_map,
            post.cpu_array,
        )) by {
            reveal(LockedArray::payloads_unchanged);
            reveal(thread_cpu_wf);
        };
    };
    assert(cpu_dirty_map_wf(
        post.container_map,
        post.process_map,
        post.cpu_array,
        post.cpu_tlb,
        post.pagetable_map,
    )) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(cpu_dirty_map_contains_container_processes);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
    assert(tlb_wf_spec(
        post.cpu_tlb,
        post.pagetable_map,
        post.cpu_array,
    )) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(tlb_wf_spec);
    };
    assert(post.inv()) by {
        reveal(KernelK::inv);
    };
}

}

use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

#[verifier::opaque]
pub open spec fn scheduler_invariant_fields_unchanged(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|s_ptr: RwLockSchedulerPtr|
        #![trigger post.spec_index(s_ptr)]
        pre.dom().contains(s_ptr) ==>
            post.spec_index(s_ptr).view()
                == pre.spec_index(s_ptr).view()
}

pub proof fn scheduler_lock_op_preserves_invariant_fields(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
    changed: RwLockSchedulerPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
    ensures
        scheduler_invariant_fields_unchanged(pre, post),
{
    reveal(scheduler_invariant_fields_unchanged);
}

pub proof fn kernel_inv_preserved_for_scheduler_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.inv(),
        scheduler_perms_wf(post.scheduler_map),
        scheduler_invariant_fields_unchanged(
            pre.scheduler_map,
            post.scheduler_map,
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
        assert(container_scheduler_wf(
            post.container_map,
            post.scheduler_map,
        )) by {
            reveal(scheduler_invariant_fields_unchanged);
            reveal(container_scheduler_wf);
        };
        assert(container_thread_scheduler_wf(
            post.container_map,
            post.thread_map,
            post.scheduler_map,
        )) by {
            reveal(scheduler_invariant_fields_unchanged);
            reveal(container_thread_wf);
            reveal(container_scheduler_wf);
            reveal(container_thread_scheduler_wf);
        };
    };
    assert(post.inv()) by {
        reveal(KernelK::inv);
    };
}

}

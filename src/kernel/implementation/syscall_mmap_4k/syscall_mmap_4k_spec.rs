use vstd::prelude::*;
use crate::*;

verus! {

/// User-visible and physical result of a successful anonymous 4K mmap.
pub open spec fn mmap_4k_syscall_range_mapped(
    pagetable: PageTable<PT_TYPE>,
    va: VAddr,
    len: usize,
) -> bool {
    forall|i: usize|
        #![trigger pagetable.mapping_4k().dom().contains(
            spec_va_add_range(va, i),
        )]
        i < len ==> {
            let mapped_va = spec_va_add_range(va, i);
            &&& pagetable.mapping_4k().dom().contains(mapped_va)
            &&& pagetable.mapping_4k().spec_index(mapped_va).present
            &&& pagetable.mapping_4k().spec_index(mapped_va).write
            &&& !pagetable.mapping_4k().spec_index(mapped_va).execute_disable
        }
}

/// Exact object-family lock scope held by ordinary mmap.
pub(super) open spec fn mmap_4k_lock_scope(
    kernel: &KernelK,
    lctx: &LocalContext,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    &&& cpu_objects_unlocked_except(
        kernel.cpu_array, lctx.thread_id(), set![cpu_id],
    )
    &&& page_objects_unlocked(kernel.page_array, lctx.thread_id())
    &&& container_objects_unlocked_except(
        kernel.container_map, lctx.thread_id(), set![container_ptr],
    )
    &&& process_objects_unlocked_except(
        kernel.process_map, lctx.thread_id(), set![process_ptr],
    )
    &&& thread_objects_unlocked_except(
        kernel.thread_map, lctx.thread_id(), set![thread_ptr],
    )
    &&& endpoint_objects_unlocked(kernel.endpoint_map, lctx.thread_id())
    &&& pagetable_objects_unlocked_except(
        kernel.pagetable_map, lctx.thread_id(), set![pagetable_ptr],
    )
    &&& iommu_table_objects_unlocked(
        kernel.iommu_table_map, lctx.thread_id(),
    )
    &&& scheduler_objects_unlocked(kernel.scheduler_map, lctx.thread_id())
    &&& pcid_allocator_objects_unlocked(
        kernel.pcid_allocator_map, lctx.thread_id(),
    )
    &&& allocator_objects_unlocked(
        kernel.allocator_4k_map, lctx.thread_id(),
    )
    &&& allocator_objects_unlocked(
        kernel.allocator_2m_map, lctx.thread_id(),
    )
    &&& allocator_objects_unlocked(
        kernel.allocator_1g_map, lctx.thread_id(),
    )
}

} // verus!

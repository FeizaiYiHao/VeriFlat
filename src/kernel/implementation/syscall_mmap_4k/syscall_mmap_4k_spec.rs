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
        #![trigger pagetable.mapping_4k().dom().contains(spec_va_add_range(va, i))]
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
    krnl: &KernelK,
    lctx: &LocalContext,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    &&& cpu_objects_unlocked_except(krnl.cpu_arr, lctx.thread_id(), set![cpu_id])
    &&& page_objects_unlocked(krnl.pg_arr, lctx.thread_id())
    &&& container_objects_unlocked_except(krnl.ctn_mp, lctx.thread_id(), set![container_ptr])
    &&& process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![process_ptr])
    &&& thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![thread_ptr])
    &&& endpoint_objects_unlocked(krnl.ep_mp, lctx.thread_id())
    &&& pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![pagetable_ptr])
    &&& iommu_table_objects_unlocked(krnl.it_mp, lctx.thread_id())
    &&& scheduler_objects_unlocked(krnl.sched_mp, lctx.thread_id())
    &&& pcid_allocator_objects_unlocked(krnl.pcid_allc_mp, lctx.thread_id())
    &&& allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())
    &&& allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id())
    &&& allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id())
}

} // verus!

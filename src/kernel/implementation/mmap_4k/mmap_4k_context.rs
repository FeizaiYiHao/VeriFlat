use vstd::prelude::*;

use crate::*;

verus! {

/// No page object is present in this thread's held-lock ledger.
pub(super) open spec fn mmap_4k_no_page_locks(lctx: &LocalContext) -> bool {
    forall|lock_id: LockId, page_index: PageIndex|
        #![trigger lctx.lock_id_set().contains((lock_id, KernelObjId::Page(page_index)))]
        !lctx.lock_id_set().contains((lock_id, KernelObjId::Page(page_index)))
}

/// Direct physical lock footprint while mmap keeps its five owner locks.
/// This remains separate from the LocalContext ledger so callers never need
/// empty-set/alignment reasoning to recover negative lock-state facts.
pub(super) open spec fn mmap_4k_other_objects_unlocked(
    kernel: &KernelK,
    thread_id: LockThreadId,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    &&& forall|c: CpuId|
        #![trigger kernel.cpu_array.spec_index(c).view()]
        index_valid(NUM_CPUS, c) && c != cpu_id
        ==> !kernel.cpu_array.spec_index(c).view().locked_by_thread(thread_id)
    &&& forall|c: RwLockContainerPtr|
        #![trigger kernel.container_map.dom().contains(c)]
        kernel.container_map.dom().contains(c) && c != container_ptr
        ==> !kernel.container_map.spec_index(c).locked_by_thread(thread_id)
    &&& forall|p: RwLockProcessPtr|
        #![trigger kernel.process_map.dom().contains(p)]
        kernel.process_map.dom().contains(p) && p != process_ptr
        ==> !kernel.process_map.spec_index(p).locked_by_thread(thread_id)
    &&& forall|t: RwLockThreadPtr|
        #![trigger kernel.thread_map.spec_index(t)]
        kernel.thread_map.dom().contains(t) && t != thread_ptr
        ==> !kernel.thread_map.spec_index(t).locked_by_thread(thread_id)
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger kernel.pagetable_map.spec_index(pt).locked_by_thread(thread_id)]
        kernel.pagetable_map.dom().contains(pt) && pt != pagetable_ptr
        ==> !kernel.pagetable_map.spec_index(pt).locked_by_thread(thread_id)
    &&& endpoint_objects_unlocked(kernel.endpoint_map, thread_id)
    &&& iommu_table_objects_unlocked(kernel.iommu_table_map, thread_id)
    &&& scheduler_objects_unlocked(kernel.scheduler_map, thread_id)
    &&& pcid_allocator_objects_unlocked(kernel.pcid_allocator_map, thread_id)
    &&& allocator_objects_unlocked(kernel.allocator_4k_map, thread_id)
    &&& allocator_objects_unlocked(kernel.allocator_2m_map, thread_id)
    &&& allocator_objects_unlocked(kernel.allocator_1g_map, thread_id)
}

/// State shared by every internal mmap operation while the syscall keeps its
/// allocator, owner-thread, and target-page-table locks.  Keeping this as one
/// open subsystem predicate avoids repeating the same lock/object relations in
/// every helper contract and loop invariant; callers can still use each fact
/// directly without a reveal.
pub(super) open spec fn mmap_4k_held_context(
    kernel: &KernelK,
    lctx: &LocalContext,
    alloc_ptr_4k: RwLockPageAllocatorPtr,
    thread_ptr: RwLockThreadPtr,
    process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr,
    cpu_id: CpuId,
    pagetable_ptr: RwLockPageTableRoot,
    thread_lock_perm: &LockPerm,
    pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& kernel.inv()
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& lock_id_aligned(kernel, lctx)
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& kernel.cpu_array.spec_index(cpu_id).view().wlocked_by(lctx)
    &&& kernel.cpu_array.spec_index(cpu_id).view().locked_by(lctx)
    &&& kernel.container_map.dom().contains(container_ptr)
    &&& kernel.container_map.spec_index(container_ptr).wlocked_by(lctx)
    &&& kernel.container_map.spec_index(container_ptr).locked_by(lctx)
    &&& kernel.container_map.spec_index(container_ptr).view_rodata().view()
        .allocator_ptr_4k == alloc_ptr_4k
    &&& kernel.process_map.dom().contains(process_ptr)
    &&& kernel.process_map.spec_index(process_ptr).wlocked_by(lctx)
    &&& kernel.process_map.spec_index(process_ptr).locked_by(lctx)
    &&& kernel.process_map.spec_index(process_ptr).view_rodata().view()
        .owning_container == container_ptr
    &&& kernel.thread_map.dom().contains(thread_ptr)
    &&& kernel.thread_map.spec_index(thread_ptr).wlocked_by(lctx)
    &&& kernel.thread_map.spec_index(thread_ptr).locked_by(lctx)
    &&& kernel.thread_map.spec_index(thread_ptr).being_killed() == false
    &&& kernel.thread_map.spec_index(thread_ptr).view().owning_proc
        == process_ptr
    &&& kernel.thread_map.spec_index(thread_ptr).view().owning_container
        == container_ptr
    &&& kernel.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
        == pagetable_ptr
    &&& thread_lock_perm.state() is WriteLock
    &&& thread_lock_perm.thread_id() == lctx.thread_id()
    &&& thread_lock_perm.lock_id()
        == kernel.thread_map.spec_index(thread_ptr)
            .locking_thread()->Write_lock_id
    &&& kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)
    &&& kernel.pagetable_map.dom().contains(pagetable_ptr)
    &&& kernel.pagetable_map.spec_index(pagetable_ptr).wlocked_by(lctx)
    &&& kernel.pagetable_map.spec_index(pagetable_ptr).locked_by(lctx)
    &&& mmap_4k_other_objects_unlocked(
        kernel, lctx.thread_id(), cpu_id, container_ptr, process_ptr,
        thread_ptr, pagetable_ptr)
    &&& pagetable_lock_perm.state() is WriteLock
    &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& pagetable_lock_perm.lock_id()
        == kernel.pagetable_map.spec_index(pagetable_ptr)
            .locking_thread()->Write_lock_id
    &&& lctx.stable_lock_obj_contains(KernelObjId::Container(container_ptr))
    &&& lctx.stable_lock_obj_contains(KernelObjId::Process(process_ptr))
    &&& lctx.lock_entry_contains_for(
        thread_lock_perm.ordering_lock_id(),
        KernelObjId::Thread(thread_ptr),
        STABLE_LOCK_ID,
    )
    &&& lctx.lock_entry_contains_for(
        pagetable_lock_perm.ordering_lock_id(),
        KernelObjId::PageTable(pagetable_ptr),
        STABLE_LOCK_ID,
    )
    &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
    &&& lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
}

/// Preconditions shared by the two primitives that consume a staged 4K page:
/// publishing it as a leaf and installing it as a page-table directory page.
pub open spec fn staged_4k_page_op_requires(
    kernel: &KernelK,
    lctx: &LocalContext,
    page_ptr: PagePtr,
    thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot,
    va: VAddr,
    page_lock_perm: &LockPerm,
    thread_lock_perm: &LockPerm,
    pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& kernel.inv()
    &&& lock_id_aligned(kernel, lctx)
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& page_ptr_valid(page_ptr)
    &&& va_4k_valid(va)
    &&& kernel.thread_map.dom().contains(thread_ptr)
    &&& kernel.thread_map.spec_index(thread_ptr).being_killed() == false
    &&& kernel.pagetable_map.dom().contains(pagetable_ptr)
    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_va2index(va).0 && pei_valid(spec_va2index(va).0)
    &&& pei_valid(spec_va2index(va).1)
    &&& pei_valid(spec_va2index(va).2)
    &&& kernel.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
        == (PageState::Owned4k { thread_ptr })
    &&& kernel.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .owning_container
        == kernel.thread_map.spec_index(thread_ptr).view().owning_container
    &&& kernel.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
        == pagetable_ptr
    &&& kernel.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
        .contains(page_ptr)
    &&& kernel.thread_map.spec_index(thread_ptr).view().quota_4k >= 1
    &&& kernel.page_array.spec_index(page_ptr2page_index(page_ptr)).view()
        .wlocked_by(lctx)
    &&& page_lock_perm.state() is WriteLock
    &&& page_lock_perm.thread_id() == lctx.thread_id()
    &&& page_lock_perm.lock_id()
        == kernel.page_array.spec_index(page_ptr2page_index(page_ptr)).view()
            .locking_thread()->Write_lock_id
    &&& kernel.thread_map.spec_index(thread_ptr).wlocked_by(lctx)
    &&& thread_lock_perm.state() is WriteLock
    &&& thread_lock_perm.thread_id() == lctx.thread_id()
    &&& thread_lock_perm.lock_id()
        == kernel.thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id
    &&& kernel.pagetable_map.spec_index(pagetable_ptr).wlocked_by(lctx)
    &&& pagetable_lock_perm.state() is WriteLock
    &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& pagetable_lock_perm.lock_id()
        == kernel.pagetable_map.spec_index(pagetable_ptr)
            .locking_thread()->Write_lock_id
}

/// State transition shared by staged-page consumers. Page state, mappings,
/// and the visible PageTable change remain operation-specific.
pub open spec fn staged_4k_page_op_ensures(
    post: &KernelK,
    post_lctx: &LocalContext,
    pre: &KernelK,
    pre_lctx: &LocalContext,
    page_ptr: PagePtr,
    thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot,
    page_lock_perm: &LockPerm,
    thread_lock_perm: &LockPerm,
    pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& post.inv()
    &&& lock_id_aligned(post, post_lctx)
    &&& post_lctx.kernel_view_locking_state() is Release
    &&& post_lctx.thread_id() == pre_lctx.thread_id()
    &&& post_lctx.lock_id_set()
        == pre_lctx.lock_id_set()
            .remove((
                pre.page_array.lock_id_by_index(page_ptr2page_index(page_ptr)),
                KernelObjId::Page(page_ptr2page_index(page_ptr)),
            ))
            .insert((
                post.page_array.lock_id_by_index(page_ptr2page_index(page_ptr)),
                KernelObjId::Page(page_ptr2page_index(page_ptr)),
            ))
    &&& post_lctx.stable_lock_id_set() == pre_lctx.stable_lock_id_set()
    &&& post.page_array.spec_index(page_ptr2page_index(page_ptr)).view()
        .wlocked_by(post_lctx)
    &&& post.thread_map.spec_index(thread_ptr).wlocked_by(post_lctx)
    &&& post.pagetable_map.spec_index(pagetable_ptr).wlocked_by(post_lctx)
    &&& page_lock_perm.lock_id()
        == post.page_array.spec_index(page_ptr2page_index(page_ptr)).view()
            .locking_thread()->Write_lock_id
    &&& thread_lock_perm.lock_id()
        == post.thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id
    &&& pagetable_lock_perm.lock_id()
        == post.pagetable_map.spec_index(pagetable_ptr)
            .locking_thread()->Write_lock_id
    &&& post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .perm_4k.view().is_none()
    &&& post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .owning_container
        == pre.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .owning_container
    &&& post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .is_io_page
        == pre.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_io_page
    &&& post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .free_list_node_storage
        == pre.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .free_list_node_storage
    &&& post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .free_list
        == pre.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .free_list
    &&& post.thread_map.spec_index(thread_ptr).being_killed() == false
    &&& post.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
        == pre.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
            .remove(page_ptr)
    &&& post.thread_map.spec_index(thread_ptr).view().quota_4k
        == pre.thread_map.spec_index(thread_ptr).view().quota_4k - 1
    &&& post.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m.view()
        == pre.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m.view()
    &&& post.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g.view()
        == pre.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g.view()
    &&& post.thread_map.spec_index(thread_ptr).view().quota_2m
        == pre.thread_map.spec_index(thread_ptr).view().quota_2m
    &&& post.thread_map.spec_index(thread_ptr).view().quota_1g
        == pre.thread_map.spec_index(thread_ptr).view().quota_1g
    &&& post.thread_map.spec_index(thread_ptr).view()
        .free_quota_pending_fields_equal(
            &pre.thread_map.spec_index(thread_ptr).view(),
        )
    &&& post.thread_map.spec_index(thread_ptr).view().state
        == pre.thread_map.spec_index(thread_ptr).view().state
    &&& post.thread_map.spec_index(thread_ptr).view().owning_container
        == pre.thread_map.spec_index(thread_ptr).view().owning_container
    &&& post.thread_map.spec_index(thread_ptr).view().owning_proc
        == pre.thread_map.spec_index(thread_ptr).view().owning_proc
    &&& post.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
        == pre.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
    &&& post.thread_map.spec_index(thread_ptr).view().blocking_endpoint_index
        == pre.thread_map.spec_index(thread_ptr).view().blocking_endpoint_index
    &&& post.thread_map.spec_index(thread_ptr).view().ipc_payload
        == pre.thread_map.spec_index(thread_ptr).view().ipc_payload
    &&& post.thread_map.spec_index(thread_ptr).view().error_code
        == pre.thread_map.spec_index(thread_ptr).view().error_code
    &&& post.thread_map.spec_index(thread_ptr).view().trap_frame
        == pre.thread_map.spec_index(thread_ptr).view().trap_frame
    &&& post.pagetable_map.spec_index(pagetable_ptr).view().kernel_entries
        =~= pre.pagetable_map.spec_index(pagetable_ptr).view().kernel_entries
    &&& post.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
        == pre.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
    &&& post.pagetable_map.spec_index(pagetable_ptr).view().pcid
        == pre.pagetable_map.spec_index(pagetable_ptr).view().pcid
    &&& post.pagetable_map.spec_index(pagetable_ptr).view().cr3
        == pre.pagetable_map.spec_index(pagetable_ptr).view().cr3
    &&& post.pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
        == pre.pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
    &&& post.pagetable_map.unchanged_except(&pre.pagetable_map, pagetable_ptr)
    &&& post.page_array.entries_unchanged_except(
        &pre.page_array, page_ptr2page_index(page_ptr),
    )
    &&& post.thread_map.unchanged_except(&pre.thread_map, thread_ptr)
    &&& post.iommu_table_map == pre.iommu_table_map
    &&& post.iommu_root_table == pre.iommu_root_table
    &&& post.cpu_array == pre.cpu_array
    &&& post.container_map == pre.container_map
    &&& post.scheduler_map == pre.scheduler_map
    &&& post.pcid_allocator_map == pre.pcid_allocator_map
    &&& post.process_map == pre.process_map
    &&& post.endpoint_map == pre.endpoint_map
    &&& post.allocator_4k_map == pre.allocator_4k_map
    &&& post.allocator_2m_map == pre.allocator_2m_map
    &&& post.allocator_1g_map == pre.allocator_1g_map
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.root_container == pre.root_container
    &&& post.default_pagetable == pre.default_pagetable
}

} // verus!

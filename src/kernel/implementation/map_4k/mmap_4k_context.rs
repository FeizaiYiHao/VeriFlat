use vstd::prelude::*;

use crate::*;

verus! {

/// No page object is present in this thread's held-lock ledger.
pub open spec fn mmap_4k_no_page_locks(lctx: &LocalContext) -> bool {
    lctx.page_lock_map().dom().is_empty()
}

/// The owner-lock context is ready to enter the 4K allocator only when no
/// page or allocator locks are held and every held owner lock orders below it.
pub open spec fn mmap_4k_allocation_ready(
    krnl: &KernelK,
    lctx: &LocalContext,
) -> bool {
    &&& mmap_4k_no_page_locks(lctx)
    &&& page_objects_unlocked(krnl.pg_arr, lctx.thread_id())
    &&& allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())
    &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
    &&& lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
}

/// State shared by 4K directory construction.  The locked allocation thread
/// is the stable owner root; its process and container do not need separate
/// locks.  Extra endpoint/thread/page-table locks are permitted so IPC can use
/// the same builder after discovering a blocked peer.
pub open spec fn mmap_4k_held_context(
    krnl: &KernelK,
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
    &&& krnl.inv()
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& typed_lock_maps_aligned(krnl, lctx)
    &&& lock_id_set_aligned(lctx)
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(lctx)
    &&& krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == false
    &&& krnl.ctn_mp.dom().contains(container_ptr)
    &&& krnl.ctn_mp.spec_index(container_ptr).view_rodata().view()
        .allocator_ptr_4k == alloc_ptr_4k
    &&& krnl.prc_mp.dom().contains(process_ptr)
    &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view()
        .owning_container == container_ptr
    &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view()
        .pagetable == pagetable_ptr
    &&& krnl.thr_mp.dom().contains(thread_ptr)
    &&& krnl.thr_mp.spec_index(thread_ptr).wlocked_by(lctx)
    &&& krnl.thr_mp.spec_index(thread_ptr).being_killed() == false
    &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_container
        == container_ptr
    &&& {
        ||| {
            &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_proc
                == process_ptr
            &&& krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr
        }
        ||| krnl.prc_mp.spec_index(process_ptr).wlocked_by(lctx)
    }
    &&& thread_lock_perm.state() is WriteLock
    &&& thread_lock_perm.thread_id() == lctx.thread_id()
    &&& thread_lock_perm.lock_id()
        == krnl.thr_mp.spec_index(thread_ptr)
            .locking_thread()->Write_lock_id
    &&& krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
    &&& krnl.pt_mp.dom().contains(pagetable_ptr)
    &&& krnl.pt_mp.spec_index(pagetable_ptr).wlocked_by(lctx)
    &&& pagetable_lock_perm.state() is WriteLock
    &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& pagetable_lock_perm.lock_id()
        == krnl.pt_mp.spec_index(pagetable_ptr)
            .locking_thread()->Write_lock_id
}

/// Preconditions shared by the two primitives that consume a staged 4K page:
/// publishing it as a leaf and installing it as a page-table directory page.
pub open spec fn staged_4k_page_op_requires(
    krnl: &KernelK,
    lctx: &LocalContext,
    page_ptr: PagePtr,
    thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot,
    va: VAddr,
    page_lock_perm: &LockPerm,
    thread_lock_perm: &LockPerm,
    pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& krnl.inv()
    &&& typed_lock_maps_aligned(krnl, lctx)
    &&& lock_id_set_aligned(lctx)
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& page_ptr_valid(page_ptr)
    &&& va_4k_valid(va)
    &&& krnl.thr_mp.dom().contains(thread_ptr)
    &&& krnl.thr_mp.spec_index(thread_ptr).being_killed() == false
    &&& krnl.pt_mp.dom().contains(pagetable_ptr)
    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end
        <= spec_va2index(va).0
    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
        == (PageState::Owned4k { thread_ptr })
    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .owning_container
        == krnl.thr_mp.spec_index(thread_ptr).view().owning_container
    &&& krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr
        == pagetable_ptr
    &&& krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
        .contains(page_ptr)
    &&& krnl.thr_mp.spec_index(thread_ptr).view().quota_4k >= 1
    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view()
        .wlocked_by(lctx)
    &&& page_lock_perm.state() is WriteLock
    &&& page_lock_perm.thread_id() == lctx.thread_id()
    &&& page_lock_perm.lock_id()
        == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view()
            .locking_thread()->Write_lock_id
    &&& krnl.thr_mp.spec_index(thread_ptr).wlocked_by(lctx)
    &&& thread_lock_perm.state() is WriteLock
    &&& thread_lock_perm.thread_id() == lctx.thread_id()
    &&& thread_lock_perm.lock_id()
        == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
    &&& krnl.pt_mp.spec_index(pagetable_ptr).wlocked_by(lctx)
    &&& pagetable_lock_perm.state() is WriteLock
    &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& pagetable_lock_perm.lock_id()
        == krnl.pt_mp.spec_index(pagetable_ptr)
            .locking_thread()->Write_lock_id
}

/// Directory-page publication is index-based. Unlike a leaf insertion, it
/// does not need a synthetic representative virtual address.
pub open spec fn staged_4k_page_table_op_requires(
    krnl: &KernelK,
    lctx: &LocalContext,
    page_ptr: PagePtr,
    thread_ptr: RwLockThreadPtr,
    process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index),
    page_lock_perm: &LockPerm,
    thread_lock_perm: &LockPerm,
    pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& krnl.inv()
    &&& typed_lock_maps_aligned(krnl, lctx)
    &&& lock_id_set_aligned(lctx)
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& page_ptr_valid(page_ptr)
    &&& krnl.thr_mp.dom().contains(thread_ptr)
    &&& krnl.thr_mp.spec_index(thread_ptr).being_killed() == false
    &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_container
        == container_ptr
    &&& krnl.prc_mp.dom().contains(process_ptr)
    &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view()
        .owning_container == container_ptr
    &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view()
        .pagetable == pagetable_ptr
    &&& krnl.pt_mp.dom().contains(pagetable_ptr)
    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end
        <= indices.0
    &&& pei_valid(indices.0)
    &&& pei_valid(indices.1)
    &&& pei_valid(indices.2)
    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
        == (PageState::Owned4k { thread_ptr })
    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .owning_container
        == krnl.thr_mp.spec_index(thread_ptr).view().owning_container
    &&& krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
        .contains(page_ptr)
    &&& krnl.thr_mp.spec_index(thread_ptr).view().quota_4k >= 1
    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view()
        .wlocked_by(lctx)
    &&& page_lock_perm.state() is WriteLock
    &&& page_lock_perm.thread_id() == lctx.thread_id()
    &&& page_lock_perm.lock_id()
        == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view()
            .locking_thread()->Write_lock_id
    &&& krnl.thr_mp.spec_index(thread_ptr).wlocked_by(lctx)
    &&& thread_lock_perm.state() is WriteLock
    &&& thread_lock_perm.thread_id() == lctx.thread_id()
    &&& thread_lock_perm.lock_id()
        == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
    &&& krnl.pt_mp.spec_index(pagetable_ptr).wlocked_by(lctx)
    &&& pagetable_lock_perm.state() is WriteLock
    &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& pagetable_lock_perm.lock_id()
        == krnl.pt_mp.spec_index(pagetable_ptr)
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
    &&& typed_lock_maps_aligned(post, post_lctx)
    &&& lock_id_set_aligned(post_lctx)
    &&& typed_lock_maps_inserted(pre_lctx, post_lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
        lock_id: post.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
    })
    &&& post_lctx.kernel_view_locking_state() is Release
    &&& post_lctx.thread_id() == pre_lctx.thread_id()
    &&& post_lctx.lock_id_set()
        == pre_lctx.lock_id_set()
            .remove((pre.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))
            .insert((post.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))
    &&& forall|held: HeldLock|
        #![trigger post_lctx.lock_id_set().contains((held.0, held.1))]
        held.1 != KernelObjId::Page(page_ptr2page_index(page_ptr))
        ==> post_lctx.lock_id_set().contains((held.0, held.1))
            == pre_lctx.lock_id_set().contains((held.0, held.1))
    &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view()
        .wlocked_by(post_lctx)
    &&& post.thr_mp.spec_index(thread_ptr).wlocked_by(post_lctx)
    &&& post.pt_mp.spec_index(pagetable_ptr).wlocked_by(post_lctx)
    &&& post.thr_mp.lock_id_by_key(thread_ptr)
        == pre.thr_mp.lock_id_by_key(thread_ptr)
    &&& post.pt_mp.lock_id_by_key(pagetable_ptr)
        == pre.pt_mp.lock_id_by_key(pagetable_ptr)
    &&& page_lock_perm.lock_id()
        == post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view()
            .locking_thread()->Write_lock_id
    &&& thread_lock_perm.lock_id()
        == post.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
    &&& pagetable_lock_perm.lock_id()
        == post.pt_mp.spec_index(pagetable_ptr)
            .locking_thread()->Write_lock_id
    &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .owning_container
        == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .owning_container
    &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .is_io_page
        == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_io_page
    &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .free_list_node_storage
        == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .free_list_node_storage
    &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
        .free_list
        == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .free_list
    &&& post.thr_mp.spec_index(thread_ptr).being_killed() == false
    &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
        == pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
            .remove(page_ptr)
    &&& post.thr_mp.spec_index(thread_ptr).view().quota_4k
        == pre.thr_mp.spec_index(thread_ptr).view().quota_4k - 1
    &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view()
        == pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view()
    &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g.view()
        == pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g.view()
    &&& post.thr_mp.spec_index(thread_ptr).view().quota_2m
        == pre.thr_mp.spec_index(thread_ptr).view().quota_2m
    &&& post.thr_mp.spec_index(thread_ptr).view().quota_1g
        == pre.thr_mp.spec_index(thread_ptr).view().quota_1g
    &&& post.thr_mp.spec_index(thread_ptr).view()
        .free_quota_pending_fields_equal(&pre.thr_mp.spec_index(thread_ptr).view())
    &&& post.thr_mp.spec_index(thread_ptr).view().state
        == pre.thr_mp.spec_index(thread_ptr).view().state
    &&& post.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr
        == pre.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr
    &&& post.thr_mp.spec_index(thread_ptr).view().caller
        == pre.thr_mp.spec_index(thread_ptr).view().caller
    &&& post.thr_mp.spec_index(thread_ptr).view().callee
        == pre.thr_mp.spec_index(thread_ptr).view().callee
    &&& post.thr_mp.spec_index(thread_ptr).view().owning_container
        == pre.thr_mp.spec_index(thread_ptr).view().owning_container
    &&& post.thr_mp.spec_index(thread_ptr).view().upper_container_seq
        == pre.thr_mp.spec_index(thread_ptr).view().upper_container_seq
    &&& post.thr_mp.spec_index(thread_ptr).view().owning_proc
        == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
    &&& post.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr
        == pre.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr
    &&& post.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_index
        == pre.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_index
    &&& post.thr_mp.spec_index(thread_ptr).view().ipc_payload
        == pre.thr_mp.spec_index(thread_ptr).view().ipc_payload
    &&& post.thr_mp.spec_index(thread_ptr).view().error_code
        == pre.thr_mp.spec_index(thread_ptr).view().error_code
    &&& post.thr_mp.spec_index(thread_ptr).view().trap_frame
        == pre.thr_mp.spec_index(thread_ptr).view().trap_frame
    &&& post.pt_mp.spec_index(pagetable_ptr).view().kernel_entries
        =~= pre.pt_mp.spec_index(pagetable_ptr).view().kernel_entries
    &&& post.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end
        == pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end
    &&& post.pt_mp.spec_index(pagetable_ptr).view().pcid
        == pre.pt_mp.spec_index(pagetable_ptr).view().pcid
    &&& post.pt_mp.spec_index(pagetable_ptr).view().cr3
        == pre.pt_mp.spec_index(pagetable_ptr).view().cr3
    &&& post.pt_mp.spec_index(pagetable_ptr).view().proc_ptr
        == pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page_ptr))
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& post.it_mp == pre.it_mp
    &&& post.irt == pre.irt
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.sched_mp == pre.sched_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.prc_mp == pre.prc_mp
    &&& post.ep_mp == pre.ep_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
}

} // verus!

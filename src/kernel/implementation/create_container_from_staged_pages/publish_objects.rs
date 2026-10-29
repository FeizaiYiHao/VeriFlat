use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn publish_new_container_process_and_pagetable(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr, child_pagetable_ptr: RwLockPageTableRoot,
    l4_page: PagePtr, root_pcid: Pcid, child_depth: usize, process_quota_4k: usize, container_head: PageIndex, pcid_allocator_head: PageIndex,
    Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(process_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>, Tracked(l4_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        process_perms_wf(old(krnl).prc_mp),
        pagetable_perms_wf(old(krnl).pt_mp),
        old(krnl).dflt_pt.view().wf(),
        pei_valid(old(krnl).dflt_pt.view().kernel_l4_end),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, old(lctx).thread_id()),
        old(krnl).prc_mp.typed_lock_map_aligned(old(lctx).process_lock_map(), old(lctx).thread_id()),
        old(krnl).pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pcid_valid(root_pcid),
        root_pcid != KERNEL_DEFAULT_PCID,
        page_ptr_valid(child_process_ptr),
        page_ptr_valid(child_pagetable_ptr),
        page_ptr_valid(l4_page),
        child_process_ptr != child_pagetable_ptr,
        child_process_ptr != l4_page,
        child_pagetable_ptr != l4_page,
        !old(krnl).prc_mp.dom().contains(child_process_ptr),
        !old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(l4_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(child_process_ptr),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(child_pagetable_ptr),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(l4_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(child_process_ptr),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(child_pagetable_ptr),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(l4_page),),
    ensures
        final(krnl).prc_mp.spec_index(child_process_ptr).inv(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).pg_arr.typed_lock_map_aligned(ret.2.view(), final(lctx).thread_id()),
        ret.2.view().dom() == page_locks.dom(),
        forall|index: PageIndex|
            #![trigger ret.2.view().get(index)]
            #![trigger ret.2.view().dom().contains(index)]
            index != page_ptr2page_index(l4_page) && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(child_process_ptr) ==> ret.2.view().get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret.2.view(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.2.view(), page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.2.view(), page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        final(krnl).prc_mp.typed_lock_map_aligned(final(lctx).process_lock_map(), final(lctx).thread_id()),
        final(krnl).pt_mp.typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).prc_mp.perms_wf(),
        process_perms_wf(old(krnl).prc_mp) ==> process_perms_wf(final(krnl).prc_mp),
        final(krnl).pt_mp.perms_wf(),
        pagetable_perms_wf(old(krnl).pt_mp) ==> pagetable_perms_wf(final(krnl).pt_mp),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(child_pagetable_ptr, final(krnl).pt_lower.view().spec_index(child_pagetable_ptr)),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), child_pagetable_ptr).wf(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view_ghost() == final(krnl).pt_lower.view().spec_index(child_pagetable_ptr),
        forall|r: RwLockPageTableRoot|
            #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), r)]
            old(krnl).pt_mp.dom().contains(r) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), r) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), r),
        pagetable_lower_wf(old(krnl).pt_mp, old(krnl).pt_lower.view()) ==> pagetable_lower_wf(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_window_holders_hold_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view()) ==> pagetable_window_holders_hold_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(old(krnl).pt_mp, old(krnl).pt_lower.view())
            ==> pagetable_hidden_leaves_only_when_locked(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(old(krnl).pt_mp, old(krnl).pt_lower.view())
            ==> pagetable_window_stale_cpus_only_when_locked(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_window_typed_lock_map_aligned(old(krnl).pt_mp, old(krnl).pt_lower.view(), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id())
            ==> pagetable_window_typed_lock_map_aligned(final(krnl).pt_mp, final(krnl).pt_lower.view(), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(child_process_ptr) && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(l4_page) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: child_pagetable_ptr, table_type: PT_TYPE } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().owning_container == child_container_ptr,
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom() =~= old(krnl).prc_mp.dom().insert(child_process_ptr),
        forall|ptr: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(ptr)] old(krnl).prc_mp.dom().contains(ptr) ==> final(krnl).prc_mp.spec_index(ptr) == old(krnl).prc_mp.spec_index(ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().container_depth == child_depth,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().parent is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().depth == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().cr3 == l4_page,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().iommu_cr3 is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().iommu_table_ptr is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pcid == root_pcid,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pcid == root_pcid,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().iommu_table is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().owned_pci_functions.view().is_empty(),
        !final(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_4k == process_quota_4k,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().owned_threads.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().parent_linkedlist_node.is_init(),
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().uppertree_seq.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().subtree_set.view().is_empty(),
        final(krnl).pt_mp.dom() =~= old(krnl).pt_mp.dom().insert(child_pagetable_ptr),
        forall|ptr: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(ptr)] old(krnl).pt_mp.dom().contains(ptr) ==> final(krnl).pt_mp.spec_index(ptr) == old(krnl).pt_mp.spec_index(ptr),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), child_pagetable_ptr).is_empty(),
        !final(krnl).pt_mp.spec_index(child_pagetable_ptr).being_killed(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().proc_ptr == child_process_ptr,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().pcid is Some,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().pcid_value() == root_pcid,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().cr3 == l4_page,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end == old(krnl).dflt_pt.view().kernel_l4_end,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), child_pagetable_ptr).page_closure() =~= set![l4_page],
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(child_process_ptr),
        forall|ptr: RwLockProcessPtr| #![trigger final(lctx).process_lock_map().get(ptr)] ptr != child_process_ptr ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(child_pagetable_ptr),
        forall|ptr: RwLockPageTableRoot| #![trigger final(lctx).pagetable_lock_map().get(ptr)] ptr != child_pagetable_ptr ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write,),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.spec_index(child_process_ptr).write_lock_perm_match(&ret.0.view()),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
{
    let process_index = page_ptr2page_index(child_process_ptr);
    let pagetable_index = page_ptr2page_index(child_pagetable_ptr);
    let l4_index = page_ptr2page_index(l4_page);
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert({
            &&& process_index != pagetable_index
            &&& process_index != l4_index
            &&& pagetable_index != l4_index
        });
        assert(krnl.prc_mp.perms_wf() && krnl.pt_mp.perms_wf()) by { process_perms_wf_map(krnl.prc_mp); pagetable_perms_wf_map(krnl.pt_mp); };
    }
    let default_pt = krnl.dflt_pt.borrow();
    let Tracked(l4_page_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, l4_page, Allocated4KPageState::PageTable { pagetable_root: child_pagetable_ptr, table_type: PT_TYPE }, Ghost(page_locks), Tracked(&*lctx), Tracked(l4_page_lock_perm));
    let ghost l4_page_locks = page_locks.insert(l4_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(l4_index), mode: TypedLockMode::Write });
    let (l4_ptr, Tracked(mut l4_perm)) = page_perm_to_page_map(l4_page, Tracked(l4_page_perm));
    default_pt.copy_kernel_entries_to_unpublished_root(l4_ptr, Tracked(&mut l4_perm));
    proof { assert(default_pt.kernel_entries.view().len() == default_pt.kernel_l4_end) by { default_pt.kernel_entries_wf_len_at(); }; }
    let pagetable_higher = PageTableHigher::<PT_TYPE>::new(Some(root_pcid), Ghost(default_pt.kernel_entries.view()), l4_ptr, Tracked(l4_perm), default_pt.kernel_l4_end, child_process_ptr);
    let tracked pagetable_lower = PageTableLower::<PT_TYPE>::tracked_empty(pagetable_higher);
    let Tracked(pagetable_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, child_pagetable_ptr, Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE }, Ghost(l4_page_locks), Tracked(&*lctx), Tracked(pagetable_page_lock_perm));
    let ghost pagetable_page_locks = l4_page_locks.insert(pagetable_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pagetable_index), mode: TypedLockMode::Write });
    let Tracked(child_pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(child_pagetable_ptr, pagetable_higher, Tracked(pagetable_lower), Tracked(pagetable_perm), Tracked(&mut *lctx));
    let mut process_value = Process::new_fresh(child_process_ptr, root_pcid, child_pagetable_ptr, child_depth, 0);
    process_value.quota_4k = process_quota_4k;
    let process_rodata = ReadOnlyNode::new(
        ProcessRO {
            owning_container: child_container_ptr, container_depth: child_depth, parent: None, depth: 0, pagetable: child_pagetable_ptr,
            cr3: l4_ptr, iommu_cr3: None, iommu_table_ptr: None, pcid: root_pcid,
        },
        Ghost(child_process_ptr),
    );
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(Seq::empty()), subtree_set: Ghost(Set::empty()), owned_pci_functions: Ghost(Set::empty()) };
    let Tracked(process_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, child_process_ptr, Allocated4KPageState::AsProcess, Ghost(pagetable_page_locks), Tracked(&*lctx), Tracked(process_page_lock_perm));
    let ghost process_page_locks = pagetable_page_locks.insert(process_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(process_index), mode: TypedLockMode::Write });
    let Tracked(child_process_lock_perm) =
        krnl.retype_page_to_process_and_insert(child_process_ptr, process_value, process_rodata, process_ghost, Tracked(process_perm), Tracked(&mut *lctx),);
    (Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Ghost(process_page_locks))
}

pub(super) fn publish_new_container_allocator<const SIZE: usize>(
    pages: &mut PageLockedArray, allocator_map: &mut PageAllocatorUnLockedMap<SIZE>, child_container_ptr: RwLockContainerPtr, allocator_page: PagePtr,
    allocator_state: Allocated4KPageState, allocator_value: PageAllocator<SIZE>, Ghost(quota_lock_map): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
    Ghost(cache_lock_map): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
    Ghost(global_pool_lock_map): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(allocator_page_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(allocator_map).perms_wf(),
        old(pages).typed_lock_map_aligned(page_locks, lctx.thread_id()),
        old(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        old(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        old(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        allocator_value.inv(),
        allocator_state is As4KAllocator || allocator_state is As2MAllocator || allocator_state is As1GAllocator,
        !allocator_value.quota.locked(),
        !allocator_value.global_pool.locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked()]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked_by_thread(lctx.thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().rlocked_by_thread(lctx.thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_value.cpu_caches.spec_index(cpu_id).view().locked(),
        !old(allocator_map).dom().contains(allocator_page),
        page_ptr_valid(allocator_page),
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_page), TypedLockMode::Write),
        allocator_page_lock_perm.state() is WriteLock,
        allocator_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(allocator_page),).view().locking_thread()->Write_lock_id,
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(allocator_map).perms_wf(),
        allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*final(allocator_map)),
        final(pages).typed_lock_map_aligned(page_locks.insert(page_ptr2page_index(allocator_page), TypedHeldLock { lock_id: final(pages).lock_id_by_index(page_ptr2page_index(allocator_page)), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        final(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        final(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(allocator_page),),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        final(pages).spec_index(page_ptr2page_index(allocator_page)).view().view().state == (PageState::Allocated4k { state: allocator_state }),
        final(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().owning_container == child_container_ptr,
        allocator_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(allocator_page),).view().locking_thread()->Write_lock_id,
        final(allocator_map).dom() =~= old(allocator_map).dom().insert(allocator_page),
        final(allocator_map).spec_index(allocator_page) == allocator_value,
        forall|ptr: RwLockPageAllocatorPtr| #![trigger final(allocator_map).spec_index(ptr)] old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
{
    let Tracked(allocator_perm) =
        page_array_retype_owned_4k_for_container(pages, child_container_ptr, allocator_page, allocator_state, Ghost(page_locks), Tracked(lctx), Tracked(allocator_page_lock_perm));
    page_allocator_map_insert_new(allocator_map, allocator_page, allocator_value, Ghost(quota_lock_map), Ghost(cache_lock_map), Ghost(global_pool_lock_map), Tracked(lctx), Tracked(allocator_perm));
}

pub(super) fn publish_new_container_allocators(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    allocator_4k_value: PageAllocator<ALLOCATOR_SIZE_4K>, allocator_2m_value: PageAllocator<ALLOCATOR_SIZE_2M>, allocator_1g_value: PageAllocator<ALLOCATOR_SIZE_1G>, container_head: PageIndex,
    pcid_allocator_head: PageIndex, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: Ghost<Map<PageIndex, TypedHeldLock>>)
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        allocator_perms_wf(old(krnl).allc_4k_mp),
        allocator_perms_wf(old(krnl).allc_2m_mp),
        allocator_perms_wf(old(krnl).allc_1g_mp),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, lctx.thread_id()),
        old(krnl).allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id()),
        old(krnl).allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id()),
        old(krnl).allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id()),
        old(krnl).allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id()),
        old(krnl).allc_2m_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id()),
        old(krnl).allc_2m_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id()),
        old(krnl).allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id()),
        old(krnl).allc_1g_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_1g_lock_map(), lctx.thread_id()),
        old(krnl).allc_1g_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        allocator_4k_value.inv(),
        allocator_2m_value.inv(),
        allocator_1g_value.inv(),
        !allocator_4k_value.quota.locked(),
        !allocator_2m_value.quota.locked(),
        !allocator_1g_value.quota.locked(),
        !allocator_4k_value.global_pool.locked(),
        !allocator_2m_value.global_pool.locked(),
        !allocator_1g_value.global_pool.locked(),
        forall|cpu_id: CpuId| #![trigger allocator_4k_value.cpu_caches.spec_index(cpu_id).view().locked()] index_valid(NUM_CPUS, cpu_id) ==> !allocator_4k_value.cpu_caches.spec_index(cpu_id).view().locked(),
        forall|cpu_id: CpuId| #![trigger allocator_2m_value.cpu_caches.spec_index(cpu_id).view().locked()] index_valid(NUM_CPUS, cpu_id) ==> !allocator_2m_value.cpu_caches.spec_index(cpu_id).view().locked(),
        forall|cpu_id: CpuId| #![trigger allocator_1g_value.cpu_caches.spec_index(cpu_id).view().locked()] index_valid(NUM_CPUS, cpu_id) ==> !allocator_1g_value.cpu_caches.spec_index(cpu_id).view().locked(),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr2page_index(allocator_4k_page) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(allocator_4k_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(allocator_2m_page) != page_ptr2page_index(allocator_1g_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_2m_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_1g_page_lock_perm.thread_id() == lctx.thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, lctx, pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(allocator_4k_page),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(allocator_2m_page),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(allocator_1g_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(allocator_4k_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(allocator_2m_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(allocator_1g_page),),
    ensures
        final(krnl).pg_arr.typed_lock_map_aligned(ret.view(), lctx.thread_id()),
        ret.view().dom() == page_locks.dom(),
        forall|index: PageIndex|
            #![trigger ret.view().get(index)]
            #![trigger ret.view().dom().contains(index)]
            index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page) && index != page_ptr2page_index(allocator_1g_page) ==> ret.view().get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret.view(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.view(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(ret.view(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        final(krnl).allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id()),
        final(krnl).allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id()),
        final(krnl).allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id()),
        final(krnl).allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id()),
        final(krnl).allc_2m_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id()),
        final(krnl).allc_2m_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id()),
        final(krnl).allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id()),
        final(krnl).allc_1g_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_1g_lock_map(), lctx.thread_id()),
        final(krnl).allc_1g_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_1g_mp.perms_wf(),
        allocator_perms_wf(final(krnl).allc_4k_mp),
        allocator_perms_wf(final(krnl).allc_2m_mp),
        allocator_perms_wf(final(krnl).allc_1g_mp),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page) && index != page_ptr2page_index(allocator_1g_page) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        forall|index: PageIndex|
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index) && old(krnl).pg_arr.spec_index(index).view().view().state is Merged2m ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().owning_container == child_container_ptr,
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        final(krnl).allc_4k_mp.dom() =~= old(krnl).allc_4k_mp.dom().insert(allocator_4k_page),
        final(krnl).allc_2m_mp.dom() =~= old(krnl).allc_2m_mp.dom().insert(allocator_2m_page),
        final(krnl).allc_1g_mp.dom() =~= old(krnl).allc_1g_mp.dom().insert(allocator_1g_page),
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page) == allocator_4k_value,
        final(krnl).allc_2m_mp.spec_index(allocator_2m_page) == allocator_2m_value,
        final(krnl).allc_1g_mp.spec_index(allocator_1g_page) == allocator_1g_value,
        forall|ptr: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(ptr)] old(krnl).allc_4k_mp.dom().contains(ptr) ==> final(krnl).allc_4k_mp.spec_index(ptr) == old(krnl).allc_4k_mp.spec_index(ptr),
        forall|ptr: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(ptr)] old(krnl).allc_2m_mp.dom().contains(ptr) ==> final(krnl).allc_2m_mp.spec_index(ptr) == old(krnl).allc_2m_mp.spec_index(ptr),
        forall|ptr: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(ptr)] old(krnl).allc_1g_mp.dom().contains(ptr) ==> final(krnl).allc_1g_mp.spec_index(ptr) == old(krnl).allc_1g_mp.spec_index(ptr),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, lctx, pcid_allocator_head,),
{
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let ghost allocator_4k_quota_lock_map = lctx.allocator_quota_4k_lock_map();
    let ghost allocator_4k_cache_lock_map = lctx.allocator_cache_4k_lock_map();
    let ghost allocator_4k_global_pool_lock_map = lctx.allocator_global_pool_4k_lock_map();
    let ghost allocator_2m_quota_lock_map = lctx.allocator_quota_2m_lock_map();
    let ghost allocator_2m_cache_lock_map = lctx.allocator_cache_2m_lock_map();
    let ghost allocator_2m_global_pool_lock_map = lctx.allocator_global_pool_2m_lock_map();
    let ghost allocator_1g_quota_lock_map = lctx.allocator_quota_1g_lock_map();
    let ghost allocator_1g_cache_lock_map = lctx.allocator_cache_1g_lock_map();
    let ghost allocator_1g_global_pool_lock_map = lctx.allocator_global_pool_1g_lock_map();
    proof {
        assert({
            &&& krnl.allc_4k_mp.perms_wf()
            &&& krnl.allc_2m_mp.perms_wf()
            &&& krnl.allc_1g_mp.perms_wf()
        }) by { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_map(krnl.allc_1g_mp); };
    }
    publish_new_container_allocator(
        &mut krnl.pg_arr, &mut krnl.allc_4k_mp, child_container_ptr, allocator_4k_page, Allocated4KPageState::As4KAllocator, allocator_4k_value,
        Ghost(allocator_4k_quota_lock_map), Ghost(allocator_4k_cache_lock_map), Ghost(allocator_4k_global_pool_lock_map),
        Ghost(page_locks), Tracked(lctx), Tracked(allocator_4k_page_lock_perm),
    );
    let ghost allocator_4k_page_locks = page_locks.insert(allocator_4k_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(allocator_4k_index), mode: TypedLockMode::Write });
    publish_new_container_allocator(
        &mut krnl.pg_arr, &mut krnl.allc_2m_mp, child_container_ptr, allocator_2m_page, Allocated4KPageState::As2MAllocator, allocator_2m_value,
        Ghost(allocator_2m_quota_lock_map), Ghost(allocator_2m_cache_lock_map), Ghost(allocator_2m_global_pool_lock_map),
        Ghost(allocator_4k_page_locks), Tracked(lctx), Tracked(allocator_2m_page_lock_perm),
    );
    let ghost allocator_2m_page_locks = allocator_4k_page_locks.insert(allocator_2m_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(allocator_2m_index), mode: TypedLockMode::Write });
    publish_new_container_allocator(
        &mut krnl.pg_arr, &mut krnl.allc_1g_mp, child_container_ptr, allocator_1g_page, Allocated4KPageState::As1GAllocator, allocator_1g_value,
        Ghost(allocator_1g_quota_lock_map), Ghost(allocator_1g_cache_lock_map), Ghost(allocator_1g_global_pool_lock_map),
        Ghost(allocator_2m_page_locks), Tracked(lctx), Tracked(allocator_1g_page_lock_perm),
    );
    Ghost(allocator_2m_page_locks.insert(allocator_1g_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(allocator_1g_index), mode: TypedLockMode::Write }))
}

pub(super) fn publish_new_container_scheduler(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_scheduler_ptr: RwLockSchedulerPtr, scheduler_page: PagePtr,
    scheduler_value: Scheduler, container_head: PageIndex, pcid_allocator_head: PageIndex, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: Ghost<Map<PageIndex, TypedHeldLock>>)
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        scheduler_perms_wf(old(krnl).sched_mp),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, lctx.thread_id()),
        old(krnl).sched_mp.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        lctx.kernel_view_locking_state() is Acquire,
        scheduler_value.inv(),
        forall|cpu_id: CpuId| #![trigger scheduler_value.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> !scheduler_value.shards.spec_index(cpu_id).view().locked(),
        child_scheduler_ptr == scheduler_page,
        !old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        page_ptr_valid(scheduler_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == lctx.thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, lctx, pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(scheduler_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(scheduler_page),),
    ensures
        final(krnl).sched_mp.spec_index(child_scheduler_ptr).inv(),
        final(krnl).pg_arr.typed_lock_map_aligned(ret.view(), lctx.thread_id()),
        ret.view().dom() == page_locks.dom(),
        forall|index: PageIndex| #![trigger ret.view().get(index)] #![trigger ret.view().dom().contains(index)] index != page_ptr2page_index(scheduler_page) ==> ret.view().get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret.view(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        final(krnl).sched_mp.typed_shard_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).sched_mp.perms_wf(),
        scheduler_perms_wf(old(krnl).sched_mp) ==> scheduler_perms_wf(final(krnl).sched_mp),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(scheduler_page),),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().owning_container == child_container_ptr,
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().locking_thread()->Write_lock_id,
        final(krnl).sched_mp.dom() =~= old(krnl).sched_mp.dom().insert(child_scheduler_ptr),
        final(krnl).sched_mp.spec_index(child_scheduler_ptr) == scheduler_value,
        forall|ptr: RwLockSchedulerPtr| #![trigger final(krnl).sched_mp.spec_index(ptr)] old(krnl).sched_mp.dom().contains(ptr) ==> final(krnl).sched_mp.spec_index(ptr) == old(krnl).sched_mp.spec_index(ptr),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, lctx, container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, lctx, pcid_allocator_head,),
{
    proof { assert(krnl.sched_mp.perms_wf()) by { scheduler_perms_wf_map(krnl.sched_mp); }; }
    let Tracked(scheduler_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, scheduler_page, Allocated4KPageState::AsScheduler, Ghost(page_locks), Tracked(lctx), Tracked(scheduler_page_lock_perm));
    let ghost scheduler_page_locks = page_locks.insert(page_ptr2page_index(scheduler_page), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(scheduler_page)), mode: TypedLockMode::Write });
    scheduler_map_insert_new_4k(&mut krnl.sched_mp, child_scheduler_ptr, scheduler_value, Tracked(scheduler_perm), Tracked(lctx));
    Ghost(scheduler_page_locks)
}

pub(super) fn publish_new_container_cpu_set(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_cpu_set_ptr: RwLockCpuSetPtr, cpu_set_page: PagePtr, cpu_set_value: CpuSet,
    container_head: PageIndex, pcid_allocator_head: PageIndex, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>, Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Ghost<Map<PageIndex, TypedHeldLock>>))
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        cpu_set_perms_wf(old(krnl).cpu_set_mp),
        old(krnl).pg_arr.typed_lock_map_aligned(page_locks, old(lctx).thread_id()),
        old(krnl).cpu_set_mp.typed_lock_map_aligned(old(lctx).cpu_set_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        cpu_set_value.inv(),
        child_cpu_set_ptr == cpu_set_page,
        !old(krnl).cpu_set_mp.dom().contains(child_cpu_set_ptr),
        page_ptr_valid(cpu_set_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state is Owned4k,
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        cpu_set_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().locking_thread()->Write_lock_id,
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(cpu_set_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(cpu_set_page),),
    ensures
        final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).pg_arr.typed_lock_map_aligned(ret.1.view(), final(lctx).thread_id()),
        ret.1.view().dom() == page_locks.dom(),
        forall|index: PageIndex| #![trigger ret.1.view().get(index)] #![trigger ret.1.view().dom().contains(index)] index != page_ptr2page_index(cpu_set_page) ==> ret.1.view().get(index) == page_locks.get(index),
        typed_lock_map_contains_mode(ret.1.view(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        final(krnl).cpu_set_mp.typed_lock_map_aligned(final(lctx).cpu_set_lock_map(), final(lctx).thread_id()),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).cpu_set_mp.perms_wf(),
        cpu_set_perms_wf(old(krnl).cpu_set_mp) ==> cpu_set_perms_wf(final(krnl).cpu_set_mp),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(cpu_set_page),),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().iommu_mappings() == old(krnl).pg_arr.spec_index(index).view().view().iommu_mappings(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map().dom() == old(lctx).cpu_set_lock_map().dom().insert(child_cpu_set_ptr),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), child_cpu_set_ptr, TypedLockMode::Write),
        forall|ptr: RwLockCpuSetPtr| #![trigger final(lctx).cpu_set_lock_map().get(ptr)] ptr != child_cpu_set_ptr ==> final(lctx).cpu_set_lock_map().get(ptr) == old(lctx).cpu_set_lock_map().get(ptr),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().owning_container == child_container_ptr,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().locking_thread()->Write_lock_id,
        final(krnl).cpu_set_mp.dom() =~= old(krnl).cpu_set_mp.dom().insert(child_cpu_set_ptr),
        final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).view() == cpu_set_value,
        !final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).being_killed(),
        forall|ptr: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(ptr)] old(krnl).cpu_set_mp.dom().contains(ptr) ==> final(krnl).cpu_set_mp.spec_index(ptr) == old(krnl).cpu_set_mp.spec_index(ptr),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).locking_thread()->Write_lock_id,
{
    proof { assert(krnl.cpu_set_mp.perms_wf()) by { cpu_set_perms_wf_map(krnl.cpu_set_mp); }; }
    let Tracked(cpu_set_perm) = page_array_retype_owned_4k_for_container(&mut krnl.pg_arr, child_container_ptr, cpu_set_page, Allocated4KPageState::AsCpuSet, Ghost(page_locks), Tracked(&*lctx), Tracked(cpu_set_page_lock_perm));
    let ghost cpu_set_page_locks = page_locks.insert(page_ptr2page_index(cpu_set_page), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(cpu_set_page)), mode: TypedLockMode::Write });
    let cpu_set_lock_perm = cpu_set_map_insert_new_4k(&mut krnl.cpu_set_mp, child_cpu_set_ptr, cpu_set_value, Tracked(cpu_set_perm), Tracked(&mut *lctx));
    (cpu_set_lock_perm, Ghost(cpu_set_page_locks))
}

pub(super) fn publish_new_container_pcid_allocator_and_container(
    krnl: &mut KernelK, child_pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid_allocator_value: PcidAllocator,
    child_container_ptr: RwLockContainerPtr, container_value: Container, container_rodata: ReadOnlyNode<ContainerRO>, container_ghost: ContainerGhost,
    Ghost(allocator_4k_page): Ghost<PagePtr>, Ghost(allocator_2m_page): Ghost<PagePtr>, Ghost(allocator_1g_page): Ghost<PagePtr>, Ghost(scheduler_page): Ghost<PagePtr>,
    Ghost(cpu_set_page): Ghost<PagePtr>, Ghost(child_process_ptr): Ghost<PagePtr>, Ghost(child_pagetable_ptr): Ghost<PagePtr>, Ghost(l4_page): Ghost<PagePtr>,
    Ghost(bootstrap_seq): Ghost<Seq<PagePtr>>, Ghost(funding_pages): Ghost<Seq<PagePtr>>, Ghost(funding_indices): Ghost<Set<PageIndex>>,
    Ghost(pool_page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Ghost(cpu_set_page_locks): Ghost<Map<PageIndex, TypedHeldLock>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pcid_allocator_perm): Tracked<PagePerm2m>, Tracked(container_perm): Tracked<PagePerm2m>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        pcid_allocator_perms_wf(old(krnl).pcid_allc_mp),
        container_perms_wf(old(krnl).ctn_mp),
        cpu_offline_flags_wf(old(krnl).cpu_offline_mp, old(krnl).cpu_arr),
        old(krnl).pcid_allc_mp.typed_lock_map_aligned(old(lctx).pcid_allocator_lock_map(), old(lctx).thread_id()),
        old(krnl).ctn_mp.typed_lock_map_aligned(old(lctx).container_lock_map(), old(lctx).thread_id()),
        old(krnl).cpu_offline_mp.typed_flag_lock_map_aligned(old(lctx).cpu_offline_flag_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pcid_allocator_value.inv(),
        container_value.inv(),
        !old(krnl).pcid_allc_mp.dom().contains(child_pcid_allocator_ptr),
        !old(krnl).ctn_mp.dom().contains(child_container_ptr),
        !old(krnl).cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child_container_ptr)),
        page_ptr_2m_valid(child_container_ptr),
        pcid_allocator_perm.is_init(),
        pcid_allocator_perm.addr() == child_pcid_allocator_ptr,
        container_perm.is_init(),
        container_perm.addr() == child_container_ptr,
        bootstrap_seq == seq![allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, child_process_ptr, child_pagetable_ptr, l4_page],
        bootstrap_seq.no_duplicates(),
        page_ptr2page_index(child_container_ptr) != page_ptr2page_index(child_pcid_allocator_ptr),
        page_ptr2page_index(allocator_2m_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(allocator_1g_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(allocator_1g_page) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(scheduler_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(scheduler_page) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(scheduler_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(cpu_set_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(cpu_set_page) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(cpu_set_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(cpu_set_page) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(child_process_ptr) != page_ptr2page_index(allocator_1g_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(child_process_ptr) != page_ptr2page_index(cpu_set_page),
        page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(cpu_set_page) && page_ptr2page_index(child_pagetable_ptr) != page_ptr2page_index(child_process_ptr),
        page_ptr2page_index(l4_page) != page_ptr2page_index(allocator_4k_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(allocator_2m_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(l4_page) != page_ptr2page_index(scheduler_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(cpu_set_page) && page_ptr2page_index(l4_page) != page_ptr2page_index(child_process_ptr),
        page_ptr2page_index(l4_page) != page_ptr2page_index(child_pagetable_ptr),
        page_ptr_valid(allocator_4k_page) && page_ptr_valid(allocator_2m_page) && page_ptr_valid(allocator_1g_page) && page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page) && page_ptr_valid(child_process_ptr) && page_ptr_valid(child_pagetable_ptr) && page_ptr_valid(l4_page),
        funding_indices == funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set(),
        funding_pages.no_duplicates(),
        forall|i: int| #![trigger page_ptr_valid(funding_pages.spec_index(i))] 0 <= i < funding_pages.len() ==> page_ptr_valid(funding_pages.spec_index(i)),
        pool_page_locks.dom() == old(lctx).page_lock_map().dom(),
        forall|i: int|
            #![trigger funding_pages.spec_index(i)]
            0 <= i < funding_pages.len() ==> {
                &&& typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(funding_pages.spec_index(i)), TypedLockMode::Write)
            },
        forall|index: PageIndex| #![trigger pool_page_locks.get(index)] #![trigger pool_page_locks.dom().contains(index)] !funding_indices.contains(index) ==> pool_page_locks.get(index) == old(lctx).page_lock_map().get(index),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_container_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_pcid_allocator_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(pool_page_locks, page_ptr2page_index(l4_page), TypedLockMode::Write),
        cpu_set_page_locks.dom() == pool_page_locks.dom(),
        forall|index: PageIndex|
            #![trigger cpu_set_page_locks.get(index)]
            #![trigger cpu_set_page_locks.dom().contains(index)]
            index != page_ptr2page_index(child_container_ptr) && index != page_ptr2page_index(child_pcid_allocator_ptr) && index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page)
                && index != page_ptr2page_index(allocator_1g_page) && index != page_ptr2page_index(scheduler_page) && index != page_ptr2page_index(cpu_set_page) && index != page_ptr2page_index(child_process_ptr)
                && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(l4_page) ==> cpu_set_page_locks.get(index) == pool_page_locks.get(index),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_container_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_pcid_allocator_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_process_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(cpu_set_page_locks, page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr).inv(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).pcid_allc_mp.typed_lock_map_aligned(final(lctx).pcid_allocator_lock_map(), final(lctx).thread_id()),
        final(krnl).ctn_mp.typed_lock_map_aligned(final(lctx).container_lock_map(), final(lctx).thread_id()),
        final(krnl).cpu_offline_mp.typed_flag_lock_map_aligned(final(lctx).cpu_offline_flag_lock_map(), final(lctx).thread_id()),
        *final(krnl) == (KernelK { pcid_allc_mp: final(krnl).pcid_allc_mp, ctn_mp: final(krnl).ctn_mp, cpu_offline_mp: final(krnl).cpu_offline_mp, ..*old(krnl) }),
        final(krnl).cpu_offline_mp.perms_wf(),
        final(krnl).cpu_offline_mp.dom() =~= old(krnl).cpu_offline_mp.dom().insert(cpu_offline_flags_ptr(child_container_ptr)),
        forall|ptr: RwLockCpuOfflineFlagsPtr| #![trigger final(krnl).cpu_offline_mp.spec_index(ptr)] old(krnl).cpu_offline_mp.dom().contains(ptr) ==> final(krnl).cpu_offline_mp.spec_index(ptr) == old(krnl).cpu_offline_mp.spec_index(ptr),
        final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).inv(),
        final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).owning_container.view() == child_container_ptr,
        final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).container_depth.view() == container_rodata.view().depth,
        forall|cpu_id: CpuId|
            #![trigger final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id)]
            index_valid(NUM_CPUS, cpu_id) ==> {
                &&& !final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id).view().locked()
                &&& final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id).view().view().index() == (cpu_offline_flags_ptr(child_container_ptr), cpu_id)
                &&& !final(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_container_ptr)).flags.spec_index(cpu_id).view().view().requested
            },
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(krnl).pcid_allc_mp.perms_wf(),
        pcid_allocator_perms_wf(old(krnl).pcid_allc_mp) ==> pcid_allocator_perms_wf(final(krnl).pcid_allc_mp),
        final(krnl).ctn_mp.perms_wf(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).page_lock_map() == cpu_set_page_locks,
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(child_pcid_allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(lctx).pcid_allocator_lock_map().get(ptr)]
            #![trigger final(lctx).pcid_allocator_lock_map().dom().contains(ptr)]
            ptr != child_pcid_allocator_ptr ==> final(lctx).pcid_allocator_lock_map().get(ptr) == old(lctx).pcid_allocator_lock_map().get(ptr),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(child_container_ptr),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger final(lctx).container_lock_map().dom().contains(ptr)]
            ptr != child_container_ptr ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(krnl).pcid_allc_mp.dom() =~= old(krnl).pcid_allc_mp.dom().insert(child_pcid_allocator_ptr),
        final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr).view() == pcid_allocator_value,
        forall|ptr: RwLockPcidAllocatorPtr| #![trigger final(krnl).pcid_allc_mp.spec_index(ptr)] old(krnl).pcid_allc_mp.dom().contains(ptr) ==> final(krnl).pcid_allc_mp.spec_index(ptr) == old(krnl).pcid_allc_mp.spec_index(ptr),
        final(krnl).ctn_mp.dom() =~= old(krnl).ctn_mp.dom().insert(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).is_init(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view() == container_value,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata() == container_rodata,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost() == container_ghost,
        final(krnl).ctn_mp.spec_index(child_container_ptr).control() == LockControl::DynamicProcess(LockOwnerId::Some(0)),
        forall|ptr: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(ptr)] old(krnl).ctn_mp.dom().contains(ptr) ==> final(krnl).ctn_mp.spec_index(ptr) == old(krnl).ctn_mp.spec_index(ptr),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr,).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), child_pcid_allocator_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write,),
{
    hide(Seq::contains);
    proof {
        assert(krnl.pcid_allc_mp.perms_wf() && krnl.ctn_mp.perms_wf() && krnl.cpu_offline_mp.perms_wf()) by {
            pcid_allocator_perms_wf_map(krnl.pcid_allc_mp); container_perms_wf_map(krnl.ctn_mp); cpu_offline_flags_wf_map(krnl.cpu_offline_mp, krnl.cpu_arr);
        };
    }
    let child_pcid_allocator_lock_perm = pcid_allocator_map_insert_new_2m(&mut krnl.pcid_allc_mp, child_pcid_allocator_ptr, pcid_allocator_value, Tracked(pcid_allocator_perm), Tracked(&mut *lctx));
    let child_container_lock_perm = container_map_insert_new_2m(&mut krnl.ctn_mp, child_container_ptr, container_value, container_rodata, container_ghost, Tracked(container_perm), Tracked(&mut *lctx));
    let flags_value = CpuOfflineFlags::new_empty(Ghost(child_container_ptr), Ghost(container_rodata.view().depth), Ghost(cpu_offline_flags_ptr(child_container_ptr)));
    krnl.cpu_offline_mp.retype_container_page_tail_and_insert(&krnl.ctn_mp, child_container_ptr, flags_value, Tracked(&*lctx));
    proof {
        assert(krnl.cpu_offline_mp.typed_flag_lock_map_aligned(lctx.cpu_offline_flag_lock_map(), lctx.thread_id())) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        let container_head = page_ptr2page_index(child_container_ptr);
        let pcid_allocator_head = page_ptr2page_index(child_pcid_allocator_ptr);
        lctx.enter_kernel_view_release();
        rekey_published_4k_page_chain(lctx, funding_pages, funding_pages.len() as int, pool_page_locks);
        lctx.update_lock_id(KernelObjId::Page(container_head), pool_page_locks.index(container_head).lock_id, cpu_set_page_locks.index(container_head).lock_id);
        lctx.update_lock_id(KernelObjId::Page(pcid_allocator_head), pool_page_locks.index(pcid_allocator_head).lock_id, cpu_set_page_locks.index(pcid_allocator_head).lock_id);
        page_ptr_seq_indices_no_duplicates(bootstrap_seq);
        page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 0); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 1); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 2);
        page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 3); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 4); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 5);
        page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 6); page_ptr_sequence_index_in_mapped_set(bootstrap_seq, 7);
        rekey_published_4k_page_chain(lctx, bootstrap_seq, 8, cpu_set_page_locks);
    }
    (child_pcid_allocator_lock_perm, child_container_lock_perm)
}

pub(super) fn link_new_container_into_tree(
    containers: &mut ContainerLockedMap, root_container: RwLockContainerPtr, parent_container_ptr: RwLockContainerPtr,
    child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr, child_scheduler_ptr: RwLockSchedulerPtr,
    child_pcid_allocator_ptr: RwLockPcidAllocatorPtr, child_cpu_set_ptr: RwLockCpuSetPtr, child_allocator_4k_ptr: RwLockPageAllocatorPtr,
    child_allocator_2m_ptr: RwLockPageAllocatorPtr, child_allocator_1g_ptr: RwLockPageAllocatorPtr, child_depth: usize,
    thread_page: PagePtr, Ghost(child_uppers): Ghost<Seq<RwLockContainerPtr>>, Ghost(moved_pages): Ghost<Set<PagePtr>>,
    Ghost(base_containers): Ghost<ContainerLockedMap>, Ghost(base_pages): Ghost<PageLockedArray>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
)
    requires
        container_perms_wf(base_containers),
        container_tree_wf(root_container, base_containers),
        container_pages_wf(base_pages, base_containers),
        base_containers.dom().contains(parent_container_ptr),
        !base_containers.dom().contains(child_container_ptr),
        base_containers.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(containers).perms_wf(),
        old(containers).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),),
        old(containers).dom() == base_containers.dom().insert(child_container_ptr),
        forall|container_ptr: RwLockContainerPtr|
            #![trigger old(containers).spec_index(container_ptr)]
            base_containers.dom().contains(container_ptr) ==> old(containers).spec_index(container_ptr) == base_containers.spec_index(container_ptr),
        old(containers).spec_index(child_container_ptr).is_init(),
        old(containers).spec_index(child_container_ptr).inv(),
        !old(containers).spec_index(child_container_ptr).being_killed(),
        old(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.is_init(),
        old(containers).spec_index(child_container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty(),
        old(containers).spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        old(containers).spec_index(child_container_ptr).view_rodata().view().depth == child_depth,
        old(containers).spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().pcid_allocator == child_pcid_allocator_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_2m == child_allocator_2m_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_1g == child_allocator_1g_ptr,
        old(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq.view() == child_uppers,
        old(containers).spec_index(child_container_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty(),
        old(containers).spec_index(child_container_ptr).view().owned_pages.view() == moved_pages,
        old(containers).spec_index(child_container_ptr).view().root_process == child_process_ptr,
        !old(containers).spec_index(child_container_ptr).view().zombie,
        old(containers).spec_index(child_container_ptr).view_ghost().owned_processes.view() == set![child_process_ptr],
        child_depth == base_containers.spec_index(parent_container_ptr).view_rodata().view().depth + 1,
        child_uppers == base_containers.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        child_uppers.no_duplicates(),
        child_uppers.to_set().subset_of(base_containers.dom()),
        !child_uppers.to_set().contains(child_container_ptr),
        moved_pages.subset_of(base_containers.spec_index(parent_container_ptr).view().owned_pages.view()),
        !moved_pages.contains(thread_page),
        base_containers.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        typed_lock_map_contains_mode(lctx.container_lock_map(), parent_container_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(lctx.container_lock_map(), child_container_ptr, TypedLockMode::Write,),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == lctx.thread_id(),
        parent_container_lock_perm.lock_id() == old(containers).spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == lctx.thread_id(),
        child_container_lock_perm.lock_id() == old(containers).spec_index(child_container_ptr).locking_thread()->Write_lock_id,
    ensures
        final(containers).spec_index(parent_container_ptr).inv(),
        final(containers).spec_index(child_container_ptr).inv(),
        final(containers).perms_wf(),
        final(containers).dom() == old(containers).dom(),
        final(containers).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),),
        final(containers).spec_index(child_container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty(),
        !final(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.is_init(),
        final(containers).spec_index(child_container_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty(),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(containers).spec_index(ptr).view_ghost().uppertree_seq]
            #![trigger base_containers.spec_index(ptr).view_ghost().uppertree_seq]
            base_containers.dom().contains(ptr) ==> final(containers).spec_index(ptr).view_ghost().uppertree_seq == base_containers.spec_index(ptr).view_ghost().uppertree_seq,
        forall|ptr: RwLockContainerPtr|
            #![trigger child_uppers.contains(ptr)]
            child_uppers.contains(ptr) ==> final(containers).spec_index(ptr).view_ghost().subtree_set.view() == base_containers.spec_index(ptr).view_ghost().subtree_set.view().insert(child_container_ptr),
        forall|ptr: RwLockContainerPtr|
            #![trigger base_containers.dom().contains(ptr)]
            base_containers.dom().contains(ptr) && !child_uppers.contains(ptr) ==> final(containers).spec_index(ptr).view_ghost().subtree_set == base_containers.spec_index(ptr).view_ghost().subtree_set,
        final(containers).spec_index(parent_container_ptr).view().children.view() == base_containers.spec_index(parent_container_ptr).view().children.view().push(child_container_ptr),
        final(containers).spec_index(parent_container_ptr).view().children.map().dom().contains(final(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.addr()),
        final(containers).spec_index(parent_container_ptr).view().children.map().spec_index(final(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.addr()) == child_container_ptr,
        forall|node_addr: usize|
            #![trigger base_containers.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr)]
            base_containers.spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr) ==> {
                &&& final(containers).spec_index(parent_container_ptr).view().children.map().dom().contains(node_addr)
                &&& final(containers).spec_index(parent_container_ptr).view().children.map().spec_index(node_addr) == base_containers.spec_index(parent_container_ptr).view().children.map().spec_index(node_addr)
            },
        final(containers).spec_index(parent_container_ptr).view().owned_pages.view() == base_containers.spec_index(parent_container_ptr).view().owned_pages.view().difference(moved_pages),
        final(containers).spec_index(parent_container_ptr).view() == (Container {
            children: final(containers).spec_index(parent_container_ptr).view().children,
            owned_pages: final(containers).spec_index(parent_container_ptr).view().owned_pages,
            ..base_containers.spec_index(parent_container_ptr).view()
        }),
        final(containers).spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        final(containers).spec_index(child_container_ptr).view().owned_pages.view() == moved_pages,
        !final(containers).spec_index(child_container_ptr).being_killed(),
        final(containers).spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        final(containers).spec_index(child_container_ptr).view_rodata().view().depth == child_depth,
        final(containers).spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().pcid_allocator == child_pcid_allocator_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_2m == child_allocator_2m_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_1g == child_allocator_1g_ptr,
        final(containers).spec_index(child_container_ptr).view().root_process == child_process_ptr,
        !final(containers).spec_index(child_container_ptr).view().zombie,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_processes.view() == set![child_process_ptr],
        final(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq == old(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_endpoints == old(containers).spec_index(child_container_ptr).view_ghost().owned_endpoints,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_threads == old(containers).spec_index(child_container_ptr).view_ghost().owned_threads,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_indirect_threads == old(containers).spec_index(child_container_ptr).view_ghost().owned_indirect_threads,
        final(containers).spec_index(child_container_ptr).view_ghost().retire_ready == old(containers).spec_index(child_container_ptr).view_ghost().retire_ready,
        final(containers).spec_index(child_container_ptr).control() == old(containers).spec_index(child_container_ptr).control(),
        parent_container_lock_perm.lock_id() == final(containers).spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.lock_id() == final(containers).spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        forall|container_ptr: RwLockContainerPtr|
            #![trigger final(containers).spec_index(container_ptr)]
            base_containers.dom().contains(container_ptr) ==> {
                &&& final(containers).spec_index(container_ptr).is_init() == base_containers.spec_index(container_ptr).is_init()
                &&& final(containers).spec_index(container_ptr).view_rodata() == base_containers.spec_index(container_ptr).view_rodata()
                &&& final(containers).spec_index(container_ptr).locking_thread() == base_containers.spec_index(container_ptr).locking_thread()
                &&& final(containers).spec_index(container_ptr).control() == base_containers.spec_index(container_ptr).control()
                &&& final(containers).spec_index(container_ptr).view().parent_linkedlist_node == base_containers.spec_index(container_ptr).view().parent_linkedlist_node
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_threads == base_containers.spec_index(container_ptr).view_ghost().owned_threads
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_processes == base_containers.spec_index(container_ptr).view_ghost().owned_processes
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_indirect_threads == base_containers.spec_index(container_ptr).view_ghost().owned_indirect_threads
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_endpoints == base_containers.spec_index(container_ptr).view_ghost().owned_endpoints
                &&& final(containers).spec_index(container_ptr).view_ghost().retire_ready == base_containers.spec_index(container_ptr).view_ghost().retire_ready
                &&& container_ptr != parent_container_ptr ==> final(containers).spec_index(container_ptr).view() == base_containers.spec_index(container_ptr).view()
            },
{
    proof { assert(old(containers).spec_index(parent_container_ptr).inv() && base_containers.spec_index(parent_container_ptr).view().children.view().no_duplicates()) by { container_perms_wf_at(base_containers, parent_container_ptr); }; }
    let (node_addr, node_perm) = container_map_take_parent_node(containers, child_container_ptr, Tracked(lctx), Tracked(child_container_lock_perm));
    proof {
        let ghost original_children = base_containers.spec_index(parent_container_ptr).view().children.view();
        assert(original_children.len() <= NUM_PAGES * 4096) by { container_children_len_bounded_at(root_container, base_pages, base_containers, parent_container_ptr); };
        assert(containers.spec_index(parent_container_ptr).view().children.length == original_children.len()) by { containers.spec_index(parent_container_ptr).view().children.lemma_len_view(); };
        assert(!original_children.contains(child_container_ptr)) by {
            if original_children.contains(child_container_ptr) { assert(base_containers.dom().contains(child_container_ptr)) by { container_children_parent_wf_at(root_container, base_containers, parent_container_ptr, child_container_ptr); }; }
        };
    }
    container_map_push_child(containers, parent_container_ptr, child_container_ptr, node_addr, node_perm, Tracked(lctx), Tracked(parent_container_lock_perm));
    proof { container_insert_child_into_ancestor_subtree_sets(containers, child_uppers, child_container_ptr, lctx.container_lock_map(), lctx.thread_id()); }
    container_map_remove_owned_pages(containers, parent_container_ptr, Ghost(moved_pages), Tracked(lctx), Tracked(parent_container_lock_perm));
}
}

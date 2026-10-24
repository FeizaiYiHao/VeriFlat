use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;
use super::syscall_ipc_pages_lock::*;
use super::syscall_ipc_pages_fill::ipc_pages_fill_target_page;

verus! {
/// Builds the missing L4, L3 and L2 directories of every target page of a pages rendezvous under the write-held target page table,
/// one `Share4kDirectory` step per new directory, then downgrades the target page table to read and returns the read lock and the target
/// window locks: the existing ones and those minted with each new L2.
fn ipc_pages_fill_target(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    target_allocator: RwLockPageAllocatorPtr, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<LockPerm>,
    Ghost(source_windows): Ghost<Map<WindowVa, LockPerm>>, Tracked(target_windows): Tracked<Map<WindowVa, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<Map<WindowVa, LockPerm>>))
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(target_thread)) >= 3 * target_range.len,
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == target_thread,
        share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source is None,
        old(krnl).ctn_mp.dom().contains(target_container),
        old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
        old(krnl).allc_4k_mp.dom().contains(target_allocator),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        !thread_is_dangling(old(krnl).thr_mp.spec_index(target_thread)),
        source_pagetable_lock_perm.state() is ReadLock,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 3 * target_range.len + 1,
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 3 * target_range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len()
            ==> share_4k_range_step(final(steps).view()[j], cpu_id) || ipc_pages_downgrade_step_pre(final(steps).view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == final(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        final(krnl).prc_mp.dom().contains(source_process),
        final(krnl).prc_mp.dom().contains(target_process),
        !final(krnl).prc_mp.spec_index(source_process).view().zombie,
        !final(krnl).prc_mp.spec_index(target_process).view().zombie,
        final(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        final(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        ret.0@.thread_id() == final(lctx).thread_id(),
        ret.0@.state() is ReadLock,
        final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret.0@),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && ret.1@.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.1@.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.1@.dom().contains(w)] ret.1@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.1@.index(w).state() is WriteLock
                &&& ret.1@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.1@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& final(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
{
    let tracked mut window_perms = target_windows;
    let range_len = target_range.len;
    let start_indices = va2index(target_range.start);
    let end_indices = va2index(target_range.index(range_len - 1));
    proof { held_kernel_objects_unchanged_reflexive(krnl, lctx); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable); }
    let mut i: usize = 0;
    while i < range_len
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            nonwindow_typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            steps.snapshot_k() == *krnl,
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + 3 * i,
            old(steps).nonlock_view().len() <= steps.nonlock_view().len() <= old(steps).nonlock_view().len() + 3 * i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len()
                ==> share_4k_range_step(steps.view()[j], cpu_id) || ipc_pages_downgrade_step_pre(steps.view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id),
            share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(*old(krnl), cpu_id),
            share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == target_thread,
            share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
            share_4k_objects_k(*old(krnl), cpu_id).transfer_source is None,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            current_thread_ptr != peer_thread_ptr,
            source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
            old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
            old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
            old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
            source_pagetable != target_pagetable,
            target_range.wf(),
            source_range.len > 0,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
            target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            target_pagetable_lock_perm.state() is WriteLock,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
            forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                    let indices = spec_va2index(target_range.view().spec_index(j));
                    &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                    &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                    &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
                },
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(target_thread)) >= 3 * target_range.len,
            old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.ctn_mp.dom().contains(target_container),
            krnl.ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
            krnl.allc_4k_mp.dom().contains(target_allocator),
            krnl.prc_mp.dom().contains(target_process),
            krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
            krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_threads_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), set![target_thread]),
            krnl.thr_mp.dom().contains(current_thread_ptr),
            krnl.thr_mp.dom().contains(peer_thread_ptr),
            krnl.thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
            held_pagetables_unchanged_except(old(krnl).pt_mp, krnl.pt_mp, old(lctx), set![target_pagetable]),
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)) ==> {
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).window_view(w) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_view(w)
                    &&& forall|v: VAddr|
                        #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)]
                        #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)]
                        spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                                ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(v)
                        }
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                        ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va)
                },
            krnl.thr_mp.spec_index(target_thread).being_killed() == old(krnl).thr_mp.spec_index(target_thread).being_killed(),
            !thread_is_dangling(krnl.thr_mp.spec_index(target_thread)),
            krnl.thr_mp.spec_index(target_thread).view_ghost() == old(krnl).thr_mp.spec_index(target_thread).view_ghost(),
            krnl.thr_mp.spec_index(target_thread).view().owning_container == old(krnl).thr_mp.spec_index(target_thread).view().owning_container,
            krnl.thr_mp.spec_index(target_thread).view().owning_proc == old(krnl).thr_mp.spec_index(target_thread).view().owning_proc,
            krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(target_thread).view().state == old(krnl).thr_mp.spec_index(target_thread).view().state,
            krnl.thr_mp.spec_index(target_thread).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(target_thread).view().endpoint_descriptors.view(),
            krnl.thr_mp.spec_index(target_thread).view().upper_container_seq == old(krnl).thr_mp.spec_index(target_thread).view().upper_container_seq,
            krnl.thr_mp.spec_index(target_thread).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view(),
            krnl.thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(target_thread).view().quota_4k - 3 * i <= krnl.thr_mp.spec_index(target_thread).view().quota_4k,
            current_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            peer_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(target_pagetable),
            krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
            target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).wf(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus,
            target_range.len == range_len,
            i <= range_len,
            start_indices == spec_va2index(target_range.start),
            end_indices == spec_va2index(target_range.view()[range_len - 1]),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                p != target_pagetable ==> lctx.pagetable_window_lock_map().dom().contains((p, w)) == old(lctx).pagetable_window_lock_map().dom().contains((p, w)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    ==> lctx.pagetable_window_lock_map().dom().contains((p, w)) && lctx.pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w))]
                lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w))
                    == (va_range_2m_windows(*target_range).contains(w) && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
            forall|w: WindowVa|
                #![trigger lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w))]
                #![trigger va_range_2m_windows(*target_range).contains(w)]
                lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)) ==> {
                &&& window_perms.dom().contains(w)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == lctx.thread_id()
                &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
            },
            forall|w: WindowVa| #![trigger window_perms.dom().contains(w)]
                window_perms.dom().contains(w) ==> lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)),
            forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < i ==> {
                let va = target_range.view().spec_index(j);
                &&& pei_valid(spec_v2l4index(va)) && pei_valid(spec_v2l3index(va)) && pei_valid(spec_v2l2index(va))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_v2l4index(va)
                &&& lctx.pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        decreases range_len - i,
    {
        ipc_pages_fill_target_page(
            krnl, target_range, i, start_indices, end_indices, target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable,
            Ghost(current_thread_ptr), Ghost(old(steps).view().len() as int), Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(if target_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }), Tracked(&target_pagetable_lock_perm), Tracked(&mut window_perms),
        );
        i = i + 1;
    }
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        va_range_2m_windows_contains_window_of_first_n_pages(*source_range, source_range.len as int);
        container_thread_wf_uppertree_at(old(krnl).ctn_mp, old(krnl).thr_mp, target_thread); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, target_container);
    }
    let Tracked(read_perm) = ipc_pages_downgrade_target(
        krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
        source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
        Tracked(peer_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Ghost(source_windows), Ghost(window_perms),
        Ghost(old(steps).view().len() as int),
    );
    (Tracked(read_perm), Tracked(window_perms))
}

/// Downgrades the filled target page table of a pages rendezvous from write to read and records the downgrade step; the held
/// source table and every held window keep their state, and the target windows now satisfy the read-mode window facts.
fn ipc_pages_downgrade_target(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<LockPerm>, Ghost(source_windows): Ghost<Map<WindowVa, LockPerm>>,
    Ghost(target_windows): Ghost<Map<WindowVa, LockPerm>>, Ghost(start): Ghost<int>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        source_pagetable_lock_perm.state() is ReadLock,
        0 <= start <= old(steps).view().len(),
        forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len()
            ==> share_4k_range_step(old(steps).view()[j], cpu_id) || ipc_pages_downgrade_step_pre(old(steps).view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(old(steps).view()[j].old_u, old(steps).view()[j].new_u, cpu_id),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 1,
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] start <= j < final(steps).view().len()
            ==> share_4k_range_step(final(steps).view()[j], cpu_id) || ipc_pages_downgrade_step_pre(final(steps).view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == final(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        final(krnl).prc_mp.dom().contains(source_process),
        final(krnl).prc_mp.dom().contains(target_process),
        !final(krnl).prc_mp.spec_index(source_process).view().zombie,
        !final(krnl).prc_mp.spec_index(target_process).view().zombie,
        final(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        final(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        ret@.thread_id() == final(lctx).thread_id(),
        !(ret@.state() is WriteLock),
        ret@.state() is ReadLock,
        final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret@),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& final(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
{
    let ghost pre_k = *krnl;
    let ghost before = steps.view();
    proof {
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
        ipc_pages_downgrade_step_pre_from_k(&*krnl, &*lctx, cpu_id, current_thread_ptr, peer_thread_ptr, source_thread, target_thread, source_process, target_process,
            source_pagetable, target_pagetable, *source_range, *target_range);
    }
    let Tracked(read_perm) = krnl.downgrade_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    proof {
        let ghost downgraded_k = *krnl;
        assert(krnl.pt_lower.view() =~= pre_k.pt_lower.view().insert(source_pagetable, krnl.pt_lower.view().spec_index(source_pagetable))
            .insert(target_pagetable, krnl.pt_lower.view().spec_index(target_pagetable)));
        kernel_pagetable_pair_lock_modes_and_progress_changed_implies_u_step(&pre_k, &*krnl, source_process, target_process, source_pagetable, target_pagetable,
            current_thread_ptr);
        ipc_pages_downgrade_step_from_u(kernel_k_to_kernel_u(pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, source_process, target_process, LockStateU::ReadLocked);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        ipc_pages_trace_downgrade_step(&*steps, before, start, kernel_k_to_kernel_u(pre_k), kernel_k_to_kernel_u(downgraded_k), cpu_id);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        container_thread_wf_uppertree_at(pre_k.ctn_mp, pre_k.thr_mp, target_thread); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, target_container);
        va_range_2m_windows_contains_window_of_first_n_pages(*source_range, source_range.len as int);
        va_range_2m_windows_contains_window_of_first_n_pages(*target_range, target_range.len as int);
    }
    Tracked(read_perm)
}

/// After a passed pages check: records the check step, reads the target container's 4K allocator, and when the target page table was
/// write-locked for filling builds the missing target directories and downgrades it, leaving both tables read-held with every target
/// page's L2 entry present.
fn ipc_pages_prepare_target(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    fill: bool, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<LockPerm>,
    Ghost(source_windows): Ghost<Map<WindowVa, LockPerm>>, Tracked(target_windows): Tracked<Map<WindowVa, LockPerm>>, Ghost(channel_index): Ghost<EndpointIdx>,
) -> (ret: (usize, Tracked<LockPerm>, Tracked<Map<WindowVa, LockPerm>>))
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ipc_pages_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Success,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, if fill { TypedLockMode::Write } else { TypedLockMode::Read }),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        (target_pagetable_lock_perm.state() is WriteLock) == fill,
        fill ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !fill ==> target_pagetable_lock_perm.state() is ReadLock,
        !fill ==> old(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
                &&& !fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !fill ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !fill ==> forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(target_thread)) >= 3 * target_range.len,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        old(steps).view().len() + 1 <= final(steps).view().len() <= old(steps).view().len() + 3 * target_range.len + 2,
        old(steps).nonlock_view().len() + 1 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 3 * target_range.len + 1,
        ipc_pages_check_result(final(steps).view()[old(steps).view().len() as int].old_u, cpu_id) is Success,
        ipc_pages_check_step_pre(final(steps).view()[old(steps).view().len() as int].old_u, cpu_id, channel_index),
        ipc_pages_check_step(final(steps).view()[old(steps).view().len() as int].old_u, final(steps).view()[old(steps).view().len() as int].new_u, cpu_id),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() < j < final(steps).view().len()
            ==> share_4k_range_step(final(steps).view()[j], cpu_id) || ipc_pages_downgrade_step_pre(final(steps).view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == final(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        final(krnl).prc_mp.dom().contains(source_process),
        final(krnl).prc_mp.dom().contains(target_process),
        !final(krnl).prc_mp.spec_index(source_process).view().zombie,
        !final(krnl).prc_mp.spec_index(target_process).view().zombie,
        final(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        final(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        ret.1@.thread_id() == final(lctx).thread_id(),
        !(ret.1@.state() is WriteLock),
        ret.1@.state() is ReadLock,
        final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret.1@),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && ret.2@.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.2@.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.2@.dom().contains(w)] ret.2@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.2@.index(w).state() is WriteLock
                &&& ret.2@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.2@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& final(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        forall|j: int| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(target_range.view().spec_index(j))))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        ret.0 == final(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k,
{
    let ghost tables = if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read };
    let ghost check_pre_k = *krnl;
    proof {
        ipc_pages_check_step_pre_from_k(&*krnl, &*lctx, cpu_id, current_thread_ptr, peer_thread_ptr, endpoint_ptr, channel_index, source_thread, target_thread, source_process, target_process,
            source_pagetable, target_pagetable, tables);
    }
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } })), Tracked(&*lctx),
        Tracked(current_thread_lock_perm));
    proof {
        assert(ipc_pages_check_step(kernel_k_to_kernel_u(check_pre_k), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
            kernel_thread_syscall_progress_changed_implies_u_step(&check_pre_k, &*krnl, current_thread_ptr);
            ipc_pages_passed_check_step_from_u(kernel_k_to_kernel_u(check_pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, *source_range, *target_range, peer_thread_ptr, tables);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread); container_perms_wf_at(krnl.ctn_mp, target_container);
        process_pagetable_match_pagetable_at(krnl.prc_mp, krnl.pt_mp, target_pagetable);
        va_range_2m_windows_contains_window_of_first_n_pages(*source_range, source_range.len as int);
        assert(share_mapping_4k_range_owner_compatible(&*krnl, source_pagetable, target_container, source_range)) by {
            container_thread_wf_uppertree_at(check_pre_k.ctn_mp, check_pre_k.thr_mp, target_thread); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
            container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, target_container);
        };
    }
    let target_allocator = krnl.ctn_mp.borrow_rodata(target_container).borrow().allocator_ptr_4k;
    proof {
        assert(krnl.allc_4k_mp.dom().contains(target_allocator)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, target_container); };
        assert({
            &&& share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread && share_4k_objects_k(*krnl, cpu_id).quota_thread == target_thread
            &&& share_4k_objects_k(*krnl, cpu_id).target == target_process && share_4k_objects_k(*krnl, cpu_id).target_container == target_container
            &&& share_4k_objects_k(*krnl, cpu_id).transfer_source is None
        }) by { reveal(share_4k_objects_k); };
    }
    let (Tracked(read_perm), Tracked(read_windows)) = if fill {
        ipc_pages_fill_target(
            krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
            source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
            Tracked(peer_thread_lock_perm), target_allocator, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Ghost(source_windows), Tracked(target_windows),
        )
    } else {
        proof { va_range_2m_windows_contains_window_of_first_n_pages(*target_range, target_range.len as int); }
        (Tracked(target_pagetable_lock_perm), Tracked(target_windows))
    };
    (target_allocator, Tracked(read_perm), Tracked(read_windows))
}

/// After a passed pages check: records the check step, builds the missing target directories and downgrades the target table when it
/// was write-locked for filling, and shares every source page into the read-held target table under the held windows.
pub(super) fn ipc_pages_share_locked(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    fill: bool, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<LockPerm>,
    Ghost(source_windows): Ghost<Map<WindowVa, LockPerm>>, Tracked(target_windows): Tracked<Map<WindowVa, LockPerm>>,
    Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
) -> (ret: (Tracked<LockPerm>, Tracked<Map<WindowVa, LockPerm>>))
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        0 <= start <= old(steps).view().len(),
        ipc_pages_trace_after_lock(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range },
            if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }),
        ipc_pages_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Success,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, if fill { TypedLockMode::Write } else { TypedLockMode::Read }),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        (target_pagetable_lock_perm.state() is WriteLock) == fill,
        fill ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !fill ==> target_pagetable_lock_perm.state() is ReadLock,
        !fill ==> old(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
                &&& !fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !fill ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !fill ==> forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(target_thread)) >= 3 * target_range.len,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        old(steps).view().len() + source_range.len + 1 <= final(steps).view().len() <= old(steps).view().len() + 4 * source_range.len + 2,
        old(steps).nonlock_view().len() + source_range.len + 1 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 1,
        ipc_pages_trace_after_share(final(steps).view(), start, pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == final(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: source_range.len, origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        final(krnl).prc_mp.dom().contains(source_process),
        final(krnl).prc_mp.dom().contains(target_process),
        !final(krnl).prc_mp.spec_index(source_process).view().zombie,
        !final(krnl).prc_mp.spec_index(target_process).view().zombie,
        final(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        final(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        ret.0@.thread_id() == final(lctx).thread_id(),
        !(ret.0@.state() is WriteLock),
        ret.0@.state() is ReadLock,
        final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret.0@),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && ret.1@.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.1@.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.1@.dom().contains(w)] ret.1@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.1@.index(w).state() is WriteLock
                &&& ret.1@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.1@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
{
    let ghost range = if waiting_state is SENDING { *source_range } else { *target_range };
    let ghost tables = if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read };
    let ghost check_before = steps.view();
    let (target_allocator, Tracked(read_perm), Tracked(read_windows)) = ipc_pages_prepare_target(
        krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
        source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
        Tracked(peer_thread_lock_perm), fill, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Ghost(source_windows), Tracked(target_windows), Ghost(channel_index),
    );
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread); container_perms_wf_at(krnl.ctn_mp, target_container);
        process_pagetable_match_pagetable_at(krnl.prc_mp, krnl.pt_mp, target_pagetable);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, target_container);
        assert({
            &&& share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread && share_4k_objects_k(*krnl, cpu_id).quota_thread == target_thread
            &&& share_4k_objects_k(*krnl, cpu_id).target == target_process && share_4k_objects_k(*krnl, cpu_id).target_container == target_container
            &&& share_4k_objects_k(*krnl, cpu_id).transfer_source is None
        }) by { reveal(share_4k_objects_k); };
    }
    share_mapping_4k_build_and_share(
        krnl, source_range, target_range, target_allocator, source_thread, target_thread, current_thread_ptr, target_process, target_container, cpu_id, source_pagetable,
        target_pagetable, false, None, Ghost(Share4kOrigin::IpcPages { peer: peer_thread_ptr }), Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(if source_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }), Tracked(if target_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }),
        Tracked(source_pagetable_lock_perm), Tracked(&read_perm), Tracked(None), Tracked(None),
    );
    proof {
        ipc_pages_trace_share_steps(&*steps, check_before, start, pre, cpu_id, channel_index, waiting_state, range, tables);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
    }
    (Tracked(read_perm), Tracked(read_windows))
}

/// Releases the held windows and both page tables of a pages rendezvous and records the release step with `result`: the unlock step
/// after a share, or the failed check step otherwise, completing the mapping trace that starts at `start`.
pub(super) fn ipc_pages_release_tables_and_record(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    result: RetValueType, fill: bool, source_user: bool, target_user: bool, Tracked(source_pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<LockPerm>, Tracked(source_windows): Tracked<Map<WindowVa, LockPerm>>,
    Tracked(target_windows): Tracked<Map<WindowVa, LockPerm>>, Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        0 <= start <= old(steps).view().len(),
        result is Success ==> ipc_pages_trace_after_share(old(steps).view(), start, pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }),
        !(result is Success) ==> ipc_pages_trace_after_lock(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, channel_index, waiting_state,
            if waiting_state is SENDING { *source_range } else { *target_range }, if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }),
        !(result is Success) ==> result == ipc_pages_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == (if result is Success { Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: source_range.len,
            origin: Share4kOrigin::IpcPages { peer: peer_thread_ptr } }) } else { Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }) }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if source_thread == current_thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, if (fill && !(result is Success)) { TypedLockMode::Write } else { TypedLockMode::Read }),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        (target_pagetable_lock_perm.state() is WriteLock) == (fill && !(result is Success)),
        (fill && !(result is Success)) ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !(fill && !(result is Success)) ==> target_pagetable_lock_perm.state() is ReadLock,
        !(fill && !(result is Success)) ==> old(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        (fill && !(result is Success)) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        (fill && !(result is Success)) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        source_user == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0),
        target_user == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        source_user && target_user ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        source_user && target_user ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
                &&& !(fill && !(result is Success)) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !(fill && !(result is Success)) ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(source_user && target_user) ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        ipc_pages_mapping_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }, result),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)] t == source_thread || t == target_thread ==> {
            &&& final(krnl).thr_mp.dom().contains(t)
            &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
            &&& final(krnl).thr_mp.spec_index(t).view().state == old(krnl).thr_mp.spec_index(t).view().state
            &&& final(krnl).thr_mp.spec_index(t).view().owning_proc == old(krnl).thr_mp.spec_index(t).view().owning_proc
            &&& final(krnl).thr_mp.spec_index(t).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& final(krnl).thr_mp.spec_index(t).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(t).view().temp_alloc_clean()
        },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: Some(result) }),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
{
    let ghost range = if waiting_state is SENDING { *source_range } else { *target_range };
    let ghost tables = if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read };
    let ghost unlock_pre_k = *krnl;
    let ghost unlock_before = steps.view();
    let passed = match result { RetValueType::Success => true, _ => false };
    proof {
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
        if passed {
            ipc_pages_unlock_tables_step_pre_from_k(&*krnl, &*lctx, cpu_id, current_thread_ptr, peer_thread_ptr, source_thread, target_thread, source_process, target_process,
                source_pagetable, target_pagetable, *source_range, *target_range);
        } else {
            ipc_pages_check_step_pre_from_k(&*krnl, &*lctx, cpu_id, current_thread_ptr, peer_thread_ptr, endpoint_ptr, channel_index, source_thread, target_thread, source_process,
                target_process, source_pagetable, target_pagetable, tables);
        }
    }
    let Ghost(unlocked_k) = ipc_pages_release_tables_and_progress(
        krnl, source_range, target_range, source_pagetable, target_pagetable, cpu_id, current_thread_ptr, peer_thread_ptr, endpoint_ptr, result, source_user && target_user,
        fill && !passed, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm),
        Tracked(source_windows), Tracked(target_windows),
    );
    proof {
        kernel_pagetable_pair_lock_modes_and_progress_changed_implies_u_step(&unlock_pre_k, &unlocked_k, source_process, target_process, source_pagetable, target_pagetable,
            current_thread_ptr);
        if passed {
            ipc_pages_unlock_tables_step_from_u(kernel_k_to_kernel_u(unlock_pre_k), kernel_k_to_kernel_u(unlocked_k), cpu_id, current_thread_ptr, *source_range, *target_range,
                peer_thread_ptr, source_process, target_process, unlocked_k.pt_mp.spec_index(source_pagetable).lock_state_u(), unlocked_k.pt_mp.spec_index(target_pagetable).lock_state_u());
            ipc_pages_trace_unlock_step(&*steps, unlock_before, start, pre, kernel_k_to_kernel_u(unlock_pre_k), kernel_k_to_kernel_u(unlocked_k), cpu_id, channel_index, waiting_state, range);
        } else {
            ipc_pages_failed_check_step_from_u(kernel_k_to_kernel_u(unlock_pre_k), kernel_k_to_kernel_u(unlocked_k), cpu_id, current_thread_ptr, *source_range, *target_range,
                peer_thread_ptr, tables, result, source_process, target_process, unlocked_k.pt_mp.spec_index(source_pagetable).lock_state_u(),
                unlocked_k.pt_mp.spec_index(target_pagetable).lock_state_u());
            ipc_pages_trace_failed_check_step(&*steps, unlock_before, start, pre, kernel_k_to_kernel_u(unlock_pre_k), kernel_k_to_kernel_u(unlocked_k), cpu_id, channel_index,
                waiting_state, range, tables, result);
        }
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
    }
}
} // verus!

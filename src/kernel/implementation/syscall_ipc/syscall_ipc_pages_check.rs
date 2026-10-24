use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pages_helpers::ipc_share_pages_source_owners_in_target_uppertree;

verus! {
/// Checks under the target page table's lock that no target page has a 4K, 2M, or 1G leaf; an interval known to hold a 4K leaf
/// is scanned for its first leaf, which is returned as the witness.
fn ipc_pages_target_free(
    krnl: &KernelK, target_range: &VaRange4K, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: (bool, Ghost<Option<(L4Index, L3Index, L2Index, L1Index)>>))
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(target_pagetable),
        target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
        target_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        target_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        target_range.wf(),
        target_range.len > 0,
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
    ensures
        ret.0 == (pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_mapping_4k_range_empty(spec_va2index(target_range.start), spec_va2index(target_range.view().spec_index(target_range.len - 1)))
            && forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            }),
        ret.1@ is Some ==> {
            let f = ret.1@->Some_0;
            &&& pei_valid(f.0) && pei_valid(f.1) && pei_valid(f.2) && pei_valid(f.3)
            &&& spec_l4_index_path_le(spec_va2index(target_range.start), f)
            &&& spec_l4_index_path_le(f, spec_va2index(target_range.view().spec_index(target_range.len - 1)))
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(spec_index2va(f))
        },
        !ret.0 && ret.1@ is None ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_mapping_4k_range_empty(spec_va2index(target_range.start), spec_va2index(target_range.view().spec_index(target_range.len - 1))),
        ret.1@ is None ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_mapping_4k_va_range_empty(target_range.start, target_range.view().spec_index(target_range.len - 1)),
{
    let range_len = target_range.len;
    let range_start = target_range.start;
    let end_index = range_len - 1;
    let end_va = target_range.index(end_index);
    assert(end_va == spec_va_add_range(range_start, end_index)) by { target_range.va_range_lemma(); };
    let start_indices = va2index(range_start);
    proof {
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(target_pagetable).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
    }
    let pagetable = krnl.pt_mp.borrow_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(target_pagetable_lock_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(target_pagetable);
    if !pagetable.mapping_4k_va_range_empty(Tracked(lower), range_start, end_va) {
        proof { broadcast use spec_va_4k_valid_index_roundtrip; }
        let found = pagetable.next_mapped_4k_from(Tracked(lower), start_indices);
        return (false, Ghost(found));
    }
    (pagetable.mapping_4k_va_range_buildable(Tracked(lower), target_range), Ghost(None))
}

/// Runs the source owner check of a pages rendezvous whose containers are not related by ancestry, keeping every fact of the held
/// page tables, windows, and threads that the remaining checks rely on.
fn ipc_pages_check_source_owners(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    fill: bool, source_user: bool, target_user: bool, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
    Ghost(source_windows): Ghost<Map<WindowVa, LockPerm>>, Ghost(target_windows): Ghost<Map<WindowVa, LockPerm>>,
) -> (ret: bool)
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
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
                &&& !fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !fill ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(source_user && target_user) ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
        !fill && source_user && target_user ==> forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        source_user && target_user,
        source_container != target_container,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
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
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
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
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, if fill { TypedLockMode::Write } else { TypedLockMode::Read }),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        (target_pagetable_lock_perm.state() is WriteLock) == fill,
        fill ==> target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !fill ==> target_pagetable_lock_perm.state() is ReadLock,
        !fill ==> final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        fill ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        fill ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        source_user == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0),
        target_user == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        source_user && target_user ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        source_user && target_user ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
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
                &&& !fill ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !fill ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(source_user && target_user) ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
        !fill && source_user && target_user ==> forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
        ret == share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& final(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
{
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, source_thread); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(target_thread).inv()) by { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, target_thread); };
        va_range_2m_windows_contains_window_of_first_n_pages(*source_range, source_range.len as int);
        va_range_2m_windows_contains_window_of_first_n_pages(*target_range, target_range.len as int);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        assert(lctx.thread_lock_map().dom() =~= set![source_thread, target_thread]);
    }
    let owners = share_mapping_4k_source_owner_precheck(
        krnl, source_range, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, Tracked(&mut *lctx),
        Tracked(&mut *steps), Tracked(if source_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }),
        Tracked(if target_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }), Tracked(source_pagetable_lock_perm),
        Tracked(target_pagetable_lock_perm),
    );
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        container_thread_wf_uppertree_at(old(krnl).ctn_mp, old(krnl).thr_mp, target_thread); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        container_uppertree_seq_in_dom(old(krnl).rt_ctn, old(krnl).ctn_mp, target_container); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, target_container);
    }
    owners
}

/// Runs the pages checks of a rendezvous under both held page tables and their held 2M windows: source range, source leaves, target
/// quota, target range, source owners, and target leaves, returning the result in the specification's priority. The owner check runs
/// before the target leaf check, so a target range in use may cost one owner check.
pub(super) fn ipc_pages_check_tables(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    fill: bool, source_user: bool, target_user: bool, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
    Ghost(source_windows): Ghost<Map<WindowVa, LockPerm>>, Ghost(target_windows): Ghost<Map<WindowVa, LockPerm>>,
) -> (ret: RetValueType)
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
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
                &&& !fill ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !fill ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(source_user && target_user) ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
        !fill && source_user && target_user ==> forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
        ret is Success || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        ret == ipc_pages_check_result(kernel_k_to_kernel_u(*final(krnl)), cpu_id),
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
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
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
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, if fill { TypedLockMode::Write } else { TypedLockMode::Read }),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        (target_pagetable_lock_perm.state() is WriteLock) == fill,
        fill ==> target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !fill ==> target_pagetable_lock_perm.state() is ReadLock,
        !fill ==> final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        fill ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        fill ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        source_user == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0),
        target_user == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        source_user && target_user ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        source_user && target_user ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
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
                &&& !fill ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !fill ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(source_user && target_user) ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
        !fill && source_user && target_user ==> forall|j: int| #![trigger window_of(target_range.view().spec_index(j))] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
        ret is Success ==> source_user && target_user,
        ret is Success ==> forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& final(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j))))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
        ret is Success ==> share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
        ret is Success ==> thread_effective_quota_4k(final(krnl).thr_mp.spec_index(target_thread)) >= 3 * target_range.len,
        ret is Success ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_mapping_4k_range_empty(spec_va2index(target_range.start), spec_va2index(target_range.view().spec_index(target_range.len - 1))),
        ret is Success ==> forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j))
            },
{
    hide(Seq::no_duplicates);
    let ghost mut found: Option<(L4Index, L3Index, L2Index, L1Index)> = None;
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, source_thread); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread);
        assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(target_thread).inv()) by { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, target_thread); };
    }
    let result = if !source_user {
        RetValueType::Error
    } else if !share_mapping_4k_source_precheck(&*krnl, source_range, source_pagetable, Tracked(&*lctx), Tracked(source_pagetable_lock_perm)) {
        RetValueType::ErrorIpcSourceUnmapped
    } else if krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx),
        Tracked(if target_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm })).quota_4k < 3usize * target_range.len {
        RetValueType::ErrorNoQuota
    } else if !target_user {
        RetValueType::Error
    } else {
        let containers_compatible = if source_container == target_container { true }
            else { container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, source_container, target_container) };
        let owners_compatible = if containers_compatible {
            proof {
                ipc_share_pages_source_owners_in_target_uppertree(&*krnl, cpu_id, current_thread_ptr, peer_thread_ptr, source_thread, source_pagetable, source_container, target_container,
                    source_range);
            }
            true
        } else {
            ipc_pages_check_source_owners(
                krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
                source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
                Tracked(peer_thread_lock_perm), fill, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Ghost(source_windows),
                Ghost(target_windows),
            )
        };
        let (target_clear, Ghost(target_found)) = ipc_pages_target_free(&*krnl, target_range, target_pagetable, Tracked(&*lctx), Tracked(target_pagetable_lock_perm));
        proof { found = target_found; }
        if !target_clear { RetValueType::ErrorVaInUse } else if !owners_compatible { RetValueType::ErrorIpcPageOwnerMismatch } else { RetValueType::Success }
    };
    proof {
        if result is Success { va_range_2m_windows_contains_window_of_first_n_pages(*source_range, source_range.len as int); }
        if !fill { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable); }
        ipc_pages_check_result_from_k(&*krnl, cpu_id, current_thread_ptr, peer_thread_ptr, source_thread, target_thread, source_process, target_process, source_pagetable,
            target_pagetable, target_container, *source_range, *target_range, if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read }, result, found);
    }
    result
}
} // verus!

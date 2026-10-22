use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;
use super::syscall_ipc_pages_check::ipc_pages_check_tables;
use super::syscall_ipc_pages_lock::ipc_pages_lock_tables;
use super::syscall_ipc_pages_share::{ipc_pages_release_tables_and_record, ipc_pages_share_locked};
use vstd::{assert_maps_equal, assert_maps_equal_internal};

verus! {
/// After the pages enter step, locks both page tables and their windows of the two ranges (filling the target directories under a
/// write-locked target when one is missing), checks and shares the pages, and releases everything with the check result, extending
/// the mapping trace that starts at `start`.
fn ipc_lock_tables_and_share_pages(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot,
    Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        ipc_pages_trace_after_enter(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, channel_index, waiting_state,
            if waiting_state is SENDING { *source_range } else { *target_range }),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        (waiting_state is SENDING) == (source_thread == current_thread_ptr),
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: None,
        }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
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
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        old(krnl).prc_mp.dom().contains(target_process),
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret is Success || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 3 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 3,
        !(ret is Success) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 2,
        ipc_pages_mapping_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id,
            channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }, ret),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)] t == source_thread || t == target_thread ==> {
            &&& final(krnl).thr_mp.dom().contains(t)
            &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
            &&& final(krnl).thr_mp.spec_index(t).view().state == old(krnl).thr_mp.spec_index(t).view().state
            &&& final(krnl).thr_mp.spec_index(t).view().owning_proc == old(krnl).thr_mp.spec_index(t).view().owning_proc
            &&& final(krnl).thr_mp.spec_index(t).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& final(krnl).thr_mp.spec_index(t).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(t).view().temp_alloc_clean()
        },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: Some(ret),
        }),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
{
    let (fill, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows)) = ipc_pages_lock_tables(
        krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
        source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
        Tracked(peer_thread_lock_perm), Ghost(channel_index), Ghost(waiting_state), Ghost(start), Ghost(pre),
    );
    let result = ipc_pages_check_tables(
        krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
        source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
        Tracked(peer_thread_lock_perm), fill, source_user, target_user, Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm), Ghost(source_windows), Ghost(target_windows),
    );
    let passed = match result { RetValueType::Success => true, _ => false };
    if passed {
        let (Tracked(read_perm), Tracked(read_windows)) = ipc_pages_share_locked(
            krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
            source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
            Tracked(peer_thread_lock_perm), fill, Tracked(&source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Ghost(source_windows), Tracked(target_windows), Ghost(channel_index), Ghost(waiting_state), Ghost(start), Ghost(pre),
        );
        ipc_pages_release_tables_and_record(
            krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
            source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
            Tracked(peer_thread_lock_perm), result, fill, true, true, Tracked(source_pagetable_lock_perm), Tracked(read_perm), Tracked(source_windows), Tracked(read_windows), Ghost(channel_index), Ghost(waiting_state), Ghost(start), Ghost(pre),
        );
    } else {
        ipc_pages_release_tables_and_record(
            krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
            source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm),
            Tracked(peer_thread_lock_perm), result, fill, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows),
            Tracked(target_windows), Ghost(channel_index), Ghost(waiting_state), Ghost(start), Ghost(pre),
        );
    }
    proof {
        assert_maps_equal!(lctx.pagetable_lock_map(), old(lctx).pagetable_lock_map(), p => {});
        assert_maps_equal!(lctx.pagetable_window_lock_map(), old(lctx).pagetable_window_lock_map(), p => {});
    }
    result
}

/// Enters a pages rendezvous, locks both page tables, checks and shares the pages, and releases both page
/// tables with the check result.
fn ipc_map_pages_and_release_tables(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, current_thread_lock_perm: Tracked<&LockPerm>, peer_thread_lock_perm: Tracked<&LockPerm>,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot,
    Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().ipc_partner is None,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        source_process != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        (waiting_state is SENDING) == (source_thread == current_thread_ptr),
        edp_idx_valid(channel_index),
        waiting_state is SENDING || waiting_state is RECEIVING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (IPCPayLoad::Pages { va_range: if waiting_state is SENDING { *target_range } else { *source_range } }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret is Success || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 4 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 4,
        !(ret is Success) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 3,
        ipc_pages_mapping_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id,
            channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }, ret),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        current_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        peer_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)] t == source_thread || t == target_thread ==> {
            &&& final(krnl).thr_mp.dom().contains(t)
            &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
            &&& final(krnl).thr_mp.spec_index(t).view().state == old(krnl).thr_mp.spec_index(t).view().state
            &&& final(krnl).thr_mp.spec_index(t).view().owning_proc == old(krnl).thr_mp.spec_index(t).view().owning_proc
            &&& final(krnl).thr_mp.spec_index(t).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& final(krnl).thr_mp.spec_index(t).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(t).view().temp_alloc_clean()
        },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: Some(ret),
        }),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
{
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();
    let ghost range = if waiting_state is SENDING { *source_range } else { *target_range };
    proof {
        let pre_k = old(steps).snapshot_k();
        assert({
            let cpu = pre_k.cpu_arr.spec_index(cpu_id).value;
            let caller = pre_k.thr_mp.spec_index(current_thread_ptr);
            let peer = pre_k.thr_mp.spec_index(peer_thread_ptr);
            let channel = pre_k.ep_mp.spec_index(endpoint_ptr);
            &&& cpu.locking_thread() is None
            &&& cpu.view().view().state is Running
            &&& cpu.view().view().current_process == Some(process_ptr)
            &&& cpu.view().view().current_thread == Some(current_thread_ptr)
            &&& pre_k.prc_mp.dom().contains(process_ptr)
            &&& pre_k.thr_mp.dom().contains(current_thread_ptr)
            &&& pre_k.thr_mp.dom().contains(peer_thread_ptr)
            &&& pre_k.ep_mp.dom().contains(endpoint_ptr)
            &&& caller.locking_thread() is None
            &&& caller.view().syscall_progress.view() is None
            &&& !caller.being_killed()
            &&& caller.view().state == (ThreadState::RUNNING { cpu_id })
            &&& caller.view().owning_proc == process_ptr
            &&& pre_k.ctn_mp.dom().contains(caller.view().owning_container)
            &&& caller.view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()
            &&& channel.locking_thread() is None
            &&& !channel.view().queue.view().contains(current_thread_ptr)
            &&& channel.view().queue.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view()
            &&& channel.view().queue_state == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state
            &&& peer.locking_thread() is None
            &&& !peer.being_killed()
            &&& peer.view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state
            &&& peer.view().blocking_endpoint_ptr == Some(endpoint_ptr)
            &&& pre_k.ctn_mp.dom().contains(peer.view().owning_container)
            &&& peer.view().ipc_payload == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
            &&& peer.view().owning_proc == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_proc
        }) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            running_thread_not_in_endpoint_queue(old(krnl), endpoint_ptr, current_thread_ptr);
            container_thread_wf_at(old(krnl).ctn_mp, old(krnl).thr_mp, current_thread_ptr); container_thread_wf_at(old(krnl).ctn_mp, old(krnl).thr_mp, peer_thread_ptr);
        };
        endpoint_perms_wf_at(old(krnl).ep_mp, endpoint_ptr); old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.lemma_len_view();
        ipc_pages_enter_step_pre_from_k(&pre_k, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, channel_index, waiting_state, range,
            if waiting_state is SENDING { *target_range } else { *source_range });
        krnl.set_thread_ipc_partner(peer_thread_ptr, Some(current_thread_ptr), &*lctx);
    }
    let ghost partnered_k = *krnl;
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::IpcPages {
        source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: None,
    })), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        assert({
            &&& steps.snapshot_k().thr_mp.dom().contains(current_thread_ptr)
            &&& steps.snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None
            &&& ipc_pages_enter_step(kernel_k_to_kernel_u(steps.snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, range)
        }) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            reveal(kernel_thread_nonlock_fields_unchanged);
            kernel_cpu_and_two_threads_lock_modes_changed_implies_u_step(&steps.snapshot_k(), old(krnl), old(lctx), cpu_id, current_thread_ptr, peer_thread_ptr, endpoint_ptr, None);
            kernel_thread_ghost_changed_implies_u_eq(old(krnl), &partnered_k, peer_thread_ptr);
            kernel_thread_syscall_progress_changed_implies_u_step(&partnered_k, &*krnl, current_thread_ptr);
            ipc_pages_enter_step_from_u(kernel_k_to_kernel_u(steps.snapshot_k()), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
                channel_index, waiting_state, *source_range, *target_range);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        let ghost entered_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        assert(ipc_pages_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, channel_index, waiting_state, range)) by {
            ipc_pages_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, channel_index, waiting_state, range);
        };
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& !krnl.prc_mp.spec_index(source_process).view().zombie
            &&& !krnl.prc_mp.spec_index(target_process).view().zombie
            &&& krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable
            &&& krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable
            &&& krnl.pt_mp.dom().contains(source_pagetable)
            &&& krnl.pt_mp.dom().contains(target_pagetable)
            &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process
            &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
            &&& source_pagetable != target_pagetable
        }) by {
            process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
            process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        };
    }
    ipc_lock_tables_and_share_pages(
        krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
        Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm), Tracked(peer_thread_lock_perm), source_process, source_container,
        source_pagetable, target_process, target_container, target_pagetable, Ghost(channel_index), Ghost(waiting_state), Ghost(old(steps).view().len() as int),
        Ghost(kernel_k_to_kernel_u(old(steps).snapshot_k())),
    )
}

pub(super) fn ipc_rendezvous_pages(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<LockPerm>, Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        (source_thread == current_thread_ptr) == (waiting_state is SENDING),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (IPCPayLoad::Pages { va_range: if source_thread == current_thread_ptr { *target_range } else { *source_range } }),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().ipc_partner is None,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_thread != target_thread,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
    ensures
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ipc_pages_rendezvous_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Success || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 5 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 5,
        ret is ErrorIpcSameProcess ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        !(ret is Success) && !(ret is ErrorIpcSameProcess) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 4,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    proof {
        assert({
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
        }) by { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); };
    }
    let source_thread_ref = krnl.thr_mp.borrow_typed(
        source_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(if source_thread == current_thread_ptr { &current_thread_lock_perm } else { &peer_thread_lock_perm }),
    );
    let (source_process, source_container, source_pagetable) = (source_thread_ref.owning_proc, source_thread_ref.owning_container, source_thread_ref.proc_pagetable_ptr);
    let target_thread_ref = krnl.thr_mp.borrow_typed(
        target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(if target_thread == current_thread_ptr { &current_thread_lock_perm } else { &peer_thread_lock_perm }),
    );
    let (target_process, target_container, target_pagetable) = (target_thread_ref.owning_proc, target_thread_ref.owning_container, target_thread_ref.proc_pagetable_ptr);
    if source_process == target_process {
        let ghost payload = IPCPayLoad::Pages { va_range: if waiting_state is SENDING { *source_range } else { *target_range } };
        proof {
            assert({
                let pre = steps.snapshot_k();
                &&& pre.thr_mp.dom().contains(current_thread_ptr) && pre.thr_mp.dom().contains(peer_thread_ptr) && pre.ep_mp.dom().contains(endpoint_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(current_thread_ptr)
                &&& pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr)
                &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == peer_thread_ptr
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().state == krnl.thr_mp.spec_index(peer_thread_ptr).view().state
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == krnl.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
                &&& pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().owning_proc == krnl.thr_mp.spec_index(peer_thread_ptr).view().owning_proc
            }) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                reveal(kernel_endpoint_nonlock_fields_unchanged);
            };
            ipc_rendezvous_result_from_k(&steps.snapshot_k(), cpu_id, channel_index, waiting_state, payload, current_thread_ptr, endpoint_ptr, peer_thread_ptr, RetValueType::ErrorIpcSameProcess);
        }
        let ret = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(Some((channel_index, waiting_state, payload))), false, peer_thread_ptr,
            RetValueType::ErrorIpcSameProcess, Tracked(cpu_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
        );
        proof { ipc_rendezvous_trace_error_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, payload, ret); }
        ret
    } else {
        let result = ipc_map_pages_and_release_tables(
            krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm), Tracked(&peer_thread_lock_perm),
            source_process, source_container, source_pagetable, target_process, target_container, target_pagetable, Ghost(channel_index), Ghost(waiting_state),
        );
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost finish_before = steps.view();
        let ghost finish_pre_u = kernel_k_to_kernel_u(*krnl);
        let ret = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(None), true, peer_thread_ptr,
            result, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
        proof {
            ipc_pages_rendezvous_trace_finish_step(&*steps, finish_before, old(steps).view().len() as int, kernel_k_to_kernel_u(old(steps).snapshot_k()), finish_pre_u, kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state,
                if waiting_state is SENDING { *source_range } else { *target_range }, result);
        }
        ret
    }
}
} // verus!

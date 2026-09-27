use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{ipc_dequeue_endpoint_waiter, ipc_enqueue_scheduled_thread, ipc_schedule_endpoint_waiter};
use super::syscall_ipc_cpu_spec::ipc_cpu_rendezvous_transition;
use super::syscall_ipc_cpu_eof::ipc_cpu_rendezvous_eof;
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;
use super::syscall_ipc_spec::*;

verus! {
    #[verifier::spinoff_prover]
    fn finish_ipc_cpu_rendezvous_release(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr, source_cpu_set: RwLockCpuSetPtr,
    target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
    Ghost(peer_result): Ghost<RetValueType>, Ghost(cpu_transfer): Ghost<Option<(CpuId, RwLockThreadPtr)>>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    Tracked(peer_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(source_cpu_set_lock_perm): Tracked<LockPerm>, Tracked(target_cpu_set_lock_perm): Tracked<LockPerm>, transfer_cpu_lock_perm: Option<Tracked<LockPerm>>,
    )
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, transfer_cpu_id),
            current_thread_ptr != peer_thread_ptr,
            old(krnl).cpu_published[cpu_id as int].view() == (
                    old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3,
                    old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid,
                ),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(peer_thread_ptr),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
            !(old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).sched_mp.dom().contains(peer_scheduler_ptr),
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), peer_scheduler_ptr, TypedLockMode::Write),
            peer_scheduler_lock_perm.state() is WriteLock,
            peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).locking_thread()->Write_lock_id,
            source_cpu_set != target_cpu_set,
            old(krnl).cpu_set_mp.dom().contains(source_cpu_set),
            typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), source_cpu_set, TypedLockMode::Write),
            source_cpu_set_lock_perm.state() is WriteLock,
            source_cpu_set_lock_perm.thread_id() == old(lctx).thread_id(),
            source_cpu_set_lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(source_cpu_set).locking_thread()->Write_lock_id,
            old(krnl).cpu_set_mp.dom().contains(target_cpu_set),
            typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), target_cpu_set, TypedLockMode::Write),
            target_cpu_set_lock_perm.state() is WriteLock,
            target_cpu_set_lock_perm.thread_id() == old(lctx).thread_id(),
            target_cpu_set_lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(target_cpu_set).locking_thread()->Write_lock_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= if transfer_cpu_lock_perm is Some { set![cpu_id, transfer_cpu_id] } else { set![cpu_id] },
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom()
                =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom() =~= set![peer_scheduler_ptr],
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom()
                =~= set![source_cpu_set, target_cpu_set],
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            kernel_ipc_rendezvous_fields(
                &old(steps).snapshot_k(), old(krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result,
                cpu_transfer,
            ),
            (transfer_cpu_lock_perm is Some) == (cpu_transfer is Some),
            transfer_cpu_lock_perm is Some ==> {
                let transfer_perm = transfer_cpu_lock_perm.unwrap().view();
                &&& transfer_cpu_id != cpu_id
                &&& typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), transfer_cpu_id, TypedLockMode::Write)
                &&& old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().being_killed() == false
                &&& transfer_perm.state() is WriteLock
                &&& transfer_perm.thread_id() == old(lctx).thread_id()
                &&& transfer_perm.lock_id() == old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().locking_thread()->Write_lock_id
                &&& old(krnl).cpu_published[transfer_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_pcid)
            },
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view(),
            final(krnl).thr_mp.spec_index(peer_thread_ptr).view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view(),
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            kernel_u_ipc_rendezvous_changed(
                final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, current_thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
            ),
    {
        if let Some(transfer_perm) = transfer_cpu_lock_perm {
            krnl.wunlock_cpu(transfer_cpu_id, Tracked(&mut *lctx), transfer_perm);
        }
        krnl.wunlock_cpu_set(target_cpu_set, Tracked(&mut *lctx), Tracked(target_cpu_set_lock_perm));
        krnl.wunlock_cpu_set(source_cpu_set, Tracked(&mut *lctx), Tracked(source_cpu_set_lock_perm));
        krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_ipc_rendezvous_fields(
                &steps.snapshot_k(), &*krnl, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result,
                cpu_transfer,
            )) by {
                broadcast use kernel_process_nonlock_fields_unchanged_transitive;
                reveal(kernel_ipc_rendezvous_fields); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            };
            steps.end_kernel_step_ipc_rendezvous(
                &*krnl, &*lctx, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
            );
        }
    }

    #[verifier::spinoff_prover]
    pub(super) fn ipc_rendezvous_cpu(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, Ghost(endpoint_index): Ghost<EndpointIdx>,
    Ghost(waiting_state): Ghost<ThreadState>, peer_thread_ptr: RwLockThreadPtr, is_send: bool, transfer_cpu_id: CpuId,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            index_valid(NUM_CPUS, transfer_cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            current_thread_ptr != peer_thread_ptr,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(peer_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
            edp_idx_valid(endpoint_index),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
            waiting_state is SENDING || waiting_state is RECEIVING,
            (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret is Success || ret is SuccessUsize || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff,
            ret is Success ==> is_send,
            ret is SuccessUsize ==> !is_send && ret->SuccessUsize_value == transfer_cpu_id,
            ret is Success || ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off,
            ret is Success ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container,
            ret is Success || ret is SuccessUsize ==> final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SCHEDULED,
            ret is Success || ret is SuccessUsize ==> final(krnl).thr_mp.spec_index(peer_thread_ptr).view().error_code == Some(if is_send { RetValueType::SuccessUsize { value: transfer_cpu_id } } else { RetValueType::Success }),
            ret is Success ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container != old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container != old(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_container,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            kernel_u_ipc_rendezvous_changed(
                final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, current_thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, peer_thread_ptr,
                if ret is Success { RetValueType::SuccessUsize { value: transfer_cpu_id } } else if ret is SuccessUsize { RetValueType::Success } else { ret },
                if ret is Success || ret is SuccessUsize { Some((transfer_cpu_id, if is_send { peer_thread_ptr } else { current_thread_ptr })) } else { None },
            ),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {

        proof {
            assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(peer_thread_ptr).is_init() && krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            ) by { thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); };
        }
        assert(krnl.cpu_arr.inv()) by { reveal(cpu_array_wf); };
        let current_container = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container;
        let peer_container = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm)).owning_container;
        let source_container = if is_send { current_container } else { peer_container };
        let target_container = if !is_send { current_container } else { peer_container };
        if source_container == target_container {
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            return ipc_schedule_waiting_peer_and_finish(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr,
                Ghost(Some((endpoint_index, waiting_state))), peer_thread_ptr, RetValueType::ErrorIpcSameContainer, Tracked(cpu_lock_perm),
                Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
            );
        }
        proof {
            assert({
                &&& krnl.ctn_mp.dom().contains(source_container)
                &&& krnl.ctn_mp.dom().contains(target_container)
                &&& krnl.ctn_mp.view().spec_index(source_container).is_init()
                &&& krnl.ctn_mp.view().spec_index(source_container).addr() == source_container
                &&& krnl.ctn_mp.view().spec_index(target_container).is_init()
                &&& krnl.ctn_mp.view().spec_index(target_container).addr() == target_container
            }) by { reveal(container_thread_wf); container_perms_wf_at(krnl.ctn_mp, source_container); container_perms_wf_at(krnl.ctn_mp, target_container); };
        }
        let source_cpu_set = krnl.ctn_mp.borrow_rodata(source_container).borrow().cpu_set;
        let target_cpu_set = krnl.ctn_mp.borrow_rodata(target_container).borrow().cpu_set;
        let target_container_depth = krnl.ctn_mp.borrow_rodata(target_container).borrow().depth;
        let peer_scheduler_ptr = krnl.ctn_mp.borrow_rodata(peer_container).borrow().scheduler;
        proof {
            assert({
                &&& krnl.cpu_set_mp.dom().contains(source_cpu_set)
                &&& krnl.cpu_set_mp.dom().contains(target_cpu_set)
                &&& source_cpu_set != target_cpu_set
                &&& !lctx.cpu_set_lock_map().dom().contains(source_cpu_set)
                &&& !lctx.cpu_set_lock_map().dom().contains(target_cpu_set)
            }) by { reveal(container_cpu_set_wf); };
        }
        proof {
            assert({
                &&& krnl.sched_mp.dom().contains(peer_scheduler_ptr)
                &&& !lctx.scheduler_lock_map().dom().contains(peer_scheduler_ptr)
                &&& krnl.ctn_mp.dom().contains(peer_container)
                &&& krnl.ctn_mp.spec_index(peer_container).view_rodata().view().scheduler == peer_scheduler_ptr
                &&& krnl.sched_mp.spec_index(peer_scheduler_ptr).view().owning_container == peer_container
                &&& !krnl.sched_mp.spec_index(peer_scheduler_ptr).view().queue.view().contains(peer_thread_ptr)
            }) by { reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
            assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
        }
        assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).view().queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr); };
        let (first_cpu_set, second_cpu_set) = if source_cpu_set < target_cpu_set { (source_cpu_set, target_cpu_set) } else { (target_cpu_set, source_cpu_set) };
        let first_perm = krnl.wlock_cpu_set(first_cpu_set, Tracked(&mut *lctx));
        let second_perm = krnl.wlock_cpu_set(second_cpu_set, Tracked(&mut *lctx));
        let (Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm)) = if source_cpu_set < target_cpu_set { (first_perm, second_perm) } else { (second_perm, first_perm) };

        let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx));
        let source_set = krnl.cpu_set_mp.borrow_typed(source_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&source_cpu_set_lock_perm));
        let result = if !source_set.owned_cpus.contains(transfer_cpu_id) {
            RetValueType::ErrorIpcCpuOwnerMismatch
        } else if !source_set.owned_cpus.is_closed(transfer_cpu_id) {
            RetValueType::ErrorIpcCpuNotOff
        } else { RetValueType::Success };
        let mut transfer_cpu_lock_perm: Option<Tracked<LockPerm>> = None;
        if let RetValueType::Success = result {
            proof {
                assert({
                    &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
                    &&& transfer_cpu_id != cpu_id
                    &&& !lctx.cpu_lock_map().dom().contains(transfer_cpu_id)
                    &&& !krnl.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
                    &&& krnl.cpu_set_mp.spec_index(target_cpu_set).inv()
                }) by { reveal(container_cpu_wf); reveal(cpu_array_wf); };
            }
            proof { assert(old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container) by { reveal(container_cpu_wf); }; }
            let transfer_perm = krnl.wlock_off_cpu(transfer_cpu_id, source_cpu_set, Tracked(&mut *lctx));
            transfer_cpu_lock_perm = Some(transfer_perm);
        }
        let peer_result = if let RetValueType::Success = result {
            if is_send { RetValueType::SuccessUsize { value: transfer_cpu_id } } else { RetValueType::Success }
        } else { result };
        let caller_result = if let RetValueType::Success = result {
            if !is_send { RetValueType::SuccessUsize { value: transfer_cpu_id } } else { RetValueType::Success }
        } else { result };
        let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
        let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, peer_thread_ptr, Tracked(&endpoint_lock_perm));
        proof {
            assert({
                let peer_node_addr = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr();
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(peer_node_addr)
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thread_ptr
                &&& endpoint_node_perm.addr() == peer_node_addr
            }) by { reveal(thread_endpoint_queue_wf); endpoint_perms_wf_at(old(krnl).ep_mp, endpoint_ptr); reveal(LinkedList::wf_map); };
        }
        let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_waiter(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, current_thread_ptr, peer_result, Tracked(endpoint_node_perm), Tracked(&peer_thread_lock_perm));
        ipc_enqueue_scheduled_thread(&mut krnl.sched_mp, Tracked(&*lctx), peer_scheduler_ptr, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&peer_scheduler_lock_perm));
        if transfer_cpu_lock_perm.is_some() {
            let transfer_perm = transfer_cpu_lock_perm.as_ref().unwrap();
            {
                let source_set = krnl.cpu_set_mp.borrow_mut_typed(source_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&source_cpu_set_lock_perm));
                source_set.owned_cpus.remove(transfer_cpu_id);
                let target_set = krnl.cpu_set_mp.borrow_mut_typed(target_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&target_cpu_set_lock_perm));
                target_set.owned_cpus.insert_closed(transfer_cpu_id);
                let transfer_cpu = krnl.cpu_arr.borrow_mut_typed(transfer_cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&transfer_perm.borrow()));
                transfer_cpu.transfer_off_cpu_to_container(target_container, target_container_depth);
            }
        }
        let ghost cpu_transfer: Option<(CpuId, RwLockThreadPtr)> = if result is Success {
            Some((transfer_cpu_id, if is_send { peer_thread_ptr } else { current_thread_ptr }))
        } else { None };
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
            assert(ipc_cpu_rendezvous_transition(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr,
                source_container, target_container, source_cpu_set, target_cpu_set,
                transfer_cpu_id, result is Success, peer_result, lctx.thread_id(),
            )) by { reveal(ipc_cpu_rendezvous_transition); };
            ipc_cpu_rendezvous_eof(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr,
                source_container, target_container, source_cpu_set, target_cpu_set,
                transfer_cpu_id, result is Success, peer_result, lctx.thread_id(), steps.snapshot_k(), cpu_id, process_ptr, endpoint_index,
                waiting_state, cpu_transfer,
            );
        }
        finish_ipc_cpu_rendezvous_release(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            peer_scheduler_ptr, source_cpu_set, target_cpu_set, transfer_cpu_id, Ghost(endpoint_index), Ghost(waiting_state), Ghost(peer_result),
            Ghost(cpu_transfer), Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm), Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm),
            transfer_cpu_lock_perm,
        );
        caller_result
    }
}

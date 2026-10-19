use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{ipc_dequeue_endpoint_waiter, ipc_schedule_endpoint_waiter};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_cpu_spec::ipc_cpu_rendezvous_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_cpu_eof::ipc_cpu_rendezvous_eof;
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
    #[verifier::spinoff_prover]
    fn finish_ipc_cpu_rendezvous_release(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_cpu_set: RwLockCpuSetPtr,
        target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
        Ghost(peer_result): Ghost<RetValueType>, Ghost(cpu_transfer): Ghost<Option<(CpuId, RwLockThreadPtr)>>, Ghost(payload): Ghost<IPCPayLoad>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
        Tracked(peer_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
        Tracked(source_cpu_set_lock_perm): Tracked<LockPerm>, Tracked(target_cpu_set_lock_perm): Tracked<LockPerm>, transfer_cpu_lock_perm: Option<Tracked<LockPerm>>,
        Ghost(source_container): Ghost<RwLockContainerPtr>, Ghost(target_container): Ghost<RwLockContainerPtr>, Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
    )
        requires
            old(krnl).inv(),
            forall|p: RwLockContainerPtr| #![trigger entry_k.ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && entry_k.ctn_mp.dom().contains(p) ==> if entry_lctx.container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { entry_k.ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
            forall|p: RwLockProcessPtr| #![trigger entry_k.prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && entry_k.prc_mp.dom().contains(p) ==> if entry_lctx.process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { entry_k.prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger entry_k.thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
                old(steps).snapshot_k().thr_mp.dom().contains(p) && entry_k.thr_mp.dom().contains(p) ==> if entry_lctx.thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
                } else { entry_k.thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger entry_k.ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && entry_k.ep_mp.dom().contains(p) ==> if entry_lctx.endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { entry_k.ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger entry_k.pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && entry_k.pt_mp.dom().contains(p) ==> if entry_lctx.pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { entry_k.pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger entry_k.it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
                old(steps).snapshot_k().it_mp.dom().contains(p) && entry_k.it_mp.dom().contains(p) ==> if entry_lctx.iommu_table_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
                } else { entry_k.it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
            forall|i: CpuId| #![trigger entry_k.cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> if entry_lctx.cpu_lock_map().dom().contains(i) {
                    old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
                } else { entry_k.cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, transfer_cpu_id),
            current_thread_ptr != peer_thread_ptr,
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is KILLED),
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
            !(old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is KILLED),
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
            index_valid(NUM_CPUS, wake_cpu),
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_scheduler_ptr, wake_cpu), TypedLockMode::Write),
            peer_scheduler_lock_perm.state() is WriteLock,
            peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
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
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom() =~= set![(peer_scheduler_ptr, wake_cpu)],
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom() =~= set![source_cpu_set, target_cpu_set],
            old(lctx).pagetable_lock_map().dom().is_empty(),
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
            entry_lctx.container_lock_map().dom().is_empty(),
            entry_lctx.process_lock_map().dom().is_empty(),
            entry_lctx.thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            entry_lctx.endpoint_lock_map().dom() =~= set![endpoint_ptr],
            entry_lctx.pagetable_lock_map().dom().is_empty(),
            entry_lctx.iommu_table_lock_map().dom().is_empty(),
            entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
            entry_k.cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            entry_k.cpu_set_mp.spec_index(source_cpu_set).locking_thread() is None,
            entry_k.cpu_set_mp.spec_index(target_cpu_set).locking_thread() is None,
            cpu_transfer is Some ==> entry_k.cpu_arr.spec_index(transfer_cpu_id).value.locking_thread() is None,
            ipc_cpu_rendezvous_eof_transition_framing(
                entry_k, *old(krnl), current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set,
                transfer_cpu_id, cpu_transfer is Some, peer_result, old(lctx).thread_id(),
            ),
            ({
                let snap = old(steps).snapshot_k();
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(current_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
            }),
            kernel_ipc_rendezvous_fields(&old(steps).snapshot_k(), old(krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, None),
            ({
                let result = ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload);
                &&& peer_result == ipc_peer_result(payload, result)
                &&& cpu_transfer == ipc_cpu_transfer(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, payload, result)
            }),
            payload is Cpu || payload is ReceiveCpu,
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
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
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
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            ipc_rendezvous_result(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload) == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload),
    {
        unlock_ipc_cpu_rendezvous_locks(
            krnl, Tracked(&mut *lctx), cpu_id, current_thread_ptr, endpoint_ptr, peer_thread_ptr, peer_scheduler_ptr, wake_cpu, source_cpu_set, target_cpu_set, transfer_cpu_id,
            Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm),
            Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm), transfer_cpu_lock_perm,
        );
        proof {
            assert(kernel_ipc_rendezvous_fields(&steps.snapshot_k(), &*krnl, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, None)) by { reveal(kernel_ipc_rendezvous_fields); };
            reveal(ipc_cpu_rendezvous_eof_transition_framing);
            steps.end_kernel_step_ipc_rendezvous(&*krnl, &*lctx, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, None, payload, true);
            assert({
                &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step_pre(steps.nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload)
            }) by {
                ipc_rendezvous_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, None, payload, true);
                ipc_rendezvous_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state,
                    peer_thread_ptr, peer_result, cpu_transfer, None, payload, true);
            };
        }
    }

    /// Releases every lock held by the CPU-payload rendezvous; only lock states move, and exactly the held ones become unlocked.
    fn unlock_ipc_cpu_rendezvous_locks(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
        transfer_cpu_id: CpuId, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
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
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is KILLED),
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
            !(old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is KILLED),
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
            index_valid(NUM_CPUS, wake_cpu),
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_scheduler_ptr, wake_cpu), TypedLockMode::Write),
            peer_scheduler_lock_perm.state() is WriteLock,
            peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
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
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom() =~= set![(peer_scheduler_ptr, wake_cpu)],
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom() =~= set![source_cpu_set, target_cpu_set],
            old(lctx).pagetable_lock_map().dom().is_empty(),
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
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_set_mp: final(krnl).cpu_set_mp, thr_mp: final(krnl).thr_mp, sched_mp: final(krnl).sched_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
            forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) ==> {
                &&& final(krnl).cpu_arr.spec_index(i).value.view() == old(krnl).cpu_arr.spec_index(i).value.view()
                &&& final(krnl).cpu_arr.spec_index(i).value.killer_info() == old(krnl).cpu_arr.spec_index(i).value.killer_info()
                &&& final(krnl).cpu_arr.spec_index(i).value.locking_thread() == if old(lctx).cpu_lock_map().dom().contains(i) { RwLockState::None } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() }
            },
            final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
            forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)] old(krnl).thr_mp.dom().contains(t) ==> {
                &&& final(krnl).thr_mp.spec_index(t).view() == old(krnl).thr_mp.spec_index(t).view()
                &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
                &&& final(krnl).thr_mp.spec_index(t).locking_thread() == if old(lctx).thread_lock_map().dom().contains(t) { RwLockState::None } else { old(krnl).thr_mp.spec_index(t).locking_thread() }
            },
            final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom(),
            forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)] old(krnl).ep_mp.dom().contains(e) ==> {
                &&& final(krnl).ep_mp.spec_index(e).view() == old(krnl).ep_mp.spec_index(e).view()
                &&& final(krnl).ep_mp.spec_index(e).being_killed() == old(krnl).ep_mp.spec_index(e).being_killed()
                &&& final(krnl).ep_mp.spec_index(e).locking_thread() == if old(lctx).endpoint_lock_map().dom().contains(e) { RwLockState::None } else { old(krnl).ep_mp.spec_index(e).locking_thread() }
            },
            final(krnl).cpu_set_mp.dom() == old(krnl).cpu_set_mp.dom(),
            forall|p: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(p)] old(krnl).cpu_set_mp.dom().contains(p) ==>
                final(krnl).cpu_set_mp.spec_index(p).locking_thread() == if old(lctx).cpu_set_lock_map().dom().contains(p) { RwLockState::None } else { old(krnl).cpu_set_mp.spec_index(p).locking_thread() },
            forall|c: RwLockContainerPtr| #![trigger final(krnl).sched_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().scheduler)]
                old(krnl).ctn_mp.dom().contains(c) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().scheduler))
                    == scheduler_shards_of(old(krnl).sched_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().scheduler)),
    {
        if let Some(transfer_perm) = transfer_cpu_lock_perm { krnl.wunlock_cpu(transfer_cpu_id, Tracked(&mut *lctx), transfer_perm); }
        krnl.wunlock_cpu_set(target_cpu_set, Tracked(&mut *lctx), Tracked(target_cpu_set_lock_perm));
        krnl.wunlock_cpu_set(source_cpu_set, Tracked(&mut *lctx), Tracked(source_cpu_set_lock_perm));
        krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }
    }

    /// When `transfer` holds, write-locks the closed transfer CPU and moves it from the source CPU set into the target container's CPU set;
    /// otherwise leaves the kernel and the lock context unchanged.
    fn ipc_transfer_closed_cpu(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, transfer: bool, transfer_cpu_id: CpuId, source_cpu_set: RwLockCpuSetPtr,
        target_cpu_set: RwLockCpuSetPtr, target_container: RwLockContainerPtr, target_container_depth: usize,
        Tracked(source_cpu_set_lock_perm): Tracked<&LockPerm>, Tracked(target_cpu_set_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, transfer_cpu_id),
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
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            transfer ==> !old(lctx).cpu_lock_map().dom().contains(transfer_cpu_id),
            transfer ==> old(krnl).cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
            transfer ==> !old(krnl).cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id),
        ensures
            (ret is Some) == transfer,
            !transfer ==> *final(krnl) == *old(krnl) && *final(lctx) == *old(lctx),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            transfer ==> typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Cpu(transfer_cpu_id), TypedHeldLock { lock_id: final(krnl).cpu_arr.lock_id_by_index(transfer_cpu_id), mode: TypedLockMode::Write }),
            transfer ==> {
                let transfer_perm = ret->Some_0.view();
                &&& old(krnl).cpu_arr.spec_index(transfer_cpu_id).value.locking_thread() is None
                &&& transfer_perm.state() is WriteLock
                &&& transfer_perm.thread_id() == old(lctx).thread_id()
                &&& transfer_perm.lock_id() == final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().locking_thread()->Write_lock_id
                &&& final(krnl).cpu_published[transfer_cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_pcid)
            },
            final(krnl).cpu_arr.inv(),
            final(krnl).cpu_arr.view().len() == old(krnl).cpu_arr.view().len(),
            forall|cpu_i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(cpu_i)] #![trigger final(krnl).cpu_arr.spec_index(cpu_i)]
                index_valid(NUM_CPUS, cpu_i) && (!transfer || cpu_i != transfer_cpu_id) ==> final(krnl).cpu_arr.spec_index(cpu_i) == old(krnl).cpu_arr.spec_index(cpu_i),
            transfer ==> {
                let before = old(krnl).cpu_arr.spec_index(transfer_cpu_id).view();
                let after = final(krnl).cpu_arr.spec_index(transfer_cpu_id).view();
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed() && !after.being_killed()
                &&& after.locking_thread() is Write
                &&& after.locking_thread()->Write_thread_id == old(lctx).thread_id()
                &&& after.view().view() == CpuView { owning_container: target_container, container_depth: target_container_depth, ..before.view().view() }
                &&& after.view().wf()
            },
            final(krnl).cpu_set_mp.perms_wf(),
            final(krnl).cpu_set_mp.dom() == old(krnl).cpu_set_mp.dom(),
            final(krnl).cpu_set_mp.spec_index(source_cpu_set).locking_thread() == old(krnl).cpu_set_mp.spec_index(source_cpu_set).locking_thread(),
            final(krnl).cpu_set_mp.spec_index(target_cpu_set).locking_thread() == old(krnl).cpu_set_mp.spec_index(target_cpu_set).locking_thread(),
            final(krnl).cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.wf(),
            final(krnl).cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.wf(),
            forall|key: RwLockCpuSetPtr| #![trigger old(krnl).cpu_set_mp.spec_index(key)] #![trigger final(krnl).cpu_set_mp.spec_index(key)]
                old(krnl).cpu_set_mp.dom().contains(key) && key != source_cpu_set && key != target_cpu_set ==> final(krnl).cpu_set_mp.spec_index(key) == old(krnl).cpu_set_mp.spec_index(key),
            ({
                let before = old(krnl).cpu_set_mp.spec_index(source_cpu_set);
                let after = final(krnl).cpu_set_mp.spec_index(source_cpu_set);
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& transfer ==> {
                    &&& after.view().owned_cpus.view() == before.view().owned_cpus.view().remove(transfer_cpu_id)
                    &&& after.view().owned_cpus.closed_view() == before.view().owned_cpus.closed_view().remove(transfer_cpu_id)
                    &&& after.view().owned_cpus.data.view() == before.view().owned_cpus.data.view().update(transfer_cpu_id as int, false)
                    &&& after.view().owned_cpus.closed.view() == before.view().owned_cpus.closed.view().update(transfer_cpu_id as int, false)
                    &&& after.view().owned_cpus.len as int == before.view().owned_cpus.len as int - 1
                }
            }),
            ({
                let before = old(krnl).cpu_set_mp.spec_index(target_cpu_set);
                let after = final(krnl).cpu_set_mp.spec_index(target_cpu_set);
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& transfer ==> {
                    &&& after.view().owned_cpus.view() == before.view().owned_cpus.view().insert(transfer_cpu_id)
                    &&& after.view().owned_cpus.closed_view() == before.view().owned_cpus.closed_view().insert(transfer_cpu_id)
                    &&& after.view().owned_cpus.data.view() == before.view().owned_cpus.data.view().update(transfer_cpu_id as int, true)
                    &&& after.view().owned_cpus.closed.view() == before.view().owned_cpus.closed.view().update(transfer_cpu_id as int, true)
                    &&& after.view().owned_cpus.len as int == before.view().owned_cpus.len as int + 1
                }
            }),
    {
        proof {
            assert(krnl.cpu_arr.inv() && krnl.cpu_set_mp.perms_wf() && krnl.cpu_set_mp.spec_index(source_cpu_set).inv() && krnl.cpu_set_mp.spec_index(target_cpu_set).inv()) by {
                cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view());
                cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), transfer_cpu_id); cpu_set_perms_wf_map(krnl.cpu_set_mp); cpu_set_perms_wf_at(krnl.cpu_set_mp, source_cpu_set); cpu_set_perms_wf_at(krnl.cpu_set_mp, target_cpu_set);
            };
        }
        if !transfer { return None; }
        let transfer_perm = krnl.wlock_off_cpu(transfer_cpu_id, source_cpu_set, Tracked(&mut *lctx));
        let source_set = krnl.cpu_set_mp.borrow_mut_typed(source_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(source_cpu_set_lock_perm));
        source_set.owned_cpus.remove(transfer_cpu_id);
        let target_set = krnl.cpu_set_mp.borrow_mut_typed(target_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(target_cpu_set_lock_perm));
        target_set.owned_cpus.insert_closed(transfer_cpu_id);
        let transfer_cpu = krnl.cpu_arr.borrow_mut_typed(transfer_cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&transfer_perm.borrow()));
        transfer_cpu.transfer_off_cpu_to_container(target_container, target_container_depth);
        Some(transfer_perm)
    }

    /// Write-locks the source and target CPU sets in address order and the peer's scheduler shard, checks that
    /// `transfer_cpu_id` is a closed CPU of the source container, and on success moves it into the target container.
    fn ipc_lock_cpu_sets_and_transfer_cpu(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
        source_container: RwLockContainerPtr, target_container: RwLockContainerPtr, target_container_depth: usize, source_cpu_set: RwLockCpuSetPtr,
        target_cpu_set: RwLockCpuSetPtr, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, transfer_cpu_id: CpuId,
    ) -> (ret: (RetValueType, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Option<Tracked<LockPerm>>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, wake_cpu),
            index_valid(NUM_CPUS, transfer_cpu_id),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
            old(krnl).ctn_mp.dom().contains(source_container),
            old(krnl).ctn_mp.dom().contains(target_container),
            old(krnl).ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set,
            old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set,
            source_cpu_set != target_cpu_set,
            old(krnl).cpu_set_mp.dom().contains(source_cpu_set),
            old(krnl).cpu_set_mp.dom().contains(target_cpu_set),
            old(krnl).sched_mp.dom().contains(peer_scheduler_ptr),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_lock_map().dom() =~= if ret.4 is Some { set![cpu_id, transfer_cpu_id] } else { set![cpu_id] },
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(lctx).cpu_set_lock_map().dom() =~= set![source_cpu_set, target_cpu_set],
            typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), source_cpu_set, TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), target_cpu_set, TypedLockMode::Write),
            final(lctx).scheduler_lock_map().dom() =~= set![(peer_scheduler_ptr, wake_cpu)],
            typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (peer_scheduler_ptr, wake_cpu), TypedLockMode::Write),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_set_mp: final(krnl).cpu_set_mp, sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
            ({
                let transfer_cpu = old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view();
                &&& ret.0 == if transfer_cpu.owning_container != source_container { RetValueType::ErrorIpcCpuOwnerMismatch }
                    else if !(transfer_cpu.state is Off) { RetValueType::ErrorIpcCpuNotOff } else { RetValueType::Success }
            }),
            ret.0 is Success ==> {
                &&& transfer_cpu_id != cpu_id
                &&& old(krnl).cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
                &&& old(krnl).cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
                &&& !old(krnl).cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            },
            (ret.4 is Some) == (ret.0 is Success),
            ret.4 is Some ==> {
                let transfer_perm = ret.4.unwrap().view();
                &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), transfer_cpu_id, TypedLockMode::Write)
                &&& old(krnl).cpu_arr.spec_index(transfer_cpu_id).value.locking_thread() is None
                &&& transfer_perm.state() is WriteLock
                &&& transfer_perm.thread_id() == old(lctx).thread_id()
                &&& transfer_perm.lock_id() == final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().locking_thread()->Write_lock_id
                &&& final(krnl).cpu_published[transfer_cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_pcid)
            },
            final(krnl).cpu_arr.inv(),
            final(krnl).cpu_arr.view().len() == old(krnl).cpu_arr.view().len(),
            forall|cpu_i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(cpu_i)] #![trigger final(krnl).cpu_arr.spec_index(cpu_i)]
                index_valid(NUM_CPUS, cpu_i) && (!(ret.0 is Success) || cpu_i != transfer_cpu_id) ==> final(krnl).cpu_arr.spec_index(cpu_i) == old(krnl).cpu_arr.spec_index(cpu_i),
            ret.0 is Success ==> {
                let before = old(krnl).cpu_arr.spec_index(transfer_cpu_id).view();
                let after = final(krnl).cpu_arr.spec_index(transfer_cpu_id).view();
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed() && !after.being_killed()
                &&& after.locking_thread() is Write
                &&& after.locking_thread()->Write_thread_id == old(lctx).thread_id()
                &&& after.view().view() == CpuView { owning_container: target_container, container_depth: target_container_depth, ..before.view().view() }
                &&& after.view().wf()
            },
            final(krnl).cpu_set_mp.perms_wf(),
            final(krnl).cpu_set_mp.dom() == old(krnl).cpu_set_mp.dom(),
            forall|key: RwLockCpuSetPtr| #![trigger old(krnl).cpu_set_mp.spec_index(key)] #![trigger final(krnl).cpu_set_mp.spec_index(key)]
                old(krnl).cpu_set_mp.dom().contains(key) && key != source_cpu_set && key != target_cpu_set ==> final(krnl).cpu_set_mp.spec_index(key) == old(krnl).cpu_set_mp.spec_index(key),
            ({
                let before = old(krnl).cpu_set_mp.spec_index(source_cpu_set);
                let after = final(krnl).cpu_set_mp.spec_index(source_cpu_set);
                &&& before.locking_thread() is None
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.locking_thread() is Write
                &&& after.locking_thread()->Write_thread_id == old(lctx).thread_id()
                &&& ret.1.view().state() is WriteLock
                &&& ret.1.view().thread_id() == old(lctx).thread_id()
                &&& ret.1.view().lock_id() == after.locking_thread()->Write_lock_id
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& after.view().owned_cpus.wf()
                &&& !(ret.0 is Success) ==> after.view().owned_cpus == before.view().owned_cpus
                &&& ret.0 is Success ==> {
                    &&& after.view().owned_cpus.view() == before.view().owned_cpus.view().remove(transfer_cpu_id)
                    &&& after.view().owned_cpus.closed_view() == before.view().owned_cpus.closed_view().remove(transfer_cpu_id)
                    &&& after.view().owned_cpus.data.view() == before.view().owned_cpus.data.view().update(transfer_cpu_id as int, false)
                    &&& after.view().owned_cpus.closed.view() == before.view().owned_cpus.closed.view().update(transfer_cpu_id as int, false)
                    &&& after.view().owned_cpus.len as int == before.view().owned_cpus.len as int - 1
                }
            }),
            ({
                let before = old(krnl).cpu_set_mp.spec_index(target_cpu_set);
                let after = final(krnl).cpu_set_mp.spec_index(target_cpu_set);
                &&& before.locking_thread() is None
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.locking_thread() is Write
                &&& after.locking_thread()->Write_thread_id == old(lctx).thread_id()
                &&& ret.2.view().state() is WriteLock
                &&& ret.2.view().thread_id() == old(lctx).thread_id()
                &&& ret.2.view().lock_id() == after.locking_thread()->Write_lock_id
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& after.view().owned_cpus.wf()
                &&& !(ret.0 is Success) ==> after.view().owned_cpus == before.view().owned_cpus
                &&& ret.0 is Success ==> {
                    &&& after.view().owned_cpus.view() == before.view().owned_cpus.view().insert(transfer_cpu_id)
                    &&& after.view().owned_cpus.closed_view() == before.view().owned_cpus.closed_view().insert(transfer_cpu_id)
                    &&& after.view().owned_cpus.data.view() == before.view().owned_cpus.data.view().update(transfer_cpu_id as int, true)
                    &&& after.view().owned_cpus.closed.view() == before.view().owned_cpus.closed.view().update(transfer_cpu_id as int, true)
                    &&& after.view().owned_cpus.len as int == before.view().owned_cpus.len as int + 1
                }
            }),
            scheduler_perms_wf(final(krnl).sched_mp),
            final(krnl).sched_mp.unchanged_except(&old(krnl).sched_mp, peer_scheduler_ptr),
            final(krnl).sched_mp.spec_index(peer_scheduler_ptr).inv(),
            final(krnl).sched_mp.spec_index(peer_scheduler_ptr).owning_container == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).owning_container,
            final(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.unchanged_except(&old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards, wake_cpu),
            final(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.lock_id_by_index(wake_cpu) == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.lock_id_by_index(wake_cpu),
            scheduler_shards_of(final(krnl).sched_mp.spec_index(peer_scheduler_ptr)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(peer_scheduler_ptr)),
            wlock_ensures(old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view(), final(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view(),
                old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.lock_id_by_index(wake_cpu), final(lctx), ret.3.view()),
    {
        hide(Seq::contains);
        let (first_cpu_set, second_cpu_set) = if source_cpu_set < target_cpu_set { (source_cpu_set, target_cpu_set) } else { (target_cpu_set, source_cpu_set) };
        let first_perm = krnl.wlock_cpu_set(first_cpu_set, Tracked(&mut *lctx));
        let second_perm = krnl.wlock_cpu_set(second_cpu_set, Tracked(&mut *lctx));
        let (Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm)) = if source_cpu_set < target_cpu_set { (first_perm, second_perm) } else { (second_perm, first_perm) };
        let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx));
        let source_set = krnl.cpu_set_mp.borrow_typed(source_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&source_cpu_set_lock_perm));
        let result = if !source_set.owned_cpus.contains(transfer_cpu_id) {
            RetValueType::ErrorIpcCpuOwnerMismatch
        } else if !source_set.owned_cpus.is_closed(transfer_cpu_id) {
            RetValueType::ErrorIpcCpuNotOff
        } else { RetValueType::Success };
        proof {
            assert({
                let transfer_cpu = old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view();
                &&& result == if transfer_cpu.owning_container != source_container { RetValueType::ErrorIpcCpuOwnerMismatch }
                    else if !(transfer_cpu.state is Off) { RetValueType::ErrorIpcCpuNotOff } else { RetValueType::Success }
                &&& result is Success ==> {
                    &&& transfer_cpu_id != cpu_id
                    &&& !lctx.cpu_lock_map().dom().contains(transfer_cpu_id)
                    &&& !krnl.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
                }
            }) by {
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, transfer_cpu_id); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, source_container, transfer_cpu_id);
                container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, target_container, transfer_cpu_id);
            };
        }
        let transfer_cpu_lock_perm = ipc_transfer_closed_cpu(
            krnl, Tracked(&mut *lctx), matches!(result, RetValueType::Success), transfer_cpu_id, source_cpu_set, target_cpu_set, target_container, target_container_depth,
            Tracked(&source_cpu_set_lock_perm), Tracked(&target_cpu_set_lock_perm),
        );
        (result, Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm), Tracked(peer_scheduler_lock_perm), transfer_cpu_lock_perm)
    }

    /// Cross-container path of `ipc_rendezvous_cpu`: locks both CPU sets and the peer scheduler shard, transfers the closed CPU on success,
    /// schedules the dequeued peer, and releases every lock.
    #[verifier::spinoff_prover]
    fn ipc_rendezvous_cpu_cross_container(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, Ghost(endpoint_index): Ghost<EndpointIdx>,
        Ghost(waiting_state): Ghost<ThreadState>, peer_thread_ptr: RwLockThreadPtr, is_send: bool, transfer_cpu_id: CpuId, Ghost(payload): Ghost<IPCPayLoad>,
        current_container: RwLockContainerPtr, peer_container: RwLockContainerPtr, wake_cpu: CpuId,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
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
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            index_valid(NUM_CPUS, transfer_cpu_id),
            is_send == (waiting_state is SENDING),
            payload == (if is_send { IPCPayLoad::Cpu { cpu_id: transfer_cpu_id } } else { IPCPayLoad::ReceiveCpu }),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            current_thread_ptr != peer_thread_ptr,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
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
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (if is_send { ThreadState::RECEIVING } else { ThreadState::SENDING }),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (if is_send { IPCPayLoad::ReceiveCpu } else { IPCPayLoad::Cpu { cpu_id: transfer_cpu_id } }),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
            edp_idx_valid(endpoint_index),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
            waiting_state is SENDING || waiting_state is RECEIVING,
            (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
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
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            current_container != peer_container,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == current_container,
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_container == peer_container,
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().last_cpu == wake_cpu,
            ({
                let pre = old(steps).snapshot_k();
                let transfer_cpu = old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view();
                &&& pre.thr_mp.dom().contains(current_thread_ptr) && pre.thr_mp.dom().contains(peer_thread_ptr) && pre.ep_mp.dom().contains(endpoint_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(current_thread_ptr)
                &&& pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
                &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == peer_thread_ptr
                &&& pre.thr_mp.spec_index(current_thread_ptr).view().owning_container == current_container
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container == peer_container
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
                &&& pre.cpu_arr.spec_index(transfer_cpu_id).value.view().view().owning_container == transfer_cpu.owning_container
                &&& pre.cpu_arr.spec_index(transfer_cpu_id).value.view().view().state == transfer_cpu.state
            }),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
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
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ret == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            ret == ipc_rendezvous_result(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {
        hide(Seq::contains);
        let source_container = if is_send { current_container } else { peer_container };
        let target_container = if !is_send { current_container } else { peer_container };
        proof {
            assert({
                &&& krnl.ctn_mp.dom().contains(source_container)
                &&& krnl.ctn_mp.dom().contains(target_container)
                &&& krnl.ctn_mp.view().spec_index(source_container).is_init()
                &&& krnl.ctn_mp.view().spec_index(source_container).addr() == source_container
                &&& krnl.ctn_mp.view().spec_index(target_container).is_init()
                &&& krnl.ctn_mp.view().spec_index(target_container).addr() == target_container
            }) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr); container_perms_wf_at(krnl.ctn_mp, source_container); container_perms_wf_at(krnl.ctn_mp, target_container); };
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
            }) by { container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, source_container); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, target_container); };
        }
        proof {
            assert({
                &&& krnl.sched_mp.dom().contains(peer_scheduler_ptr)
                &&& index_valid(NUM_CPUS, wake_cpu)
                &&& krnl.ctn_mp.dom().contains(peer_container)
                &&& krnl.ctn_mp.spec_index(peer_container).view_rodata().view().scheduler == peer_scheduler_ptr
                &&& krnl.sched_mp.spec_index(peer_scheduler_ptr).owning_container == peer_container
                &&& !krnl.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.view().contains(peer_thread_ptr)
            }) by {
                thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container);
                container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr);
            };
        }
        assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr, wake_cpu); };
        let (result, Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm), Tracked(peer_scheduler_lock_perm), transfer_cpu_lock_perm) = ipc_lock_cpu_sets_and_transfer_cpu(
            krnl, Tracked(&mut *lctx), cpu_id, current_thread_ptr, peer_thread_ptr, source_container, target_container, target_container_depth, source_cpu_set, target_cpu_set,
            peer_scheduler_ptr, wake_cpu, transfer_cpu_id,
        );
        let peer_result = if let RetValueType::Success = result { if is_send { RetValueType::SuccessUsize { value: transfer_cpu_id } } else { RetValueType::Success } } else { result };
        let caller_result = if let RetValueType::Success = result { if !is_send { RetValueType::SuccessUsize { value: transfer_cpu_id } } else { RetValueType::Success } } else { result };
        let ghost cpu_transfer: Option<(CpuId, RwLockThreadPtr)> = if result is Success { Some((transfer_cpu_id, if is_send { peer_thread_ptr } else { current_thread_ptr })) } else { None };
        proof { ipc_rendezvous_result_from_k(&steps.snapshot_k(), cpu_id, endpoint_index, waiting_state, payload, current_thread_ptr, endpoint_ptr, peer_thread_ptr, caller_result); }
        let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
        let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, peer_thread_ptr, Tracked(&endpoint_lock_perm));
        proof {
            assert({
                let peer_node_addr = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr();
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(peer_node_addr)
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thread_ptr
                &&& endpoint_node_perm.addr() == peer_node_addr
            }) by { thread_endpoint_queue_wf_thread_at(old(krnl).thr_mp, old(krnl).ep_mp, peer_thread_ptr); endpoint_perms_wf_at(old(krnl).ep_mp, endpoint_ptr); reveal(LinkedList::wf_map); };
        }
        let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_waiter(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, wake_cpu, current_thread_ptr, peer_result, Tracked(endpoint_node_perm), Tracked(&peer_thread_lock_perm));
        scheduler_map_enqueue_scheduled_thread(&mut krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&*lctx), Tracked(&peer_scheduler_lock_perm));
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
            scheduler_perms_wf_map(old(krnl).sched_mp); scheduler_perms_wf_at(old(krnl).sched_mp, peer_scheduler_ptr); scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, peer_scheduler_ptr);
            assert(ipc_cpu_rendezvous_eof_transition_framing(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu,
                source_container, target_container, source_cpu_set, target_cpu_set,
                transfer_cpu_id, result is Success, peer_result, lctx.thread_id(),
            )) by { reveal(ipc_cpu_rendezvous_eof_transition_framing); };
            ipc_cpu_rendezvous_eof(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu,
                source_container, target_container, source_cpu_set, target_cpu_set,
                transfer_cpu_id, result is Success, peer_result, lctx.thread_id(), steps.snapshot_k(), cpu_id, process_ptr, endpoint_index,
                waiting_state, cpu_transfer,
            );
            assert({
                let snap = steps.snapshot_k();
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(current_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
            }) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
        finish_ipc_cpu_rendezvous_release(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            peer_scheduler_ptr, wake_cpu, source_cpu_set, target_cpu_set, transfer_cpu_id, Ghost(endpoint_index), Ghost(waiting_state), Ghost(peer_result),
            Ghost(cpu_transfer), Ghost(payload), Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm), Tracked(source_cpu_set_lock_perm), Tracked(target_cpu_set_lock_perm),
            transfer_cpu_lock_perm, Ghost(source_container), Ghost(target_container), Ghost(*old(krnl)), Ghost(*old(lctx)),
        );
        caller_result
    }

    #[verifier::spinoff_prover]
    pub(super) fn ipc_rendezvous_cpu(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, Ghost(endpoint_index): Ghost<EndpointIdx>,
        Ghost(waiting_state): Ghost<ThreadState>, peer_thread_ptr: RwLockThreadPtr, is_send: bool, transfer_cpu_id: CpuId, Ghost(payload): Ghost<IPCPayLoad>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
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
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            index_valid(NUM_CPUS, transfer_cpu_id),
            is_send == (waiting_state is SENDING),
            payload == (if is_send { IPCPayLoad::Cpu { cpu_id: transfer_cpu_id } } else { IPCPayLoad::ReceiveCpu }),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            current_thread_ptr != peer_thread_ptr,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
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
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (if is_send { ThreadState::RECEIVING } else { ThreadState::SENDING }),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (if is_send { IPCPayLoad::ReceiveCpu } else { IPCPayLoad::Cpu { cpu_id: transfer_cpu_id } }),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
            edp_idx_valid(endpoint_index),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
            waiting_state is SENDING || waiting_state is RECEIVING,
            (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
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
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
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
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ret == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            ret == ipc_rendezvous_result(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {
        proof {
            assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(peer_thread_ptr).is_init() && krnl.thr_mp.spec_index(current_thread_ptr).is_init()) by {
                thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr);
            };
        }
        let current_container = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container;
        let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        let peer_container = peer_thread_ref.owning_container;
        let wake_cpu = peer_thread_ref.last_cpu;
        let source_container = if is_send { current_container } else { peer_container };
        let target_container = if !is_send { current_container } else { peer_container };
        proof {
            assert({
                let pre = steps.snapshot_k();
                let transfer_cpu = old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view();
                &&& pre.thr_mp.dom().contains(current_thread_ptr) && pre.thr_mp.dom().contains(peer_thread_ptr) && pre.ep_mp.dom().contains(endpoint_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(current_thread_ptr)
                &&& pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
                &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == peer_thread_ptr
                &&& pre.thr_mp.spec_index(current_thread_ptr).view().owning_container == current_container
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container == peer_container
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state
                &&& pre.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
                &&& pre.cpu_arr.spec_index(transfer_cpu_id).value.view().view().owning_container == transfer_cpu.owning_container
                &&& pre.cpu_arr.spec_index(transfer_cpu_id).value.view().view().state == transfer_cpu.state
            }) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            };
        }
        if source_container == target_container {
            proof { ipc_rendezvous_result_from_k(&steps.snapshot_k(), cpu_id, endpoint_index, waiting_state, payload, current_thread_ptr, endpoint_ptr, peer_thread_ptr, RetValueType::ErrorIpcSameContainer); }
            return ipc_schedule_waiting_peer_and_finish(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr,
                Ghost(Some((endpoint_index, waiting_state, payload))), peer_thread_ptr, RetValueType::ErrorIpcSameContainer, Tracked(cpu_lock_perm),
                Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
            );
        }
        ipc_rendezvous_cpu_cross_container(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(endpoint_index), Ghost(waiting_state),
            peer_thread_ptr, is_send, transfer_cpu_id, Ghost(payload), current_container, peer_container, wake_cpu, Tracked(cpu_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
        )
    }
}

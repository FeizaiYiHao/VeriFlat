use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{ipc_dequeue_endpoint_waiter, ipc_schedule_endpoint_waiter};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_spec::ipc_pci_rendezvous_eof_transition_framing;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
    pub(super) fn finish_ipc_pci_rendezvous_release(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
        peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
        Ghost(peer_result): Ghost<RetValueType>, Ghost(pci_transfer): Ghost<Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>>, Ghost(payload): Ghost<IPCPayLoad>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
        Tracked(irt_lock_perm): Tracked<LockPerm>, iommu_table: Option<RwLockPageTableRoot>, Tracked(iommu_table_lock_perm): Tracked<Option<LockPerm>>,
    )
        requires
            old(krnl).inv(),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() && old(krnl).ctn_mp.spec_index(p).lock_process_owner_u() == old(steps).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u() },
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
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
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
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is KILLED),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(peer_thread_ptr),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
            !(old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is KILLED),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
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
            typed_lock_map_contains_mode(old(lctx).iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
            irt_lock_perm.state() is WriteLock,
            irt_lock_perm.thread_id() == old(lctx).thread_id(),
            irt_lock_perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom() =~= set![(peer_scheduler_ptr, wake_cpu)],
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            iommu_table is None ==> old(lctx).iommu_table_lock_map().dom().is_empty(),
            iommu_table matches Some(t) ==> pci_transfer is Some && old(krnl).prc_mp.spec_index(pci_transfer->Some_0.1).view().iommu_table == Some(t),
            iommu_table matches Some(t) ==> {
                &&& old(lctx).iommu_table_lock_map().dom() =~= set![t]
                &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), t, TypedLockMode::Write)
                &&& old(krnl).it_mp.dom().contains(t)
                &&& old(krnl).it_mp.spec_index(t).view().leaves_present()
                &&& iommu_table_lock_perm is Some
                &&& iommu_table_lock_perm->Some_0.state() is WriteLock
                &&& iommu_table_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& iommu_table_lock_perm->Some_0.lock_id() == old(krnl).it_mp.spec_index(t).locking_thread()->Write_lock_id
            },
            old(lctx).iommu_root_table_lock_map().dom() =~= set![old(krnl).irt.view().table_base()],
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
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            kernel_ipc_rendezvous_fields(&old(steps).snapshot_k(), old(krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr,
                peer_result, None, pci_transfer),
            payload is Pci,
            ({
                let result = ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload);
                &&& peer_result == result
                &&& peer_result == ipc_peer_result(payload, result)
                &&& pci_transfer == ipc_pci_transfer(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload, result)
            }),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
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
        if let Some(t) = iommu_table {
            krnl.wunlock_iommu_table(t, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm.tracked_unwrap()));
        }
        krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_lock_perm));
        krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_ipc_rendezvous_fields(&steps.snapshot_k(), &*krnl, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr,
                peer_result, None, pci_transfer)) by {
                reveal(kernel_ipc_rendezvous_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            };
            steps.end_kernel_step_ipc_rendezvous(&*krnl, &*lctx, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr,
                peer_result, None, pci_transfer, payload, false);
            assert({
                &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step_pre(steps.nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload)
            }) by {
                ipc_rendezvous_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index,
                    waiting_state, peer_thread_ptr, peer_result, None, pci_transfer, payload, false);
                ipc_rendezvous_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index,
                    waiting_state, peer_thread_ptr, peer_result, None, pci_transfer, payload, false);
            };
        }
    }

    /// Cross-process locked phase of `ipc_rendezvous_pci`: write-locks the root table, on a successful transfer of an attached
    /// function the sender's IOMMU table named by its read-only mirror, and the peer's scheduler shard; dequeues the waiting peer
    /// and schedules it with the owner-check result, and on success moves the PCI function to the receiver, detaching it under the
    /// table lock or, when absent, only handing over its owner slot. Ends in the release view with every lock still held.
    pub(super) fn ipc_pci_lock_transfer_and_schedule_peer(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, bus: u8, dev: u8, fun: u8, sender_proc: RwLockProcessPtr,
        receiver_proc: RwLockProcessPtr, Tracked(endpoint_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (RetValueType, Option<RwLockPageTableRoot>, Ghost<Option<PciBdf>>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<Option<LockPerm>>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, wake_cpu),
            pci_bdf_valid(bus as usize, dev as usize, fun as usize),
            current_thread_ptr != peer_thread_ptr,
            sender_proc != receiver_proc,
            old(krnl).prc_mp.dom().contains(sender_proc),
            old(krnl).prc_mp.dom().contains(receiver_proc),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.dom().contains(peer_thread_ptr),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
            old(krnl).sched_mp.dom().contains(peer_scheduler_ptr),
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
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map().dom() == old(lctx).thread_lock_map().dom(),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            ret.1 is None ==> final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map() && final(krnl).it_mp == old(krnl).it_mp,
            ret.1 is Some ==> ret.0 is Success,
            ret.1 matches Some(t) ==> final(krnl).prc_mp.spec_index(sender_proc).view().iommu_table == Some(t),
            ret.1 matches Some(t) ==> final(lctx).iommu_table_lock_map().dom() =~= set![t] && typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), t, TypedLockMode::Write),
            ret.1 matches Some(t) ==> !old(krnl).it_mp.spec_index(t).locked(),
            ret.1 matches Some(t) ==> final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, t),
            ret.1 matches Some(t) ==> old(krnl).it_mp.spec_index(t).view().leaves_present(),
            ret.1 matches Some(t) ==> final(krnl).it_mp.spec_index(t).view().mapping_4k() == old(krnl).it_mp.spec_index(t).view().mapping_4k()
                && final(krnl).it_mp.spec_index(t).view().mapping_2m() == old(krnl).it_mp.spec_index(t).view().mapping_2m()
                && final(krnl).it_mp.spec_index(t).view().mapping_1g() == old(krnl).it_mp.spec_index(t).view().mapping_1g(),
            ret.1 matches Some(t) ==> ret.5.view() is Some && ret.5.view()->Some_0.state() is WriteLock && ret.5.view()->Some_0.thread_id() == old(lctx).thread_id(),
            ret.1 matches Some(t) ==> ret.5.view()->Some_0.lock_id() == final(krnl).it_mp.spec_index(t).locking_thread()->Write_lock_id,
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).scheduler_lock_map().dom() =~= set![(peer_scheduler_ptr, wake_cpu)],
            typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (peer_scheduler_ptr, wake_cpu), TypedLockMode::Write),
            final(lctx).iommu_root_table_lock_map().dom() =~= set![old(krnl).irt.view().table_base()],
            typed_lock_map_contains_mode(final(lctx).iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
            *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, sched_mp: final(krnl).sched_mp, irt: final(krnl).irt,
                iommu_tlb: final(krnl).iommu_tlb, it_mp: final(krnl).it_mp, ..*old(krnl) }),
            ret.0 == if old(krnl).irt.view().spec_index_owner(bus as usize, dev as usize, fun as usize) == sender_proc { RetValueType::Success } else { RetValueType::ErrorIpcPciOwnerMismatch },
            ipc_pci_rendezvous_eof_transition_framing(*old(krnl), *final(krnl), current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc,
                receiver_proc, (bus as usize, dev as usize, fun as usize), ret.0 is Success, ret.0, old(lctx).thread_id(), ret.1, ret.2.view()),
            !old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(old(krnl).thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
            final(krnl).irt.view().table_base() == old(krnl).irt.view().table_base(),
            final(krnl).irt.inv(),
            final(krnl).iommu_tlb.inv(),
            iommu_table_perms_wf(final(krnl).it_mp),
            final(krnl).prc_mp.perms_wf(),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.wf(),
            final(krnl).sched_mp.perms_wf(),
            final(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.inv(),
            final(krnl).sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.wf(),
            final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
            final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
            forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
                old(krnl).prc_mp.dom().contains(p) ==> final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread(),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, peer_thread_ptr),
            final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread(),
            final(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(peer_thread_ptr).view().non_ipc_fields_unchanged(&old(krnl).thr_mp.spec_index(peer_thread_ptr).view()),
            final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
            final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr),
            final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread(),
            ret.3.view().state() is WriteLock,
            ret.3.view().thread_id() == old(lctx).thread_id(),
            ret.3.view().lock_id() == final(krnl).irt.locking_thread()->Write_lock_id,
            ret.4.view().state() is WriteLock,
            ret.4.view().thread_id() == old(lctx).thread_id(),
            ret.4.view().lock_id() == final(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
    {
        proof { thread_perms_wf_map(krnl.thr_mp); }
        let ghost bdf: PciBdf = (bus as usize, dev as usize, fun as usize);
        let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
        let owner = krnl.irt.borrow(Tracked(&irt_lock_perm)).owner(bus as usize, dev as usize, fun as usize);
        let attached = krnl.irt.borrow(Tracked(&irt_lock_perm)).is_attached(bus as usize, dev as usize, fun as usize);
        let transferred = owner == sender_proc;
        let result = if transferred { RetValueType::Success } else { RetValueType::ErrorIpcPciOwnerMismatch };
        proof { process_perms_wf_at(krnl.prc_mp, sender_proc); }
        let iommu_table = if transferred && attached { krnl.prc_mp.borrow_rodata(sender_proc).borrow().iommu_table_ptr } else { None };
        let Tracked(iommu_table_lock_perm) = match iommu_table {
            Some(t) => {
                proof { process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, sender_proc); }
                let Tracked(perm) = krnl.wlock_iommu_table(t, Tracked(&mut *lctx));
                Tracked(Some(perm))
            },
            None => Tracked(None),
        };
        let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx));
        proof { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr); }
        let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
        assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr, wake_cpu); };
        let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, peer_thread_ptr, Tracked(endpoint_lock_perm));
        proof {
            assert({
                let peer_node_addr = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr();
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(peer_node_addr)
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thread_ptr
                &&& endpoint_node_perm.addr() == peer_node_addr
            }) by {
                thread_endpoint_queue_wf_thread_at(old(krnl).thr_mp, old(krnl).ep_mp, peer_thread_ptr); endpoint_perms_wf_at(old(krnl).ep_mp, endpoint_ptr);
                old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.lemma_value_addr_unique(endpoint_node_perm.addr(), old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr());
            };
        }
        let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_waiter(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, wake_cpu, current_thread_ptr, result,
            Tracked(endpoint_node_perm), Tracked(peer_thread_lock_perm));
        scheduler_map_enqueue_scheduled_thread(&mut krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&*lctx), Tracked(&peer_scheduler_lock_perm));
        let ghost mut anchor: Option<PciBdf> = None;
        if transferred {
            match iommu_table {
                Some(t) => {
                    proof { krnl.it_mp.spec_index(t).view().table_pages_wf_cr3_at(); }
                    let new_anchor = iommu_root_table_reassign_detached(&mut krnl.irt, &mut krnl.iommu_tlb, &mut krnl.it_mp, t, bus as usize, dev as usize, fun as usize, receiver_proc,
                        Tracked(&*lctx), Tracked(&irt_lock_perm), Tracked(iommu_table_lock_perm.tracked_borrow()));
                    proof { anchor = new_anchor; }
                },
                None => {
                    krnl.irt.borrow_mut(Tracked(&*lctx), Tracked(&irt_lock_perm)).set_owner(bus as usize, dev as usize, fun as usize, receiver_proc);
                    proof { assert(iommu_root_table_typed_lock_map_aligned(krnl.irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
                },
            }
            proof { process_map_move_pci_function(&mut krnl.prc_mp, sender_proc, receiver_proc, bdf, lctx.process_lock_map(), lctx.thread_id()); }
        }
        proof {
            process_perms_wf_map(krnl.prc_mp);
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
            scheduler_perms_wf_map(old(krnl).sched_mp); scheduler_perms_wf_at(old(krnl).sched_mp, peer_scheduler_ptr);
            assert(ipc_pci_rendezvous_eof_transition_framing(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred,
                result, lctx.thread_id(), iommu_table, anchor,
            )) by { reveal(ipc_pci_rendezvous_eof_transition_framing); };
        }
        (result, iommu_table, Ghost(anchor), Tracked(irt_lock_perm), Tracked(peer_scheduler_lock_perm), Tracked(iommu_table_lock_perm))
    }
}

use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{ipc_dequeue_endpoint_waiter, ipc_schedule_endpoint_waiter};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_spec::ipc_pci_rendezvous_transition;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_eof::ipc_pci_rendezvous_eof;
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
    fn finish_ipc_pci_rendezvous_release(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
        peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
        Ghost(peer_result): Ghost<RetValueType>, Ghost(pci_transfer): Ghost<Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>>, Ghost(payload): Ghost<IPCPayLoad>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
        Tracked(irt_lock_perm): Tracked<LockPerm>,
    )
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
            old(lctx).iommu_table_lock_map().dom().is_empty(),
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

    /// Hands the PCI function named on both sides from the sending to the receiving process under the root-table
    /// lock, detaching it and flushing its IOTLB domain, and schedules the waiting peer with Success. A same-process
    /// pair or a sender that does not own the function schedules the peer with that error and moves nothing.
    #[verifier::spinoff_prover]
    pub(super) fn ipc_rendezvous_pci(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, Ghost(endpoint_index): Ghost<EndpointIdx>,
        Ghost(waiting_state): Ghost<ThreadState>, peer_thread_ptr: RwLockThreadPtr, is_send: bool, bus: u8, dev: u8, fun: u8, Ghost(payload): Ghost<IPCPayLoad>,
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
            is_send == (waiting_state is SENDING),
            payload == (IPCPayLoad::Pci { bus, dev, fun }),
            pci_bdf_valid(bus as usize, dev as usize, fun as usize),
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
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (IPCPayLoad::Pci { bus, dev, fun }),
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
            ret is Success || ret is ErrorIpcSameProcess || ret is ErrorIpcPciOwnerMismatch,
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
        proof { thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); }
        let current_container = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container;
        let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        let peer_container = peer_thread_ref.owning_container;
        let peer_last_cpu = peer_thread_ref.last_cpu;
        let peer_proc = peer_thread_ref.owning_proc;
        let sender_proc = if is_send { process_ptr } else { peer_proc };
        let receiver_proc = if is_send { peer_proc } else { process_ptr };
        let ghost bdf: PciBdf = (bus as usize, dev as usize, fun as usize);
        proof {
            process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, peer_thread_ptr);
            assert({
                let pre = kernel_k_to_kernel_u(steps.snapshot_k());
                &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
                &&& pre.thread_map[current_thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& pre.endpoint_map[endpoint_ptr].queue[0] == peer_thread_ptr
                &&& pre.thread_map[current_thread_ptr].owning_proc == process_ptr
                &&& pre.thread_map[peer_thread_ptr].owning_proc == peer_proc
                &&& pre.thread_map[peer_thread_ptr].state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state
                &&& pre.thread_map[peer_thread_ptr].ipc_payload == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
                &&& pre.process_map[sender_proc].owned_pci_functions == old(krnl).prc_mp.spec_index(sender_proc).view_ghost().owned_pci_functions.view()
            }) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(endpoint_ptr));
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
                kernel_process_projection_at(&steps.snapshot_k(), sender_proc);
            };
        }
        if sender_proc == receiver_proc {
            return ipc_schedule_waiting_peer_and_finish(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr,
                Ghost(Some((endpoint_index, waiting_state, payload))), peer_thread_ptr, RetValueType::ErrorIpcSameProcess, Tracked(cpu_lock_perm),
                Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
            );
        }
        proof { assert(lctx.held_lock_majors_lt(IOMMU_ROOT_TABLE_LOCK_MAJOR)) by { reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); }; }
        let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
        let owner = krnl.irt.borrow(Tracked(&irt_lock_perm)).owner(bus as usize, dev as usize, fun as usize);
        let transferred = owner == sender_proc;
        let result = if transferred { RetValueType::Success } else { RetValueType::ErrorIpcPciOwnerMismatch };
        let ghost pci_transfer = if transferred { Some((bdf, sender_proc, receiver_proc)) } else { None };
        proof {
            assert({
                let pre = kernel_k_to_kernel_u(steps.snapshot_k());
                &&& result == ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, payload)
                &&& pci_transfer == ipc_pci_transfer(pre, cpu_id, endpoint_index, waiting_state, payload, result)
            }) by { reveal(process_pci_function_ownership_wf); };
        }
        let wake_cpu = if peer_container == current_container { cpu_id } else { peer_last_cpu };
        proof { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); container_perms_wf_at(krnl.ctn_mp, peer_container); }
        let peer_scheduler_ptr = krnl.ctn_mp.borrow_rodata(peer_container).borrow().scheduler;
        proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container); }
        let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx));
        proof { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr); }
        let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
        assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr, wake_cpu); };
        let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, peer_thread_ptr, Tracked(&endpoint_lock_perm));
        proof {
            assert({
                let peer_node_addr = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr();
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(peer_node_addr)
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thread_ptr
                &&& endpoint_node_perm.addr() == peer_node_addr
            }) by { thread_endpoint_queue_wf_thread_at(old(krnl).thr_mp, old(krnl).ep_mp, peer_thread_ptr); endpoint_perms_wf_at(old(krnl).ep_mp, endpoint_ptr); reveal(LinkedList::wf_map); };
        }
        let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_waiter(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, wake_cpu, current_thread_ptr, result,
            Tracked(endpoint_node_perm), Tracked(&peer_thread_lock_perm));
        scheduler_map_enqueue_scheduled_thread(&mut krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&*lctx), Tracked(&peer_scheduler_lock_perm));
        if transferred {
            iommu_root_table_reassign_detached(&mut krnl.irt, &mut krnl.iommu_tlb, bus as usize, dev as usize, fun as usize, receiver_proc, Tracked(&*lctx), Tracked(&irt_lock_perm));
            proof { process_map_move_pci_function(&mut krnl.prc_mp, sender_proc, receiver_proc, bdf, lctx.process_lock_map(), lctx.thread_id()); }
        }
        proof {
            process_perms_wf_map(krnl.prc_mp);
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
            scheduler_perms_wf_at(old(krnl).sched_mp, peer_scheduler_ptr); scheduler_perms_wf_at(krnl.sched_mp, peer_scheduler_ptr);
            assert(ipc_pci_rendezvous_transition(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred,
                result, lctx.thread_id(),
            )) by { reveal(ipc_pci_rendezvous_transition); };
            ipc_pci_rendezvous_eof(
                *old(krnl), *krnl, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred,
                result, lctx.thread_id(), steps.snapshot_k(), cpu_id, process_ptr, endpoint_index, waiting_state,
            );
        }
        finish_ipc_pci_rendezvous_release(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, peer_scheduler_ptr, wake_cpu,
            Ghost(endpoint_index), Ghost(waiting_state), Ghost(result), Ghost(pci_transfer), Ghost(payload), Tracked(cpu_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm), Tracked(irt_lock_perm),
        );
        result
    }
}

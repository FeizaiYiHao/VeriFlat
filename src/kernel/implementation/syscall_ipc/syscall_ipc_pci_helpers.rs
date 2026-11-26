use vstd::prelude::*;
use vstd::{assert_seqs_equal, assert_seqs_equal_internal};
use crate::*;
use super::syscall_ipc_queue::{ipc_dequeue_endpoint_waiter, ipc_schedule_endpoint_waiter};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_spec::{ipc_pci_rendezvous_eof_pagetable_frame, ipc_pci_rendezvous_eof_pci_handoff, ipc_pci_rendezvous_eof_transition_framing};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_eof::{ipc_pci_detach_eof, ipc_pci_rendezvous_eof, ipc_pci_transfer_eof_pagetable_frame, ipc_pci_transfer_eof_within_may_cache};
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
    /// Releases every lock the PCI-payload rendezvous still holds after its page tables are unlocked; only lock states move,
    /// and exactly the held ones become unlocked.
    fn unlock_ipc_pci_rendezvous_locks(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, current_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
        peer_thrd_ptr: RwLockThreadPtr, peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, Tracked(cpu_lock_perm): Tracked<LockPerm>,
        Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
        Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>, irt_held: bool, Tracked(irt_lock_perm): Tracked<Option<LockPerm>>, iommu_table: Option<RwLockPageTableRoot>,
        Tracked(iommu_table_lock_perm): Tracked<Option<LockPerm>>,
    )
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            irt_held == (irt_lock_perm is Some),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            current_thrd_ptr != peer_thrd_ptr,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
            !(old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state is KILLED),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().exited.view(),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).thrd_mp.dom().contains(peer_thrd_ptr),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
            !(old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state is KILLED),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().exited.view(),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thrd_ptr, TypedLockMode::Write),
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(ep_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
            old(krnl).sched_mp.dom().contains(peer_sched_ptr),
            index_valid(NUM_CPUS, wake_cpu),
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_sched_ptr, wake_cpu), TypedLockMode::Write),
            peer_scheduler_lock_perm.state() is WriteLock,
            peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
            irt_lock_perm is None ==> old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            irt_lock_perm matches Some(perm) ==> {
                &&& old(lctx).iommu_root_table_lock_map().dom() =~= set![old(krnl).irt.view().table_base()]
                &&& typed_lock_map_contains_mode(old(lctx).iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write)
                &&& perm.state() is WriteLock
                &&& perm.thread_id() == old(lctx).thread_id()
                &&& perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id
            },
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, peer_thrd_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
            old(lctx).scheduler_lock_map().dom() =~= set![(peer_sched_ptr, wake_cpu)],
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            iommu_table is None ==> old(lctx).iommu_table_lock_map().dom().is_empty(),
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
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, thrd_mp: final(krnl).thrd_mp, sched_mp: final(krnl).sched_mp, ep_mp: final(krnl).ep_mp,
                irt: final(krnl).irt, it_mp: final(krnl).it_mp, ..*old(krnl) }),
            final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state)),
            forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) ==> {
                &&& final(krnl).cpu_arr.spec_index(i).value.view().view() == old(krnl).cpu_arr.spec_index(i).value.view().view()
                &&& final(krnl).cpu_arr.spec_index(i).value.killer_info() == old(krnl).cpu_arr.spec_index(i).value.killer_info()
                &&& final(krnl).cpu_arr.spec_index(i).value.locking_thread() == if old(lctx).cpu_lock_map().dom().contains(i) { RwLockState::None } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() }
            },
            final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
            forall|t: RwLockThreadPtr| #![trigger final(krnl).thrd_mp.spec_index(t)] old(krnl).thrd_mp.dom().contains(t) ==> {
                &&& final(krnl).thrd_mp.spec_index(t).view() == old(krnl).thrd_mp.spec_index(t).view()
                &&& final(krnl).thrd_mp.spec_index(t).being_killed() == old(krnl).thrd_mp.spec_index(t).being_killed()
                &&& final(krnl).thrd_mp.spec_index(t).locking_thread() == if old(lctx).thread_lock_map().dom().contains(t) { RwLockState::None } else { old(krnl).thrd_mp.spec_index(t).locking_thread() }
            },
            final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom(),
            forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)] old(krnl).ep_mp.dom().contains(e) ==> {
                &&& final(krnl).ep_mp.spec_index(e).view() == old(krnl).ep_mp.spec_index(e).view()
                &&& final(krnl).ep_mp.spec_index(e).being_killed() == old(krnl).ep_mp.spec_index(e).being_killed()
                &&& final(krnl).ep_mp.spec_index(e).locking_thread() == if old(lctx).endpoint_lock_map().dom().contains(e) { RwLockState::None } else { old(krnl).ep_mp.spec_index(e).locking_thread() }
            },
            final(krnl).irt.view() == old(krnl).irt.view(),
            iommu_table is None ==> final(krnl).it_mp == old(krnl).it_mp,
            final(krnl).it_mp.dom() == old(krnl).it_mp.dom(),
            forall|p: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(p)] old(krnl).it_mp.dom().contains(p) ==> {
                &&& final(krnl).it_mp.spec_index(p).view() == old(krnl).it_mp.spec_index(p).view()
                &&& final(krnl).it_mp.spec_index(p).locking_thread() == if old(lctx).iommu_table_lock_map().dom().contains(p) { RwLockState::None } else { old(krnl).it_mp.spec_index(p).locking_thread() }
            },
            forall|c: RwLockContainerPtr| #![trigger final(krnl).sched_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().scheduler)]
                old(krnl).ctn_mp.dom().contains(c) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().scheduler))
                    == scheduler_shards_of(old(krnl).sched_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().scheduler)),
    {
        if let Some(t) = iommu_table {
            krnl.wunlock_iommu_table(t, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm.tracked_unwrap()));
        }
        if irt_held {
            krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_lock_perm.tracked_unwrap()));
        }
        krnl.wunlock_thread(peer_thrd_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
        krnl.wunlock_thread(current_thrd_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_scheduler_shard(peer_sched_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
        krnl.wunlock_endpoint(ep_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }
    }

    pub(super) fn finish_ipc_pci_rendezvous_release(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        prc_ptr: RwLockProcessPtr, current_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, peer_thrd_ptr: RwLockThreadPtr,
        peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, Ghost(ep_idx): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
        Ghost(peer_result): Ghost<RetValueType>, Ghost(pci_transfer): Ghost<Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>>, Ghost(payload): Ghost<IPCPayLoad>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
        irt_held: bool, Tracked(irt_lock_perm): Tracked<Option<LockPerm>>, iommu_table: Option<RwLockPageTableRoot>, Tracked(iommu_table_lock_perm): Tracked<Option<LockPerm>>,
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
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thrd_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thrd_mp.spec_index(p)]
                old(steps).snapshot_k().thrd_mp.dom().contains(p) && old(krnl).thrd_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thrd_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            old(krnl).pt_lower == old(steps).snapshot_k().pt_lower,
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
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            current_thrd_ptr != peer_thrd_ptr,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
            !(old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state is KILLED),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().exited.view(),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).thrd_mp.dom().contains(peer_thrd_ptr),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
            !(old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state is IPC_TRANSIT),
            !(old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state is KILLED),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().exited.view(),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thrd_ptr, TypedLockMode::Write),
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(ep_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
            old(krnl).sched_mp.dom().contains(peer_sched_ptr),
            index_valid(NUM_CPUS, wake_cpu),
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_sched_ptr, wake_cpu), TypedLockMode::Write),
            peer_scheduler_lock_perm.state() is WriteLock,
            peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
            (irt_lock_perm is Some) == (pci_transfer is Some),
            irt_held == (irt_lock_perm is Some),
            irt_lock_perm is None ==> old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            irt_lock_perm matches Some(perm) ==> {
                &&& old(lctx).iommu_root_table_lock_map().dom() =~= set![old(krnl).irt.view().table_base()]
                &&& typed_lock_map_contains_mode(old(lctx).iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write)
                &&& perm.state() is WriteLock
                &&& perm.thread_id() == old(lctx).thread_id()
                &&& perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id
            },
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, peer_thrd_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
            old(lctx).scheduler_lock_map().dom() =~= set![(peer_sched_ptr, wake_cpu)],
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
            iommu_table matches Some(t) ==> {
                let did = old(steps).snapshot_k().it_mp.spec_index(t).view().did;
                let anchor = pci_bdf_of_did(did->Some_0);
                did is Some && old(krnl).irt.view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == did ==> old(krnl).irt.view().spec_index_owner(anchor.0, anchor.1, anchor.2) == Some(pci_transfer->Some_0.1)
            },
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
            kernel_ipc_rendezvous_fields(&old(steps).snapshot_k(), old(krnl), cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr,
                peer_result, None, pci_transfer),
            payload is Pci,
            ({
                let snap = old(steps).snapshot_k();
                let caller_proc = snap.thrd_mp.spec_index(current_thrd_ptr).view().owning_proc;
                let peer_proc = snap.thrd_mp.spec_index(peer_thrd_ptr).view().owning_proc;
                &&& snap.thrd_mp.dom().contains(current_thrd_ptr) && snap.thrd_mp.dom().contains(peer_thrd_ptr)
                &&& snap.prc_mp.dom().contains(caller_proc) && !snap.prc_mp.spec_index(caller_proc).view().zombie
                &&& snap.pt_mp.dom().contains(snap.prc_mp.spec_index(caller_proc).view().pagetable)
                &&& snap.pt_mp.spec_index(snap.prc_mp.spec_index(caller_proc).view().pagetable).locking_thread() is None
                &&& snap.prc_mp.dom().contains(peer_proc) && !snap.prc_mp.spec_index(peer_proc).view().zombie
                &&& snap.pt_mp.dom().contains(snap.prc_mp.spec_index(peer_proc).view().pagetable)
                &&& snap.pt_mp.spec_index(snap.prc_mp.spec_index(peer_proc).view().pagetable).locking_thread() is None
            }),
            ({
                let result = ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload);
                &&& peer_result == result
                &&& peer_result == ipc_peer_result(payload, result)
                &&& pci_transfer == ipc_pci_transfer(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload, result)
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
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload),
            ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload),
    {
        unlock_ipc_pci_rendezvous_locks(
            krnl, Tracked(&mut *lctx), cpu_id, current_thrd_ptr, ep_ptr, peer_thrd_ptr, peer_sched_ptr, wake_cpu, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm),
            Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm), irt_held, Tracked(irt_lock_perm), iommu_table,
            Tracked(iommu_table_lock_perm),
        );
        proof {
            assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
            assert(kernel_ipc_rendezvous_fields(&steps.snapshot_k(), &*krnl, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr,
                peer_result, None, pci_transfer) && krnl.cpu_regs.view().view() == steps.snapshot_k().cpu_regs.view().view() && krnl.cpu_trap_frame.view().view() == steps.snapshot_k().cpu_trap_frame.view().view()) by { reveal(kernel_ipc_rendezvous_fields); };
            steps.end_kernel_step_ipc_rendezvous(&*krnl, &*lctx, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr,
                peer_result, None, pci_transfer, payload, false, true);
            assert({
                &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload)
            }) by {
                ipc_rendezvous_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, current_thrd_ptr, ep_ptr, ep_idx,
                    waiting_state, peer_thrd_ptr, peer_result, None, pci_transfer, payload, false, true, old(steps).snapshot_k());
            };
        }
    }

    /// Under the write-held page tables `sender_pt` and `receiver_pt`, write-locks the root table and, when the function is
    /// attached and the sender has an IOMMU table, that table (named by the sender's read-only mirror) and detaches the function;
    /// then the sender's entry `sender_index` releases the function and the receiver's free entry `receiver_index` claims it.
    /// Ends in the acquire view with the root table and that IOMMU table still held.
    fn ipc_pci_transfer_function(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
        receiver_pt: RwLockPageTableRoot, sender_index: usize, receiver_index: usize, bus: usize, dev: usize, fun: usize, Tracked(sender_pt_perm): Tracked<&LockPerm>,
        Tracked(receiver_pt_perm): Tracked<&LockPerm>, Ghost(pre): Ghost<KernelK>,
    ) -> (ret: (Option<RwLockPageTableRoot>, Ghost<Option<PciBdf>>, Tracked<LockPerm>, Tracked<Option<LockPerm>>))
        requires
            old(krnl).inv(),
            pre.inv(),
            *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, ..pre }),
            old(krnl).pt_mp.dom() == pre.pt_mp.dom(),
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) && p != sender_pt && p != receiver_pt ==> old(krnl).pt_mp.spec_index(p) == pre.pt_mp.spec_index(p),
            old(krnl).pt_mp.spec_index(sender_pt).view().higher == pre.pt_mp.spec_index(sender_pt).view().higher,
            old(krnl).pt_mp.spec_index(receiver_pt).view().higher == pre.pt_mp.spec_index(receiver_pt).view().higher,
            old(krnl).pt_mp.spec_index(sender_pt).being_killed() == pre.pt_mp.spec_index(sender_pt).being_killed(),
            old(krnl).pt_mp.spec_index(receiver_pt).being_killed() == pre.pt_mp.spec_index(receiver_pt).being_killed(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            pci_bdf_valid(bus, dev, fun),
            sender_proc != receiver_proc,
            sender_pt != receiver_pt,
            old(krnl).prc_mp.dom().contains(sender_proc),
            old(krnl).prc_mp.dom().contains(receiver_proc),
            old(krnl).pt_mp.dom().contains(sender_pt),
            old(krnl).pt_mp.dom().contains(receiver_pt),
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.proc_ptr == sender_proc,
            old(krnl).pt_mp.spec_index(receiver_pt).view().higher.proc_ptr == receiver_proc,
            old(krnl).prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
            !(old(krnl).prc_mp.spec_index(receiver_proc).view().state.view() is TablesEmptied),
            !(old(krnl).prc_mp.spec_index(receiver_proc).view().state.view() is Zombie),
            sender_index < PCI_FUNCTIONS_PER_PROCESS,
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.pci.spec_entry(sender_index as int).used,
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.pci.spec_entry(sender_index as int).bdf == (bus, dev, fun),
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.pci.spec_entry(sender_index as int).count == 0,
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains((bus, dev, fun)),
            receiver_index < PCI_FUNCTIONS_PER_PROCESS,
            !old(krnl).pt_mp.spec_index(receiver_pt).view().higher.pci.spec_entry(receiver_index as int).used,
            old(krnl).pt_mp.spec_index(receiver_pt).view().higher.pci.view().dom().len() < PCI_FUNCTIONS_PER_PROCESS,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), sender_pt, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), receiver_pt, TypedLockMode::Write),
            sender_pt_perm.state() is WriteLock,
            sender_pt_perm.thread_id() == old(lctx).thread_id(),
            sender_pt_perm.lock_id() == old(krnl).pt_mp.spec_index(sender_pt).locking_thread()->Write_lock_id,
            receiver_pt_perm.state() is WriteLock,
            receiver_pt_perm.thread_id() == old(lctx).thread_id(),
            receiver_pt_perm.lock_id() == old(krnl).pt_mp.spec_index(receiver_pt).locking_thread()->Write_lock_id,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), sender_pt).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), sender_pt).leaves_present(),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), sender_pt).lower.hidden_l1_tables_in_locked_windows(),
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
            !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(sender_pt).view().higher.proc_ptr).view().state.view() is TablesEmptied)
                && !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(sender_pt).view().higher.proc_ptr).view().state.view() is Zombie) ==> old(krnl).pt_mp.spec_index(sender_pt).view().higher.no_hidden_user_l4_l3_entries(),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), receiver_pt).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), receiver_pt).leaves_present(),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), receiver_pt).lower.hidden_l1_tables_in_locked_windows(),
            old(krnl).pt_mp.spec_index(receiver_pt).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
            !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(receiver_pt).view().higher.proc_ptr).view().state.view() is TablesEmptied)
                && !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(receiver_pt).view().higher.proc_ptr).view().state.view() is Zombie) ==> old(krnl).pt_mp.spec_index(receiver_pt).view().higher.no_hidden_user_l4_l3_entries(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)]
                old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
                ==> !(old(krnl).thrd_mp.spec_index(held_thread).view().state is SCHEDULED),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).iommu_root_table_lock_map().dom() =~= set![old(krnl).irt.view().table_base()],
            typed_lock_map_contains_mode(final(lctx).iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
            ret.0 is None ==> final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            ret.0 matches Some(t) ==> final(lctx).iommu_table_lock_map().dom() =~= set![t] && typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), t, TypedLockMode::Write),
            ret.0 matches Some(t) ==> !old(krnl).it_mp.spec_index(t).locked() && final(krnl).it_mp.spec_index(t).view().leaves_present(),
            ret.0 matches Some(t) ==> final(krnl).prc_mp.spec_index(sender_proc).view().iommu_table == Some(t),
            ret.0 matches Some(t) ==> ret.3.view() is Some && ret.3.view()->Some_0.state() is WriteLock && ret.3.view()->Some_0.thread_id() == old(lctx).thread_id()
                && ret.3.view()->Some_0.lock_id() == final(krnl).it_mp.spec_index(t).locking_thread()->Write_lock_id,
            ret.2.view().state() is WriteLock,
            ret.2.view().thread_id() == old(lctx).thread_id(),
            ret.2.view().lock_id() == final(krnl).irt.locking_thread()->Write_lock_id,
            final(krnl).irt.view().table_base() == old(krnl).irt.view().table_base(),
            final(krnl).pt_mp.spec_index(sender_pt).locking_thread() == old(krnl).pt_mp.spec_index(sender_pt).locking_thread(),
            final(krnl).pt_mp.spec_index(receiver_pt).locking_thread() == old(krnl).pt_mp.spec_index(receiver_pt).locking_thread(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), sender_pt).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), sender_pt).leaves_present(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), sender_pt).lower.hidden_l1_tables_in_locked_windows(),
            final(krnl).pt_mp.spec_index(sender_pt).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
            !(final(krnl).prc_mp.spec_index(final(krnl).pt_mp.spec_index(sender_pt).view().higher.proc_ptr).view().state.view() is TablesEmptied)
                && !(final(krnl).prc_mp.spec_index(final(krnl).pt_mp.spec_index(sender_pt).view().higher.proc_ptr).view().state.view() is Zombie) ==> final(krnl).pt_mp.spec_index(sender_pt).view().higher.no_hidden_user_l4_l3_entries(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), receiver_pt).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), receiver_pt).leaves_present(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), receiver_pt).lower.hidden_l1_tables_in_locked_windows(),
            final(krnl).pt_mp.spec_index(receiver_pt).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
            !(final(krnl).prc_mp.spec_index(final(krnl).pt_mp.spec_index(receiver_pt).view().higher.proc_ptr).view().state.view() is TablesEmptied)
                && !(final(krnl).prc_mp.spec_index(final(krnl).pt_mp.spec_index(receiver_pt).view().higher.proc_ptr).view().state.view() is Zombie) ==> final(krnl).pt_mp.spec_index(receiver_pt).view().higher.no_hidden_user_l4_l3_entries(),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, irt: final(krnl).irt, iommu_tlb: final(krnl).iommu_tlb, it_mp: final(krnl).it_mp, ..*old(krnl) }),
            final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
            forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] old(krnl).pt_mp.dom().contains(p) && p != sender_pt && p != receiver_pt
                ==> final(krnl).pt_mp.spec_index(p) == old(krnl).pt_mp.spec_index(p),
            ret.0 is None ==> final(krnl).it_mp == old(krnl).it_mp,
            ret.0 matches Some(t) ==> final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, t),
            ipc_pci_rendezvous_eof_pci_handoff(pre, *final(krnl), sender_proc, receiver_proc, sender_pt, receiver_pt, (bus, dev, fun), true, old(lctx).thread_id(), ret.0, ret.1.view()),
    {
        let ghost bdf: PciBdf = (bus, dev, fun);
        let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
        let attached = krnl.irt.borrow(Tracked(&irt_lock_perm)).is_attached(bus, dev, fun);
        proof { process_perms_wf_at(krnl.prc_mp, sender_proc); pagetable_perms_wf_implies_map_perms_wf(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, sender_pt); }
        let iommu_table = if attached { krnl.prc_mp.borrow_rodata(sender_proc).borrow().iommu_table_ptr } else { None };
        let ghost mut anchor: Option<PciBdf> = None;
        let ghost mut locked_it = *krnl;
        let Tracked(iommu_table_lock_perm) = match iommu_table {
            Some(t) => {
                proof { process_iommu_table_wf_process_at(krnl.prc_mp, krnl.it_mp, sender_proc); }
                let Tracked(perm) = krnl.wlock_iommu_table(t, Tracked(&mut *lctx));
                let ghost locked = *krnl;
                proof { krnl.it_mp.spec_index(t).view().table_pages_wf_cr3_at(); }
                let new_anchor = iommu_root_table_detach_owned(&mut krnl.irt, &mut krnl.iommu_tlb, &mut krnl.it_mp, t,
                    &krnl.pt_mp.borrow_typed(sender_pt, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(sender_pt_perm)).higher.pci, bus, dev, fun, Ghost(locked),
                    Tracked(&*lctx), Tracked(&irt_lock_perm), Tracked(&perm));
                proof {
                    anchor = new_anchor;
                    locked_it = locked;
                    ipc_pci_detach_eof(locked, *krnl, sender_proc, sender_pt, t, bdf, new_anchor);
                    assert({
                        &&& krnl.it_mp.spec_index(t).view().mapping_4k() == locked.it_mp.spec_index(t).view().mapping_4k()
                    });
                }
                Tracked(Some(perm))
            },
            None => Tracked(None),
        };
        let ghost detached = *krnl;
        proof { process_iommu_table_wf_process_at(krnl.prc_mp, krnl.it_mp, sender_proc); }
        krnl.update_pci_entry(sender_pt, sender_index, PciEntryUpdate::Release, Tracked(&*lctx), Tracked(sender_pt_perm), Tracked(&irt_lock_perm));
        krnl.update_pci_entry(receiver_pt, receiver_index, PciEntryUpdate::Claim { bus, device: dev, function: fun }, Tracked(&*lctx), Tracked(receiver_pt_perm),
            Tracked(&irt_lock_perm));
        proof {
            assert({
                let s_before = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), sender_pt);
                let s_after = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), sender_pt);
                let r_before = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), receiver_pt);
                let r_after = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), receiver_pt);
                &&& s_after.lower == s_before.lower
                &&& s_after.mapping_4k() == s_before.mapping_4k()
                &&& s_after.mapping_2m() == s_before.mapping_2m()
                &&& s_after.mapping_1g() == s_before.mapping_1g()
                &&& r_after.lower == r_before.lower
                &&& r_after.mapping_4k() == r_before.mapping_4k()
                &&& r_after.mapping_2m() == r_before.mapping_2m()
                &&& r_after.mapping_1g() == r_before.mapping_1g()
            });
            let owners = seq3_update(old(krnl).irt.view().owners(), bus as int, dev as int, fun as int, Some(receiver_proc));
            assert_seqs_equal!(krnl.irt.view().owners() == owners, b => {
                assert_seqs_equal!(krnl.irt.view().owners()[b] == owners[b], d => { assert_seqs_equal!(krnl.irt.view().owners()[b][d] == owners[b][d], f => {}); });
            });
            if let Some(t) = iommu_table {
                if let Some(did) = old(krnl).irt.view().spec_index_iommu_did(bus, dev, fun) {
                    ipc_pci_transfer_eof_within_may_cache(pre, locked_it, detached, *krnl, bdf, t, did, krnl.iommu_tlb.spec_index(did));
                }
            }
            ipc_pci_transfer_eof_pagetable_frame(pre, *krnl, sender_pt, receiver_pt, bdf);
            assert(ipc_pci_rendezvous_eof_pci_handoff(pre, *krnl, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, true, lctx.thread_id(), iommu_table, anchor)) by {
                broadcast use IommuRootTable::wf_context_entry_at;
                reveal(ipc_pci_rendezvous_eof_pci_handoff);
            };
        }
        (iommu_table, Ghost(anchor), Tracked(irt_lock_perm), Tracked(iommu_table_lock_perm))
    }

    /// Cross-process locked phase of `ipc_rendezvous_pci`: write-locks the sender's and the receiver's page tables and checks
    /// that the sender's PCI function array holds the function with no BAR mapping and that the receiver's has a free entry; on
    /// success hands the function over (`ipc_pci_transfer_function`); then write-locks the peer's scheduler shard, dequeues the
    /// waiting peer and schedules it with the check result. Ends in the release view with both page tables unlocked and every
    /// other lock still held; `ret.3` is the state after the PCI part and the state before the page tables are unlocked.
    pub(super) fn ipc_pci_lock_transfer_and_schedule_peer(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, current_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
        peer_thrd_ptr: RwLockThreadPtr, peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, bus: u8, dev: u8, fun: u8, sender_proc: RwLockProcessPtr,
        receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, receiver_pt: RwLockPageTableRoot, Tracked(endpoint_lock_perm): Tracked<&LockPerm>,
        Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (RetValueType, Option<RwLockPageTableRoot>, Ghost<Option<PciBdf>>, Ghost<(KernelK, KernelK)>, Tracked<Option<LockPerm>>, Tracked<LockPerm>, Tracked<Option<LockPerm>>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, wake_cpu),
            pci_bdf_valid(bus as usize, dev as usize, fun as usize),
            current_thrd_ptr != peer_thrd_ptr,
            sender_proc != receiver_proc,
            receiver_proc == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc || receiver_proc == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().owning_proc,
            old(krnl).prc_mp.dom().contains(sender_proc),
            old(krnl).prc_mp.dom().contains(receiver_proc),
            old(krnl).pt_mp.dom().contains(sender_pt),
            old(krnl).pt_mp.dom().contains(receiver_pt),
            sender_pt != receiver_pt,
            old(krnl).pt_mp.spec_index(sender_pt).view().higher.proc_ptr == sender_proc,
            old(krnl).pt_mp.spec_index(receiver_pt).view().higher.proc_ptr == receiver_proc,
            old(krnl).prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
            old(krnl).prc_mp.spec_index(receiver_proc).view().pagetable == receiver_pt,
            old(krnl).ctn_mp.spec_index(old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
            !old(krnl).prc_mp.spec_index(sender_proc).view().zombie,
            !old(krnl).prc_mp.spec_index(receiver_proc).view().zombie,
            !(old(krnl).prc_mp.spec_index(receiver_proc).view().state.view() is TablesEmptied),
            !(old(krnl).prc_mp.spec_index(receiver_proc).view().state.view() is Zombie),
            !(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            old(krnl).thrd_mp.dom().contains(peer_thrd_ptr),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thrd_ptr, TypedLockMode::Write),
            peer_thread_lock_perm.state() is WriteLock,
            peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(ep_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
            old(krnl).sched_mp.dom().contains(peer_sched_ptr),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, peer_thrd_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
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
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map().dom() == old(lctx).thread_lock_map().dom(),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thrd_ptr, TypedLockMode::Write),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map().dom().is_empty(),
            final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            ret.1 is None ==> final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            ret.1 is Some ==> ret.0 is Success,
            ret.1 matches Some(t) ==> final(krnl).prc_mp.spec_index(sender_proc).view().iommu_table == Some(t),
            ret.1 matches Some(t) ==> final(lctx).iommu_table_lock_map().dom() =~= set![t] && typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), t, TypedLockMode::Write),
            ret.1 matches Some(t) ==> final(krnl).it_mp.dom().contains(t) && final(krnl).it_mp.spec_index(t).view().leaves_present(),
            ret.1 matches Some(t) ==> ret.6.view() is Some && ret.6.view()->Some_0.state() is WriteLock && ret.6.view()->Some_0.thread_id() == old(lctx).thread_id(),
            ret.1 matches Some(t) ==> ret.6.view()->Some_0.lock_id() == final(krnl).it_mp.spec_index(t).locking_thread()->Write_lock_id,
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).scheduler_lock_map().dom() =~= set![(peer_sched_ptr, wake_cpu)],
            typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (peer_sched_ptr, wake_cpu), TypedLockMode::Write),
            (ret.4.view() is Some) == (ret.0 is Success),
            ret.4.view() is None ==> final(lctx).iommu_root_table_lock_map().dom().is_empty(),
            ret.4.view() matches Some(perm) ==> {
                &&& final(lctx).iommu_root_table_lock_map().dom() =~= set![old(krnl).irt.view().table_base()]
                &&& typed_lock_map_contains_mode(final(lctx).iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write)
                &&& perm.state() is WriteLock
                &&& perm.thread_id() == old(lctx).thread_id()
                &&& perm.lock_id() == final(krnl).irt.locking_thread()->Write_lock_id
            },
            final(krnl).irt.view().table_base() == old(krnl).irt.view().table_base(),
            ({
                let pci_s = old(krnl).pt_mp.spec_index(sender_pt).view().higher.pci;
                let pci_r = old(krnl).pt_mp.spec_index(receiver_pt).view().higher.pci;
                let bdf = (bus as usize, dev as usize, fun as usize);
                ret.0 == if !pci_s.view().dom().contains(bdf) { RetValueType::ErrorIpcPciOwnerMismatch } else if pci_s.view()[bdf].len() != 0 { RetValueType::ErrorIpcPciBarMapped }
                    else if pci_r.view().dom().len() >= PCI_FUNCTIONS_PER_PROCESS { RetValueType::ErrorIpcPciReceiverFull } else { RetValueType::Success }
            }),
            ipc_pci_rendezvous_eof_transition_framing(*old(krnl), ret.3.view().0, ret.3.view().1, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc,
                receiver_proc, sender_pt, receiver_pt, (bus as usize, dev as usize, fun as usize), ret.0 is Success, ret.0, old(lctx).thread_id(), ret.1, ret.2.view()),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, ..ret.3.view().1 }),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, thrd_mp: final(krnl).thrd_mp, ep_mp: final(krnl).ep_mp, sched_mp: final(krnl).sched_mp, irt: final(krnl).irt,
                iommu_tlb: final(krnl).iommu_tlb, it_mp: final(krnl).it_mp, ..*old(krnl) }),
            old(krnl).pt_mp.spec_index(sender_pt).locking_thread() is None,
            old(krnl).pt_mp.spec_index(receiver_pt).locking_thread() is None,
            final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
            ret.3.view().1.sched_mp.spec_index(peer_sched_ptr).shards.inv(),
            ret.3.view().1.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.wf(),
            final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
            forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] old(krnl).pt_mp.dom().contains(p)
                ==> final(krnl).pt_mp.spec_index(p).locking_thread() == old(krnl).pt_mp.spec_index(p).locking_thread(),
            forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p)] ret.3.view().1.pt_mp.dom().contains(p)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p) == whole_pagetable(ret.3.view().1.pt_mp, ret.3.view().1.pt_lower.view(), p),
            ret.1 is None ==> final(krnl).it_mp == old(krnl).it_mp,
            ret.1 matches Some(t) ==> !old(krnl).it_mp.spec_index(t).locked() && final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, t),
            final(krnl).pt_mp.dom() == ret.3.view().1.pt_mp.dom(),
            forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] ret.3.view().1.pt_mp.dom().contains(p) && p != sender_pt && p != receiver_pt
                ==> final(krnl).pt_mp.spec_index(p) == ret.3.view().1.pt_mp.spec_index(p),
            wunlock_ensures(ret.3.view().1.pt_mp.spec_index(sender_pt), final(krnl).pt_mp.spec_index(sender_pt)),
            wunlock_ensures(ret.3.view().1.pt_mp.spec_index(receiver_pt), final(krnl).pt_mp.spec_index(receiver_pt)),
            !old(krnl).sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, peer_thrd_ptr),
            final(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread(),
            final(krnl).thrd_mp.spec_index(peer_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).being_killed(),
            final(krnl).thrd_mp.spec_index(peer_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().non_ipc_fields_unchanged(&old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view()),
            final(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
            final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, ep_ptr),
            final(krnl).ep_mp.spec_index(ep_ptr).locking_thread() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread(),
            ret.5.view().state() is WriteLock,
            ret.5.view().thread_id() == old(lctx).thread_id(),
            ret.5.view().lock_id() == final(krnl).sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
    {
        let ghost bdf: PciBdf = (bus as usize, dev as usize, fun as usize);
        let (Tracked(sender_pt_perm), Tracked(receiver_pt_perm)) = krnl.wlock_pagetable_pair(sender_pt, receiver_pt, Tracked(&mut *lctx));
        proof {
            process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, sender_proc); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, receiver_proc);
            pagetable_perms_wf_implies_map_perms_wf(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, sender_pt); pagetable_perms_wf_at(krnl.pt_mp, receiver_pt);
        }
        let sender_pci = &krnl.pt_mp.borrow_typed(sender_pt, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&sender_pt_perm)).higher.pci;
        let sender_index = sender_pci.find(bus as usize, dev as usize, fun as usize);
        let mut receiver_index: usize = 0;
        let result = match sender_index {
            None => RetValueType::ErrorIpcPciOwnerMismatch,
            Some(i) => {
                proof { sender_pci.wf_function_at(bdf); }
                if sender_pci.count(i) != 0 { RetValueType::ErrorIpcPciBarMapped } else {
                    match krnl.pt_mp.borrow_typed(receiver_pt, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&receiver_pt_perm)).higher.pci.free_entry() {
                        None => RetValueType::ErrorIpcPciReceiverFull,
                        Some(j) => {
                            receiver_index = j;
                            RetValueType::Success
                        },
                    }
                }
            },
        };
        let transferred = match result { RetValueType::Success => true, _ => false };
        let (iommu_table, Ghost(anchor), Tracked(irt_lock_perm), Tracked(iommu_table_lock_perm)) = if transferred {
            proof { sender_pci.wf_function_at(bdf); }
            let (iommu_table, anchor, Tracked(irt_lock_perm), iommu_table_lock_perm) = ipc_pci_transfer_function(krnl, Tracked(&mut *lctx), sender_proc, receiver_proc,
                sender_pt, receiver_pt, sender_index.unwrap(), receiver_index, bus as usize, dev as usize, fun as usize, Tracked(&sender_pt_perm), Tracked(&receiver_pt_perm),
                Ghost(*old(krnl)));
            (iommu_table, anchor, Tracked(Some(irt_lock_perm)), iommu_table_lock_perm)
        } else {
            proof {
                assert(ipc_pci_rendezvous_eof_pagetable_frame(*old(krnl), *krnl, sender_pt, receiver_pt, bdf, false)) by { reveal(ipc_pci_rendezvous_eof_pagetable_frame); };
                assert(ipc_pci_rendezvous_eof_pci_handoff(*old(krnl), *krnl, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, false, lctx.thread_id(), None, None)) by {
                    reveal(ipc_pci_rendezvous_eof_pci_handoff);
                };
            }
            (None, Ghost(None), Tracked(None), Tracked(None))
        };
        let ghost mid = *krnl;
        let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler_shard(peer_sched_ptr, wake_cpu, Tracked(&mut *lctx));
        proof { container_thread_scheduler_wf_shard_at(krnl.ctn_mp, krnl.thrd_mp, krnl.sched_mp, peer_sched_ptr, wake_cpu, peer_thrd_ptr); }
        let ghost old_peer_thread_lock_id = krnl.thrd_mp.lock_id_by_key(peer_thrd_ptr);
        assert(krnl.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_sched_ptr, wake_cpu); };
        let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), ep_ptr, peer_thrd_ptr, Tracked(endpoint_lock_perm));
        proof {
            assert({
                let peer_node_addr = old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().endpoint_linkedlist_node.addr();
                &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue.map().dom().contains(peer_node_addr)
                &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thrd_ptr
                &&& endpoint_node_perm.addr() == peer_node_addr
            }) by {
                thread_endpoint_queue_wf_thread_at(old(krnl).thrd_mp, old(krnl).ep_mp, peer_thrd_ptr); endpoint_perms_wf_at(old(krnl).ep_mp, ep_ptr);
                old(krnl).ep_mp.spec_index(ep_ptr).view().queue.wf_and_equal_values_implies_equal_addrs(endpoint_node_perm.addr(), old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().endpoint_linkedlist_node.addr());
            };
        }
        let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_waiter(&mut krnl.thrd_mp, Tracked(&*lctx), peer_thrd_ptr, wake_cpu, current_thrd_ptr, result,
            Tracked(endpoint_node_perm), Tracked(peer_thread_lock_perm));
        scheduler_map_enqueue_scheduled_thread(&mut krnl.sched_mp, peer_sched_ptr, wake_cpu, peer_thrd_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&*lctx), Tracked(&peer_scheduler_lock_perm));
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Thread(peer_thrd_ptr), old_peer_thread_lock_id, krnl.thrd_mp.lock_id_by_key(peer_thrd_ptr));
            scheduler_perms_wf_implies_map_perms_wf(old(krnl).sched_mp); scheduler_perms_wf_at(old(krnl).sched_mp, peer_sched_ptr);
            assert(ipc_pci_rendezvous_eof_transition_framing(
                *old(krnl), mid, *krnl, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred,
                result, lctx.thread_id(), iommu_table, anchor,
            )) by { reveal(ipc_pci_rendezvous_eof_transition_framing); };
            ipc_pci_rendezvous_eof(*old(krnl), mid, *krnl, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt,
                bdf, transferred, result, lctx.thread_id(), iommu_table, anchor);
        }
        let ghost scheduled = *krnl;
        krnl.wunlock_pagetable(sender_pt, Tracked(&mut *lctx), Tracked(sender_pt_perm));
        krnl.wunlock_pagetable(receiver_pt, Tracked(&mut *lctx), Tracked(receiver_pt_perm));
        (result, iommu_table, Ghost(anchor), Ghost((mid, scheduled)), Tracked(irt_lock_perm), Tracked(peer_scheduler_lock_perm), Tracked(iommu_table_lock_perm))
    }
}

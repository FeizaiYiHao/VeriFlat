use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_transition_helpers::{ipc_block_current_release_and_end_step, ipc_schedule_peer_on_shard};
use super::syscall_ipc_queue::{ipc_block_thread_on_endpoint, ipc_enqueue_endpoint_waiter};
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_transition_spec::{ipc_block_current_eof_transition_framing, ipc_schedule_waiting_peer_eof_transition_framing};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_transition_eof::{ipc_block_current_eof, ipc_schedule_waiting_peer_eof_rendezvous_fields};
verus! {
    #[verifier::spinoff_prover]
    pub(super) fn ipc_block_current(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
        waiting_state: ThreadState, payload: IPCPayLoad, pt_regs: &Registers, cpu_lock_perm: Tracked<LockPerm>,
        current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
            old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, endpoint_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
            old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
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
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
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
            waiting_state.is_endpoint_waiting(),
            payload.wf(),
            waiting_state is RECEIVING_CALL ==> old(krnl).thr_mp.spec_index(current_thread_ptr).view().caller is None,
            !old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || match old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state {
                    EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                    EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
                },
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret is CpuIdle,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ipc_block_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state),
            ipc_block_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id,
                endpoint_index, waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id)),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
                kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::CpuIdle),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            ipc_block_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state),
            ipc_block_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();
        proof { assert(typed_lock_map_majors_lt(lctx.cpu_lock_map(), CPU_LOCK_MAJOR_OFF)) by { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); }; }
        let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx));
        let ghost locked_k = *krnl;
        let ghost old_current_thread_lock_id = krnl.thr_mp.lock_id_by_key(current_thread_ptr);
        proof {
            assert({
                &&& steps.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().state is Running
                &&& krnl.cpu_arr.inv()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
            }) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
            assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.length != usize::MAX) by { endpoint_queue_len_bounded(&*krnl, endpoint_ptr); };
            assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == krnl.ep_mp.spec_index(endpoint_ptr).view().queue.length) by { endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); reveal(LinkedList::wf_value_list); };
        }

        let (endpoint_node_addr, endpoint_node_perm) = ipc_block_thread_on_endpoint(&mut krnl.thr_mp, Tracked(&*lctx), current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, pt_regs, Tracked(&current_thread_lock_perm));

        ipc_enqueue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, current_thread_ptr, waiting_state, endpoint_node_addr, endpoint_node_perm, Tracked(&endpoint_lock_perm));

        let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
        let default_cr3 = krnl.dflt_pt.borrow().cr3;
        assert(page_ptr_valid(default_cr3)) by { old(krnl).default_pagetable_view_inv(); old(krnl).dflt_pt.view().table_pages_wf_cr3_at(); };
        krnl.cpu_arr.block_current(cpu_id, default_cr3, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));

        proof {
            lctx.update_lock_id(KernelObjId::Thread(current_thread_ptr), old_current_thread_lock_id, krnl.thr_mp.lock_id_by_key(current_thread_ptr));
            lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id));
            assert(ipc_block_current_eof_transition_framing(locked_k, *krnl, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3)) by {
                reveal(ipc_block_current_eof_transition_framing);
            };
            ipc_block_current_eof(locked_k, *krnl, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3);
        }

        proof { assert(old(krnl).ctn_mp.dom().contains(old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container)) by { container_thread_wf_at(old(krnl).ctn_mp, old(krnl).thr_mp, current_thread_ptr); }; }
        ipc_block_current_release_and_end_step(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, pt_regs,
            Ghost(default_cr3), Ghost(*old(krnl)), Ghost(locked_k), Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(needflush_perm),
        );
        RetValueType::CpuIdle
    }

    /// Releases the caller, the scheduled peer, the peer's scheduler shard, the endpoint, and the cpu after the
    /// transition `pre` → `*old(krnl)` summarized by `ipc_schedule_waiting_peer_eof_transition_framing`, and records the kernel step.
    fn ipc_release_scheduled_peer_and_end_step(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>, Ghost(payload): Ghost<IPCPayLoad>, peer_thread_ptr: RwLockThreadPtr,
        result: RetValueType, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, Ghost(pre): Ghost<KernelK>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
        Tracked(peer_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
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
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            kernel_ipc_rendezvous_fields(&old(steps).snapshot_k(), old(krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, result, None, None),
            result == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            !(result is SuccessUsize) && (result is Success ==> payload is Empty),
            (payload is Cpu || payload is ReceiveCpu) ==> result is ErrorIpcTypeMismatch || result is ErrorIpcSameContainer,
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, wake_cpu),
            current_thread_ptr != peer_thread_ptr,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
            old(krnl).thr_mp.dom().contains(peer_thread_ptr),
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
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_scheduler_ptr, wake_cpu), TypedLockMode::Write),
            peer_scheduler_lock_perm.state() is WriteLock,
            peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
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
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            ipc_schedule_waiting_peer_eof_transition_framing(pre, *old(krnl), current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, result, old(lctx).thread_id()),
            pre.thr_mp.dom().contains(current_thread_ptr),
            pre.thr_mp.dom().contains(peer_thread_ptr),
            pre.ep_mp.dom().contains(endpoint_ptr),
            pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
            pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            result == ipc_rendezvous_result(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {
        krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
        krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_ipc_rendezvous_fields(&steps.snapshot_k(), &*krnl, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, result, None, None)) by {
                broadcast use kernel_process_nonlock_fields_unchanged_transitive;
                reveal(kernel_ipc_rendezvous_fields); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            };
            steps.end_kernel_step_ipc_rendezvous(&*krnl, &*lctx, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, result, None, None, payload, false);
            assert({
                &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step_pre(steps.nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload)
            }) by {
                ipc_rendezvous_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, result, None, None, payload, false);
                ipc_rendezvous_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state,
                    peer_thread_ptr, result, None, None, payload, false);
            };
        }
    }

    pub(super) fn ipc_schedule_waiting_peer_and_finish(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>, Ghost(payload): Ghost<IPCPayLoad>, peer_thread_ptr: RwLockThreadPtr,
        result: RetValueType, cpu_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>,
        peer_thread_lock_perm: Tracked<LockPerm>,
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
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
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
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
            result == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            !(result is SuccessUsize) && (result is Success ==> payload is Empty),
            (payload is Cpu || payload is ReceiveCpu) ==> result is ErrorIpcTypeMismatch || result is ErrorIpcSameContainer,
            edp_idx_valid(endpoint_index),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
            waiting_state.is_endpoint_waiting(),
            (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != waiting_state.is_endpoint_send_waiting(),
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
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            ret == result,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload),
            final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
            final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            result == ipc_rendezvous_result(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload),
            ipc_rendezvous_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();
        let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

        proof { thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); }
        let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        let peer_container_ptr = peer_thread_ref.owning_container;
        let peer_last_cpu = peer_thread_ref.last_cpu;
        let caller_container_ptr = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container;
        let wake_cpu = if peer_container_ptr == caller_container_ptr { cpu_id } else { peer_last_cpu };
        proof { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr); container_perms_wf_at(krnl.ctn_mp, peer_container_ptr); }
        let peer_scheduler_ptr = krnl.ctn_mp.borrow_rodata(peer_container_ptr).borrow().scheduler;
        proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container_ptr); }
        let Tracked(peer_scheduler_lock_perm) = ipc_schedule_peer_on_shard(
            krnl, Tracked(&mut *lctx), cpu_id, current_thread_ptr, endpoint_ptr, peer_thread_ptr, result, peer_scheduler_ptr, wake_cpu, Tracked(&endpoint_lock_perm),
            Tracked(&peer_thread_lock_perm),
        );
        proof {
            ipc_schedule_waiting_peer_eof_rendezvous_fields(steps.snapshot_k(), *old(krnl), *krnl, cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, endpoint_ptr, endpoint_index, waiting_state,
                peer_scheduler_ptr, wake_cpu, result, lctx.thread_id());
        }
        ipc_release_scheduled_peer_and_end_step(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(endpoint_index), Ghost(waiting_state), Ghost(payload),
            peer_thread_ptr, result, peer_scheduler_ptr, wake_cpu, Ghost(*old(krnl)), Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm),
            Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm),
        );
        result
    }
} // verus!

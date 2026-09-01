use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_transition::{
    ipc_block_current, ipc_schedule_waiting_peer_and_finish,
    ipc_release_current_endpoint_and_finish,
};
use super::syscall_ipc_endpoint::{
    ipc_rendezvous_endpoint,
};
use super::syscall_ipc_pages::{
    ipc_rendezvous_pages,
};

verus! {

    pub(super) fn syscall_ipc_ordinary(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        waiting_state: ThreadState,
        payload: IPCPayLoad,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            waiting_state is SENDING || waiting_state is RECEIVING,
            match payload {
                IPCPayLoad::Empty => true,
                IPCPayLoad::Pages { va_range } => {
                    &&& va_range.wf()
                    &&& va_range.len > 0
                    &&& va_range.len <= usize::MAX / 3usize
                },
                IPCPayLoad::Endpoint { endpoint_index } =>
                    edp_idx_valid(endpoint_index),
                _ => false,
            },
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            old(krnl).all_objects_unlocked(old(lctx)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).steps.len() == 1,
            ret is Success ==> final(steps).steps.len()
                == match payload {
                    IPCPayLoad::Pages { va_range } => va_range.len,
                    _ => 0,
                },
            !(ret is CpuIdle) && !(ret is Success) ==> final(steps).steps.len() == 0,
            payload is Empty ==> (ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch),
            payload is Pages ==> (!(ret is ErrorIpcEndpointSourceInvalid) && !(ret is ErrorIpcEndpointTargetInUse) && !(ret is ErrorIpcEndpointOwnerMismatch)),
            payload is Endpoint ==> (ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch),
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
    {
        let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu_ref = krnl.cpu_arr.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu_ref.current_process.unwrap();
        let current_thread_ptr = cpu_ref.current_thread.unwrap();

        proof {
            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& krnl.prc_mp.lock_id_by_key(process_ptr).spec_gt(krnl.cpu_arr.lock_id_by_index(cpu_id))
            }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); reveal(process_perms_wf); };
        }
        let process_res = krnl.wlock_process_unless_killed(process_ptr, Tracked(&mut *lctx));
        if let (false, _) = process_res {
            release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        proof {
            assert({
                &&& krnl.thr_mp.dom().contains(current_thread_ptr)
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().container_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().process_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
                &&& krnl.thr_mp.lock_id_by_key(current_thread_ptr).spec_gt(krnl.prc_mp.lock_id_by_key(process_ptr))
            }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf); };
        }
        let current_thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
        if let (false, _) = current_thread_res {
            proof {
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
            }
            release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, Tracked(process_lock_perm), Tracked(cpu_lock_perm));
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(current_thread_lock_perm) = current_thread_res.1.unwrap();

        let current_thread_ref = krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm));
        let endpoint_option = *current_thread_ref.endpoint_descriptors.get(endpoint_index);
        if let None = endpoint_option {
            proof {
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
            }
            release_cpu_and_process_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm));
            return RetValueType::ErrorInvalidEndpoint;
        }
        let endpoint_ptr = endpoint_option.unwrap();

        proof {
            assert({
                &&& krnl.ep_mp.dom().contains(endpoint_ptr)
                &&& current_thread_lock_perm.ordering_lock_id().major == THREAD_LOCK_MAJOR
                &&& krnl.ep_mp.lock_id_by_key(endpoint_ptr).major == ENDPOINT_LOCK_MAJOR
                &&& kernel_objects_unlocked_except(krnl, lctx.thread_id(), Some(cpu_id), None, Some(process_ptr), Some(current_thread_ptr), None)
            }) by { reveal(thread_endpoint_ref_counter_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); };
        }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));

        proof {
            assert({
                &&& krnl.ep_mp.perms_wf()
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            }) by { reveal(endpoint_perms_wf); };
        }
        let endpoint_ref = krnl.ep_mp.borrow(endpoint_ptr, Tracked(&endpoint_lock_perm));
        let queue_len = endpoint_ref.queue.len();
        let queue_is_send = endpoint_ref.queue_state.is_send();
        let waiting_is_send = match waiting_state {
            ThreadState::SENDING => true,
            _ => false,
        };

        if queue_len == 0 || queue_is_send == waiting_is_send {
            proof {
                assert({
                    &&& !krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr)
                    &&& cpu_objects_unlocked_except(krnl.cpu_arr, lctx.thread_id(), set![cpu_id])
                    &&& page_objects_unlocked(krnl.pg_arr, lctx.thread_id())
                    &&& container_objects_unlocked(krnl.ctn_mp, lctx.thread_id())
                    &&& process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![process_ptr])
                    &&& thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr])
                    &&& endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])
                    &&& pagetable_objects_unlocked(krnl.pt_mp, lctx.thread_id())
                    &&& iommu_table_objects_unlocked(krnl.it_mp, lctx.thread_id())
                    &&& scheduler_objects_unlocked(krnl.sched_mp, lctx.thread_id())
                    &&& pcid_allocator_objects_unlocked(krnl.pcid_allc_mp, lctx.thread_id())
                    &&& allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())
                    &&& allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id())
                    &&& allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id())
                }) by { reveal(thread_endpoint_queue_wf); };
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
            }
            return ipc_block_current(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, &*pt_regs, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm));
        }

        proof {
            assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.wf()) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
        }
        let (_, peer_thread_ptr) = endpoint_ref.queue.peek_head();

        proof {
            assert({
                &&& krnl.thr_mp.dom().contains(peer_thread_ptr)
                &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting()
                &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& peer_thread_ptr != current_thread_ptr
                &&& !krnl.thr_mp.spec_index(peer_thread_ptr).wlocked_by(&*lctx)
                &&& krnl.thr_mp.lock_id_by_key(peer_thread_ptr).major == THREAD_BLOCKED_LOCK_MAJOR
            }) by { reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(thread_endpoint_queue_wf); };
        }
        let peer_thread_res = krnl.wlock_thread_unless_killed(peer_thread_ptr, Tracked(&mut *lctx));
        if let (false, _) = peer_thread_res {
            proof {
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
            }
            return ipc_release_current_endpoint_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, RetValueType::ErrorIpcPeerKilled, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm));
        }
        let Tracked(peer_thread_lock_perm) = peer_thread_res.1.unwrap();
        let peer_thread_ref = krnl.thr_mp.borrow(peer_thread_ptr, Tracked(&peer_thread_lock_perm));
        let endpoint_match = match (waiting_state, payload, peer_thread_ref.state, peer_thread_ref.ipc_payload) {
            (
                ThreadState::SENDING,
                IPCPayLoad::Endpoint {
                    endpoint_index: source_endpoint_index,
                },
                ThreadState::RECEIVING,
                IPCPayLoad::Endpoint {
                    endpoint_index: target_endpoint_index,
                },
            ) => Some((current_thread_ptr, peer_thread_ptr, source_endpoint_index, target_endpoint_index)),
            (
                ThreadState::RECEIVING,
                IPCPayLoad::Endpoint {
                    endpoint_index: target_endpoint_index,
                },
                ThreadState::SENDING,
                IPCPayLoad::Endpoint {
                    endpoint_index: source_endpoint_index,
                },
            ) => Some((peer_thread_ptr, current_thread_ptr, source_endpoint_index, target_endpoint_index)),
            _ => None,
        };
        if let Some((source_thread_ptr, receiver_thread_ptr, source_endpoint_index, target_endpoint_index)) = endpoint_match {
            return ipc_rendezvous_endpoint(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_thread_ptr, receiver_thread_ptr, source_endpoint_index, target_endpoint_index, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm));
        }
        let pages_match = match (waiting_state, payload, peer_thread_ref.state, peer_thread_ref.ipc_payload) {
            (
                ThreadState::SENDING,
                IPCPayLoad::Pages { va_range: source_range },
                ThreadState::RECEIVING,
                IPCPayLoad::Pages { va_range: target_range },
            ) if source_range.len == target_range.len =>
                Some((source_range, target_range, current_thread_ptr, peer_thread_ptr)),
            (
                ThreadState::RECEIVING,
                IPCPayLoad::Pages { va_range: target_range },
                ThreadState::SENDING,
                IPCPayLoad::Pages { va_range: source_range },
            ) if source_range.len == target_range.len =>
                Some((source_range, target_range, peer_thread_ptr, current_thread_ptr)),
            _ => None,
        };
        if let Some((source_range, target_range, source_thread, target_thread)) = pages_match {
            return ipc_rendezvous_pages(krnl, &source_range, &target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm));
        }
        let rendezvous_result = match (waiting_state, payload, peer_thread_ref.state, peer_thread_ref.ipc_payload) {
            (
                ThreadState::SENDING, IPCPayLoad::Empty,
                ThreadState::RECEIVING, IPCPayLoad::Empty,
            ) => RetValueType::Success,
            (
                ThreadState::RECEIVING, IPCPayLoad::Empty,
                ThreadState::SENDING, IPCPayLoad::Empty,
            ) => RetValueType::Success,
            _ => RetValueType::ErrorIpcTypeMismatch,
        };

        ipc_schedule_waiting_peer_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, rendezvous_result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm))
    }

} // verus!
